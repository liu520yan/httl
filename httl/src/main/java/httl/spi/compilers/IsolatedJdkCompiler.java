/*
 * Copyright 2011-2013 HTTL Team.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package httl.spi.compilers;

import httl.util.ClassUtils;
import httl.util.StringUtils;
import httl.util.UnsafeByteArrayInputStream;
import httl.util.UnsafeByteArrayOutputStream;

import java.io.File;
import java.io.FileOutputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.lang.ref.Reference;
import java.lang.ref.ReferenceQueue;
import java.lang.ref.WeakReference;
import java.net.URI;
import java.net.URL;
import java.net.URLClassLoader;
import java.text.ParseException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentMap;
import java.util.concurrent.atomic.AtomicLong;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import javax.tools.Diagnostic;
import javax.tools.DiagnosticListener;
import javax.tools.FileObject;
import javax.tools.ForwardingJavaFileManager;
import javax.tools.JavaCompiler;
import javax.tools.JavaFileManager;
import javax.tools.JavaFileObject;
import javax.tools.JavaFileObject.Kind;
import javax.tools.SimpleJavaFileObject;
import javax.tools.StandardJavaFileManager;
import javax.tools.StandardLocation;
import javax.tools.ToolProvider;

/**
 * IsolatedJdkCompiler. (SPI, Singleton, ThreadSafe)
 *
 * <p>A memory-safe drop-in replacement for {@link JdkCompiler}. It keeps the
 * exact same compilation semantics (real {@code javax.tools} javac, same
 * generated source, same bytecode) and is selected the same way:</p>
 *
 * <pre>
 * httl.properties: compiler=httl.spi.compilers.IsolatedJdkCompiler
 * </pre>
 *
 * <p><b>The leak in {@link JdkCompiler}.</b> {@code JdkCompiler} keeps a
 * {@code DiagnosticCollector}, a {@code StandardJavaFileManager}, one shared
 * {@code ClassLoaderImpl} (holding every generated class of every template) and
 * one {@code JavaFileManagerImpl} (holding every generated source) as
 * <i>instance</i> fields, and {@link AbstractCompiler} keeps a
 * <i>static, unbounded</i> {@code CLASS_CACHE} of every class it ever produced.
 * Every {@code getTask(...).call()} builds a fresh javac {@code Context} with a
 * full symbol table (Symtab) of the JDK class library. Because the objects
 * above stay strongly reachable for the JVM lifetime, they pin those Contexts:
 * each distinct template permanently retains roughly 6-11 MiB of heap plus its
 * generated source and bytecode, and neither the classes nor their class loader
 * can ever be unloaded.</p>
 *
 * <p><b>What this implementation does instead</b></p>
 * <ol>
 * <li><b>Per-compile javac state.</b> The file manager, the diagnostic sink, the
 * task and the defining class loader are created inside the compile call and
 * released in {@code finally}. Nothing javac-related is ever stored in a field,
 * so the Context/Symtab of a finished compile has no GC root and dies
 * immediately.</li>
 * <li><b>Diagnostics are formatted, not retained.</b> A listener appends plain
 * strings instead of collecting {@code Diagnostic} objects, so no
 * {@code JCTree}/{@code Symbol} (and therefore no Symtab) is reachable through
 * error reporting.</li>
 * <li><b>No static class cache.</b> {@link AbstractCompiler#compile(String)} is
 * overridden to bypass the shared, unbounded {@code CLASS_CACHE}. Only a
 * <i>weak</i> cache keyed by class name is kept, so a template class is reused
 * while someone still references it (the engine's template cache) and becomes
 * collectable - together with its class loader, bytecode and generated source -
 * as soon as nobody does. Class unloading then actually happens.</li>
 * <li><b>Generated source is dropped after compilation.</b> The class loader
 * keeps only the bytecode it needs to lazily define nested classes.</li>
 * <li><b>Annotation processing is off by default</b> ({@code -proc:none}),
 * which skips the per-compile {@code ServiceLoader} scan of the classpath for
 * {@code Processor} implementations. Template code never carries annotations, so
 * this changes no output; set {@code disable.annotation.processing=false} to
 * restore javac's default.</li>
 * </ol>
 *
 * <p><b>Trade-off.</b> A shared symbol table would make repeated compiles
 * faster, but it is exactly what makes them leak. Here the symbol table is built
 * per compile (~100-200 ms per template on a warm JVM); steady-state rendering is
 * unaffected because HTTL compiles once per template and caches the result. If
 * compilation throughput matters more than footprint, use
 * {@code httl.spi.compilers.JavassistCompiler} instead.</p>
 *
 * <p>No existing HTTL class is modified or replaced by this implementation.</p>
 *
 * @author HTTL Team
 */
public class IsolatedJdkCompiler extends AbstractCompiler {

	private static final Pattern PACKAGE_PATTERN = Pattern.compile("package\\s+([_a-zA-Z][_a-zA-Z0-9\\.]*);");

	private static final Pattern CLASS_PATTERN = Pattern.compile("class\\s+([_a-zA-Z][_a-zA-Z0-9]*)\\s+");

	/** Upper bound for the formatted diagnostics kept in memory on a failed compile. */
	private static final int MAX_DIAGNOSTIC_CHARS = 64 * 1024;

	/** Stateless javac entry point (a JavacTool singleton), safe to share. */
	private final JavaCompiler tool;

	private final ClassLoader parentLoader;

	/** Classpath entries resolved once at startup - plain Files, no javac state. */
	private final Set<File> classPath = new LinkedHashSet<File>();

	private final List<String> options = new ArrayList<String>();

	private final List<String> lintOptions = new ArrayList<String>();

	/** className -> weakly referenced generated class. Never retains a class. */
	private final ConcurrentMap<String, CachedClass> classCache = new ConcurrentHashMap<String, CachedClass>();

	/** Fed by the weak references so cleared entries can be dropped in O(1). */
	private final ReferenceQueue<Class<?>> staleClasses = new ReferenceQueue<Class<?>>();

	private final AtomicLong compileCount = new AtomicLong();

	private boolean lintUnchecked;

	private boolean disableAnnotationProcessing = true;

	public IsolatedJdkCompiler() {
		tool = ToolProvider.getSystemJavaCompiler();
		if (tool == null) {
			throw new IllegalStateException("Can not get system java compiler. Please run with JDK (NOT JRE),"
					+ " or configure the httl.properties: compiler=httl.spi.compilers.JavassistCompiler,"
					+ " and add javassist.jar.");
		}
		ClassLoader contextLoader = Thread.currentThread().getContextClassLoader();
		try {
			contextLoader.loadClass(IsolatedJdkCompiler.class.getName());
		} catch (ClassNotFoundException e) {
			// The context loader can not see httl.jar, fall back to ours.
			contextLoader = IsolatedJdkCompiler.class.getClassLoader();
		}
		parentLoader = contextLoader;
		ClassLoader loader = contextLoader;
		while (loader instanceof URLClassLoader
				&& !loader.getClass().getName().equals("sun.misc.Launcher$AppClassLoader")) {
			URLClassLoader urlClassLoader = (URLClassLoader) loader;
			for (URL url : urlClassLoader.getURLs()) {
				try {
					classPath.add(new File(url.toURI()));
				} catch (Exception e) {
					classPath.add(new File(url.getFile()));
				}
			}
			loader = loader.getParent();
		}
		// Resolve javac's effective classpath once through a throw-away file manager.
		StandardJavaFileManager probe = tool.getStandardFileManager(null, null, null);
		try {
			Iterable<? extends File> list = probe.getLocation(StandardLocation.CLASS_PATH);
			if (list != null) {
				for (File file : list) {
					classPath.add(file);
				}
			}
		} catch (Exception e) {
			// No classpath reported; javac will use its own default.
		} finally {
			closeQuietly(probe);
		}
		lintOptions.add("-Xlint:unchecked");
	}

	public void init() {
		if (logger != null && logger.isDebugEnabled()) {
			StringBuilder buf = new StringBuilder(320);
			buf.append("JDK Compiler classpath locations:\n");
			buf.append("================\n");
			for (File file : classPath) {
				buf.append(file.getAbsolutePath());
				buf.append("\n");
			}
			buf.append("================\n");
			logger.debug(buf.toString());
		}
	}

	/**
	 * httl.properties: java.specification.version=1.7
	 */
	public void setCompileVersion(String version) {
		if (StringUtils.isNotEmpty(version)
				&& !version.equals(ClassUtils.getJavaVersion())) {
			options.add("-target");
			options.add(version);
			lintOptions.add("-target");
			lintOptions.add(version);
		}
	}

	/**
	 * httl.properties: lint.unchecked=true
	 */
	public void setLintUnchecked(boolean lintUnchecked) {
		this.lintUnchecked = lintUnchecked;
	}

	/**
	 * httl.properties: disable.annotation.processing=false
	 *
	 * <p>Defaults to {@code true} (javac runs with {@code -proc:none}). Template
	 * sources never declare annotations, so no processor can contribute; skipping
	 * them avoids the per-compile classpath scan for processor implementations.</p>
	 */
	public void setDisableAnnotationProcessing(boolean disableAnnotationProcessing) {
		this.disableAnnotationProcessing = disableAnnotationProcessing;
	}

	/** Number of successful compiles performed by this compiler instance. */
	public long getCompileCount() {
		return compileCount.get();
	}

	/** Number of generated classes currently alive in the weak cache. */
	public int getCachedClassCount() {
		purgeStaleClasses();
		return classCache.size();
	}

	/**
	 * Compiles the given java source, reusing a still-live class with the same
	 * name if one exists.
	 *
	 * <p>Overrides {@link AbstractCompiler#compile(String)} on purpose: the base
	 * implementation stores every compiled class in a static, unbounded
	 * {@code CLASS_CACHE}, which keeps generated classes, their class loaders,
	 * their bytecode and their generated source reachable forever. This variant
	 * caches weakly instead, so classes are reused while referenced and collected
	 * once they are not.</p>
	 */
	@Override
	public Class<?> compile(String code) throws ParseException {
		String className = null;
		try {
			code = code.trim();
			if (!code.endsWith("}")) {
				throw new ParseException("The java code not endsWith \"}\"", code.length() - 1);
			}
			Matcher matcher = PACKAGE_PATTERN.matcher(code);
			String pkg = matcher.find() ? matcher.group(1) : "";
			matcher = CLASS_PATTERN.matcher(code);
			if (!matcher.find()) {
				throw new ParseException("No such class name in java code.", 0);
			}
			String classSimpleName = matcher.group(1);
			className = StringUtils.isNotEmpty(pkg) ? pkg + "." + classSimpleName : classSimpleName;

			Class<?> cls = lookupCachedClass(className);
			if (cls == null) {
				cls = doCompile(className, code);
				purgeStaleClasses();
				classCache.put(className, new CachedClass(className, cls));
			}
			dumpJavaCode(className, code);
			return cls;
		} catch (Throwable t) {
			if (logger != null && logger.isErrorEnabled()) {
				logger.error("Failed to compile class, cause: " + t.getMessage() + ", class: " + className + ", code: \n================================\n" + code + "\n================================\n", t);
			}
			if (t instanceof ParseException) {
				throw (ParseException) t;
			}
			throw new ParseException("Failed to compile class, cause: " + t.getMessage() + ", class: " + className + ", stack: " + ClassUtils.toString(t), 0);
		}
	}

	@Override
	protected Class<?> doCompile(String name, String sourceCode) throws Exception {
		try {
			return doCompile(name, sourceCode, options);
		} catch (Exception e) {
			if (lintUnchecked && e.getMessage() != null
					&& e.getMessage().contains("-Xlint:unchecked")) {
				return doCompile(name, sourceCode, lintOptions);
			}
			throw e;
		}
	}

	/**
	 * Everything javac-related in this method is method-local: a fresh diagnostic
	 * sink, file manager and class loader per compile, all released in the finally
	 * block. Once the call returns, the javac Context of this compile has no
	 * strong root and the symbol table it built becomes garbage.
	 */
	private Class<?> doCompile(String name, String sourceCode, List<String> baseOptions) throws Exception {
		Diagnostics diagnostics = new Diagnostics();
		StandardJavaFileManager standard = null;
		JavaFileManagerImpl javaFileManager = null;
		try {
			standard = tool.getStandardFileManager(diagnostics, null, null);
			if (!classPath.isEmpty()) {
				standard.setLocation(StandardLocation.CLASS_PATH, classPath);
			}
			ClassLoaderImpl classLoader = new ClassLoaderImpl(parentLoader);
			javaFileManager = new JavaFileManagerImpl(standard, classLoader);
			int i = name.lastIndexOf('.');
			String packageName = i < 0 ? "" : name.substring(0, i);
			String className = i < 0 ? name : name.substring(i + 1);
			JavaFileObjectImpl source = new JavaFileObjectImpl(className, sourceCode);
			javaFileManager.putFileForInput(StandardLocation.SOURCE_PATH, packageName,
					className + ClassUtils.JAVA_EXTENSION, source);
			Boolean result = tool.getTask(null, javaFileManager, diagnostics, optionsOf(baseOptions),
					null, Arrays.asList(new JavaFileObject[] { source })).call();
			if (result == null || !result.booleanValue()) {
				throw new IllegalStateException("Compilation failed. class: " + name
						+ ", diagnostics: " + diagnostics);
			}
			Class<?> cls = classLoader.loadClass(name);
			// The generated java source is only needed while javac runs.
			source.releaseSource();
			compileCount.incrementAndGet();
			return cls;
		} finally {
			if (javaFileManager != null) {
				javaFileManager.clear();
			}
			if (standard != null) {
				closeQuietly(standard);
			}
		}
	}

	private List<String> optionsOf(List<String> baseOptions) {
		if (!disableAnnotationProcessing) {
			return baseOptions;
		}
		for (String option : baseOptions) {
			if (option != null && option.startsWith("-proc")) {
				return baseOptions;
			}
		}
		List<String> result = new ArrayList<String>(baseOptions.size() + 1);
		result.addAll(baseOptions);
		result.add("-proc:none");
		return result;
	}

	private Class<?> lookupCachedClass(String className) {
		Class<?> cls = null;
		CachedClass cached = classCache.get(className);
		if (cached != null) {
			cls = cached.get();
			if (cls == null) {
				classCache.remove(className, cached);
			}
		}
		return cls;
	}

	private void purgeStaleClasses() {
		Reference<? extends Class<?>> stale;
		while ((stale = staleClasses.poll()) != null) {
			CachedClass cached = (CachedClass) stale;
			classCache.remove(cached.className, cached);
		}
	}

	private void dumpJavaCode(String className, String sourceCode) throws IOException {
		if (codeDirectory == null) {
			return;
		}
		int i = className.lastIndexOf('.');
		String packageName = i < 0 ? "" : className.substring(0, i);
		String simpleName = i < 0 ? className : className.substring(i + 1);
		File javaDir = new File(codeDirectory, packageName.replace('.', '/'));
		if (javaDir.exists() || javaDir.mkdirs()) {
			FileWriter writer = new FileWriter(new File(javaDir, simpleName + ClassUtils.JAVA_EXTENSION));
			try {
				writer.write(sourceCode);
				writer.flush();
			} finally {
				writer.close();
			}
		}
	}

	private static void closeQuietly(JavaFileManager manager) {
		try {
			manager.close();
		} catch (Throwable ignored) {
		}
	}

	/** Weak reference that remembers its cache key so the entry can be dropped. */
	private final class CachedClass extends WeakReference<Class<?>> {

		private final String className;

		CachedClass(String className, Class<?> referent) {
			super(referent, staleClasses);
			this.className = className;
		}
	}

	/** Collects formatted diagnostics only - never retains javac objects. */
	private static final class Diagnostics implements DiagnosticListener<JavaFileObject> {

		private final StringBuilder buffer = new StringBuilder(256);

		public void report(Diagnostic<? extends JavaFileObject> diagnostic) {
			if (diagnostic == null || buffer.length() >= MAX_DIAGNOSTIC_CHARS) {
				return;
			}
			buffer.append("\n\t");
			buffer.append(diagnostic.getKind());
			if (diagnostic.getSource() != null && diagnostic.getLineNumber() > 0) {
				buffer.append(' ');
				buffer.append(diagnostic.getSource().getName());
				buffer.append(':');
				buffer.append(diagnostic.getLineNumber());
			}
			buffer.append(' ');
			buffer.append(diagnostic.getMessage(Locale.getDefault()));
		}

		@Override
		public String toString() {
			return buffer.toString();
		}
	}

	/**
	 * Per-compile class loader. It holds only the bytecode of one compiled
	 * template (a couple of small byte arrays) and no javac object, so it becomes
	 * collectable - together with every class it defined - as soon as the last
	 * reference to those classes is dropped.
	 */
	private final class ClassLoaderImpl extends ClassLoader {

		private final Map<String, JavaFileObject> classes = new ConcurrentHashMap<String, JavaFileObject>();

		ClassLoaderImpl(ClassLoader parent) {
			super(parent);
		}

		Collection<JavaFileObject> files() {
			return Collections.unmodifiableCollection(classes.values());
		}

		@Override
		protected Class<?> findClass(String qualifiedClassName) throws ClassNotFoundException {
			JavaFileObject file = classes.get(qualifiedClassName);
			if (file == null) {
				throw new ClassNotFoundException(qualifiedClassName);
			}
			byte[] bytes = ((JavaFileObjectImpl) file).getByteCode();
			if (compileDirectory != null) {
				// saveBytecode() writes straight into the package directory and does
				// not create it; upstream JdkCompiler fails on a fresh directory here.
				int dot = qualifiedClassName.lastIndexOf('.');
				if (dot > 0) {
					File dir = new File(compileDirectory,
							qualifiedClassName.substring(0, dot).replace('.', '/'));
					if (!dir.exists()) {
						dir.mkdirs();
					}
				}
			}
			try {
				saveBytecode(qualifiedClassName, bytes);
			} catch (IOException e) {
				throw new IllegalStateException(e.getMessage(), e);
			}
			return defineClass(qualifiedClassName, bytes, 0, bytes.length);
		}

		void add(String qualifiedClassName, JavaFileObject javaFile) {
			classes.put(qualifiedClassName, javaFile);
		}

		@Override
		public InputStream getResourceAsStream(String name) {
			if (name.endsWith(ClassUtils.CLASS_EXTENSION)) {
				String qualifiedClassName = name.substring(0,
						name.length() - ClassUtils.CLASS_EXTENSION.length()).replace('/', '.');
				JavaFileObject file = classes.get(qualifiedClassName);
				if (file != null) {
					return new UnsafeByteArrayInputStream(((JavaFileObjectImpl) file).getByteCode());
				}
			}
			return super.getResourceAsStream(name);
		}
	}

	private static final class JavaFileObjectImpl extends SimpleJavaFileObject {

		private UnsafeByteArrayOutputStream bytecode;

		private CharSequence source;

		JavaFileObjectImpl(String baseName, CharSequence source) {
			super(ClassUtils.toURI(baseName + ClassUtils.JAVA_EXTENSION), Kind.SOURCE);
			this.source = source;
		}

		JavaFileObjectImpl(String name, Kind kind) {
			super(ClassUtils.toURI(name), kind);
			this.source = null;
		}

		/** Drops the generated java source once javac no longer needs it. */
		void releaseSource() {
			source = null;
		}

		@Override
		public CharSequence getCharContent(boolean ignoreEncodingErrors) {
			if (source == null) {
				throw new UnsupportedOperationException("source == null");
			}
			return source;
		}

		@Override
		public InputStream openInputStream() {
			return new UnsafeByteArrayInputStream(getByteCode());
		}

		@Override
		public OutputStream openOutputStream() {
			return bytecode = new UnsafeByteArrayOutputStream();
		}

		byte[] getByteCode() {
			return bytecode.toByteArray();
		}
	}

	/** Per-compile file manager; its maps die with the compile. */
	private static final class JavaFileManagerImpl extends ForwardingJavaFileManager<JavaFileManager> {

		private final ClassLoaderImpl classLoader;

		private final Map<URI, JavaFileObject> fileObjects = new ConcurrentHashMap<URI, JavaFileObject>();

		JavaFileManagerImpl(JavaFileManager fileManager, ClassLoaderImpl classLoader) {
			super(fileManager);
			this.classLoader = classLoader;
		}

		@Override
		public FileObject getFileForInput(Location location, String packageName, String relativeName)
				throws IOException {
			FileObject o = fileObjects.get(uri(location, packageName, relativeName));
			if (o != null) {
				return o;
			}
			return super.getFileForInput(location, packageName, relativeName);
		}

		void putFileForInput(StandardLocation location, String packageName,
				String relativeName, JavaFileObject file) {
			fileObjects.put(uri(location, packageName, relativeName), file);
		}

		private URI uri(Location location, String packageName, String relativeName) {
			return ClassUtils.toURI(location.getName() + '/' + packageName + '/' + relativeName);
		}

		@Override
		public JavaFileObject getJavaFileForOutput(Location location, String qualifiedName,
				Kind kind, FileObject outputFile) throws IOException {
			JavaFileObject file = new JavaFileObjectImpl(qualifiedName, kind);
			classLoader.add(qualifiedName, file);
			return file;
		}

		@Override
		public ClassLoader getClassLoader(JavaFileManager.Location location) {
			return classLoader;
		}

		@Override
		public String inferBinaryName(Location loc, JavaFileObject file) {
			if (file instanceof JavaFileObjectImpl) {
				return file.getName();
			}
			return super.inferBinaryName(loc, file);
		}

		@Override
		public Iterable<JavaFileObject> list(Location location, String packageName,
				Set<Kind> kinds, boolean recurse) throws IOException {
			ArrayList<JavaFileObject> files = new ArrayList<JavaFileObject>();
			if (location == StandardLocation.CLASS_PATH
					&& kinds.contains(JavaFileObject.Kind.CLASS)) {
				for (JavaFileObject file : fileObjects.values()) {
					if (file.getKind() == Kind.CLASS && file.getName().startsWith(packageName)) {
						files.add(file);
					}
				}
				files.addAll(classLoader.files());
			} else if (location == StandardLocation.SOURCE_PATH
					&& kinds.contains(JavaFileObject.Kind.SOURCE)) {
				for (JavaFileObject file : fileObjects.values()) {
					if (file.getKind() == Kind.SOURCE && file.getName().startsWith(packageName)) {
						files.add(file);
					}
				}
			}
			Iterable<JavaFileObject> result = super.list(location, packageName, kinds, recurse);
			for (JavaFileObject file : result) {
				files.add(file);
			}
			return files;
		}

		void clear() {
			// NOTE: the class loader's bytecode map is NOT cleared here - the
			// compiled class may still need it to lazily define nested classes.
			// It holds nothing but small byte arrays and dies with the class.
			fileObjects.clear();
		}
	}
}
