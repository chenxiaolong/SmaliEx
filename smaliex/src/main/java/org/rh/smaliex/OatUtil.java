/*
 * [The "BSD licence"]
 * Copyright (c) 2014 Riddle Hsu
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. The name of the author may not be used to endorse or promote products
 *    derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
 * OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
 * IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
 * NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
 * THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

package org.rh.smaliex;

import org.jf.baksmali.baksmali;
import org.jf.baksmali.baksmaliOptions;
import org.jf.dexlib2.Opcodes;
import org.jf.dexlib2.analysis.AnalysisException;
import org.jf.dexlib2.analysis.ClassPath;
import org.jf.dexlib2.analysis.MethodAnalyzer;
import org.jf.dexlib2.dexbacked.DexBackedDexFile;
import org.jf.dexlib2.iface.ClassDef;
import org.jf.dexlib2.iface.DexFile;
import org.jf.dexlib2.iface.Method;
import org.jf.dexlib2.iface.MethodImplementation;
import org.jf.dexlib2.iface.instruction.Instruction;
import org.jf.dexlib2.immutable.ImmutableDexFile;
import org.jf.dexlib2.rewriter.DexRewriter;
import org.jf.dexlib2.rewriter.MethodImplementationRewriter;
import org.jf.dexlib2.rewriter.MethodRewriter;
import org.jf.dexlib2.rewriter.Rewriter;
import org.jf.dexlib2.rewriter.RewriterModule;
import org.jf.dexlib2.rewriter.Rewriters;
import org.jf.dexlib2.writer.io.DexDataStore;
import org.jf.dexlib2.writer.pool.DexPool;
import org.rh.smaliex.reader.DataReader;
import org.rh.smaliex.reader.Elf;
import org.rh.smaliex.reader.Oat;

import javax.annotation.Nonnull;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.nio.ByteBuffer;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.Set;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;
import java.util.jar.JarOutputStream;
import java.util.zip.ZipEntry;

@SuppressWarnings("unused")
public class OatUtil {
    /**
     * Extract smali from odex or oat file.
     *
     * If the input file has multiple embedded dex files, the smali files will be placed into subdirectories within the
     * output directory. Otherwise, the smali files are placed directly into the output directory.
     *
     * If there are multiple dex files in the input file, the subdirectories will be named as follows:
     * 1. If the input file is an oat file, then the subdirectory name is based on the dex_file_location_data_ field
     * 2. If the input file is not an oat file, then the subdirectory name is "classes", "classes2", etc.
     *
     * @param inputFile Input odex or oat file
     * @param outputDir Output directory
     * @throws IOException
     */
    public static boolean smaliRaw(File inputFile, File outputDir) throws IOException {
        baksmaliOptions options = new baksmaliOptions();
        Opcodes opc = new Opcodes(org.jf.dexlib2.Opcode.LOLLIPOP);
        options.apiLevel = opc.apiLevel;
        options.allowOdex = true;
        options.jobs = 4;

        java.util.List<DexBackedDexFile> dexFiles = new ArrayList<>();
        java.util.List<File> outSubDirs = new ArrayList<>();
        if (Elf.isElf(inputFile)) {
            final byte[] buf = new byte[8192];
            try (Elf e = new Elf(inputFile)) {
                Oat oat = getOat(e);
                for (int i = 0; i < oat.mDexFiles.length; i++) {
                    Oat.DexFile df = oat.mDexFiles[i];
                    dexFiles.add(readDex(df, df.mHeader.file_size_, opc, buf));
                    String opath = new String(oat.mOatDexFiles[i].dex_file_location_data_);
                    opath = MiscUtil.getFilenamePrefix(getOuputNameForSubDex(opath));
                    outSubDirs.add(new File(outputDir, opath));
                }
            }
        } else {
            dexFiles = DexUtil.loadMultiDex(inputFile, opc);
            String subDir = "classes";
            for (int i = 0; i < dexFiles.size(); i++) {
                outSubDirs.add(new File(outputDir, subDir));
                subDir = "classes" + (i + 1);
            }
        }
        if (outSubDirs.size() == 1) {
            outSubDirs.set(0, outputDir);
        }

        for (int i = 0; i < dexFiles.size(); i++) {
            options.outputDirectory = outSubDirs.get(i).getPath();
            if (!baksmali.disassembleDexFile(dexFiles.get(i), options)) {
                return false;
            }
        }

        return true;
    }

    /**
     * Extract odex files from boot.oat and convert them to dex.
     *
     * This outputs both odex and dex files, hence the two output directory parameters.
     *
     * @param bootOat boot.oat file
     * @param odexDir Output directory for odex files
     * @param dexDir Output directory for dex files
     * @throws IOException
     */
    public static void bootOat2Dex(File bootOat, File odexDir, File dexDir) throws IOException {
        extractOdexFromOat(bootOat, odexDir);
        extractDexFromBootOat(bootOat, odexDir, dexDir);
    }

    /**
     * Extract dex files from an oat file.
     *
     * @param oatFile Oat file
     * @param bootClassPath Boot class path (path to framework odex files)
     * @param outputDir Output directory for dex files
     * @throws IOException
     */
    public static File[] oat2dex(File oatFile, File bootClassPath, File outputDir) throws IOException {
        try (Elf e = new Elf(oatFile)) {
            Oat oat = getOat(e);
            return convertToDex(oat, outputDir, bootClassPath, true);
        }
    }

    /**
     * Extract Oat file from ELF file
     *
     * @param e ELF file
     * @return Oat file
     * @throws IOException If the ELF file contains no Oat file
     */
    public static Oat getOat(Elf e) throws IOException {
        DataReader r = e.getReader();
        Elf.Elf_Shdr sec = e.getSectionByName(Oat.SECTION_RODATA);
        if (sec != null) {
            r.seek(sec.getOffset());
            return new Oat(r, true);
        }
        throw new IOException("oat not found");
    }

    /**
     * Get list of jar names from boot.oat.
     *
     * @param bootOat boot.oat file
     * @return List of jar names with code inside the boot.oat file
     * @throws IOException
     */
    public static ArrayList<String> getBootJarNames(File bootOat) throws IOException {
        ArrayList<String> names = new ArrayList<>();
        try (Elf e = new Elf(bootOat)) {
            Oat oat = getOat(e);
            for (Oat.OatDexFile df : oat.mOatDexFiles) {
                String s = new String(df.dex_file_location_data_);
                if (s.contains(":")) {
                    continue;
                }
                names.add(s.substring(s.lastIndexOf('/') + 1));
            }
        }
        return names;
    }

    /**
     * Get desired filename for the output dex.
     *
     * If the jar path has a colon (ie. in the form "/path/to/something.jar:subdex.dex"), then the output filename is
     * "something-subdex.dex". If the jar path does not have a colon (ie. in the form "/path/to/something.jar"), then
     * the output filename is "something.dex".
     *
     * @param jarPathInOat JAR path as specified in the oat file
     * @return Desired filename
     */
    public static String getOuputNameForSubDex(String jarPathInOat) {
        String path = jarPathInOat;
        String subdex = null;
        int pos = jarPathInOat.indexOf(':');
        if (pos > 0) {
            path = jarPathInOat.substring(0, pos);
            subdex = jarPathInOat.substring(pos + 1);
        }

        String prefix;
        int slashPos = path.lastIndexOf('/');
        if (slashPos >= 0) {
            prefix = MiscUtil.getFilenamePrefix(path.substring(slashPos + 1));
        } else {
            prefix = MiscUtil.getFilenamePrefix(path);
        }

        StringBuilder sb = new StringBuilder();
        sb.append(prefix);
        if (subdex != null) {
            sb.append('-');
            sb.append(subdex);
        } else {
            sb.append(".dex");
        }

        return sb.toString();
    }

    /**
     * Extract odex files from oat file.
     *
     * NOTE: The odex files created in the output directory will have the ".dex" extension.
     *
     * @param oatFile Oat file
     * @param outputDir Output directory
     * @throws IOException
     */
    public static void extractOdexFromOat(File oatFile, File outputDir) throws IOException {
        try (Elf e = new Elf(oatFile)) {
            Oat oat = getOat(e);
            for (int i = 0; i < oat.mDexFiles.length; i++) {
                Oat.OatDexFile odf = oat.mOatDexFiles[i];
                Oat.DexFile df = oat.mDexFiles[i];
                String opath = new String(odf.dex_file_location_data_);
                opath = getOuputNameForSubDex(opath);
                File out = MiscUtil.changeExt(new File(outputDir, opath), "dex");
                df.saveTo(out);
            }
        }
    }

    /**
     * Extract dex files from a boot.oat file.
     *
     * @param oatFile Oat file
     * @param bootClassPath Boot class path (path to framework odex files)
     * @param outputDir Output directory for dex files
     * @throws IOException
     */
    public static File[] extractDexFromBootOat(File oatFile, File bootClassPath, File outputDir) throws IOException {
        try (Elf e = new Elf(oatFile)) {
            Oat oat = getOat(e);
            return convertToDex(oat, outputDir, bootClassPath, false);
        }
    }

    /**
     * Get DexBackedDexFile object from a dex file.
     *
     * @param od DexFile from an Oat file
     * @param dexSize Size of dex file
     * @param opcodes Opcodes for the API level
     * @param buf Buffer area (may be null to use internal buffer)
     * @return DexBackedDexFile object
     * @throws IOException
     */
    static DexBackedDexFile readDex(Oat.DexFile od, int dexSize, Opcodes opcodes, byte[] buf) throws IOException {
        if (buf == null) {
            buf = new byte[8192];
        }
        ByteBuffer dexBytes = ByteBuffer.allocateDirect(dexSize);
        od.mReader.seek(od.mDexPosition);
        int remain = dexSize;
        int read = buf.length > dexSize ? dexSize : buf.length;
        int readSize;
        while ((readSize = od.mReader.readRaw(buf, 0, read)) != -1 && remain > 0) {
            dexBytes.put(buf, 0, readSize);
            remain -= readSize;
            if (remain < buf.length) {
                read = remain;
            }
        }
        int length = dexBytes.position();
        dexBytes.flip();
        byte[] data = new byte[length];
        dexBytes.get(data);
        return new DexBackedDexFile(opcodes, data);
    }

    /**
     * Get list of DexFile objects from an Oat file.
     *
     * @param oat Oat file
     * @param opcodes Opcodes for the API level (if null, guessed from oat file)
     * @return List of DexFile objects
     * @throws IOException
     */
    public static DexFile[] getOdexFromOat(Oat oat, Opcodes opcodes) throws IOException {
        final int BSIZE = 8192;
        final byte[] buf = new byte[BSIZE];
        if (opcodes == null) {
            opcodes = new Opcodes(oat.guessApiLevel());
        }
        DexFile[] dexFiles = new DexFile[oat.mOatDexFiles.length];
        for (int i = 0; i < oat.mOatDexFiles.length; i++) {
            Oat.DexFile dex = oat.mDexFiles[i];
            final int dexSize = dex.mHeader.file_size_;
            dexFiles[i] = readDex(dex, dexSize, opcodes, buf);
        }
        return dexFiles;
    }

    /**
     * Convert oat file to dex files.
     *
     * @param oat Oat file
     * @param outputDir Output directory for dex files
     * @param bootClassPath Boot class path (path to framework odex files)
     * @param addSelfToBcp Whether to add dex files to boot class path field
     * @throws IOException
     */
    private static File[] convertToDex(Oat oat, File outputDir, File bootClassPath,
                                       boolean addSelfToBcp) throws IOException {
        final Opcodes opcodes = new Opcodes(oat.guessApiLevel());

        if (bootClassPath == null || !bootClassPath.exists()) {
            throw new IOException("Invalid bootclasspath: " + bootClassPath);
        }
        final OatDexRewriterModule odr = new OatDexRewriterModule(bootClassPath.getPath(), opcodes);
        final DexRewriter deOpt = odr.getRewriter();

        DexFile[] dexFiles = getOdexFromOat(oat, opcodes);
        if (addSelfToBcp) {
            for (DexFile d : dexFiles) {
                odr.mBootClassPath.addDex(d);
            }
        }

        ArrayList<File> outputFiles = new ArrayList<>();

        for (int i = 0; i < oat.mOatDexFiles.length; i++) {
            Oat.OatDexFile odf = oat.mOatDexFiles[i];
            String dexLoc = new String(odf.dex_file_location_data_);
            String opath = getOuputNameForSubDex(dexLoc);
            if ("base.apk".equals(opath)) {
                opath = MiscUtil.getFilenamePrefix(oat.mSrcFile.getName());
            }
            File outputFile = MiscUtil.changeExt(new File(outputDir, opath), "dex");
            DexFile d = deOpt.rewriteDexFile(dexFiles[i]);
            if (!OatDexRewriter.isValid(d)) {
                throw new IOException("Failed to rewrite dex file: " + outputFile);
            }

            if (outputFile.exists()) {
                outputFile.delete();
            }
            DexPool.writeTo(outputFile.getAbsolutePath(), d);

            outputFiles.add(outputFile);
        }

        return outputFiles.toArray(new File[outputFiles.size()]);
    }

    public static void convertToDexJar(Oat oat, File outputFolder,
            String bootClassPath, String noClassJarFolder, boolean isBoot) throws IOException {
        final Opcodes opcodes = new Opcodes(oat.guessApiLevel());
        final OatDexRewriterModule odr = new OatDexRewriterModule(bootClassPath, opcodes);
        HashMap<String, ArrayList<Oat.DexFile>> dexFileGroup = new HashMap<>();
        for (int i = 0; i < oat.mOatDexFiles.length; i++) {
            Oat.OatDexFile odf = oat.mOatDexFiles[i];
            String opath = new String(odf.dex_file_location_data_);
            int spos = opath.indexOf(':');
            if (spos > 0) {
                // .../framework.jar:classes2.dex
                opath = opath.substring(0, spos);
            }
            opath = opath.substring(opath.lastIndexOf('/') + 1);
            ArrayList<Oat.DexFile> dfiles = dexFileGroup.get(opath);
            if (dfiles == null) {
                dfiles = new ArrayList<>();
                dexFileGroup.put(opath, dfiles);
            }
            dfiles.add(oat.mDexFiles[i]);
            if (!isBoot) {
                Oat.DexFile dex = oat.mDexFiles[i];
                odr.mBootClassPath.addDex(
                        readDex(dex, dex.mHeader.file_size_, opcodes, null));
            }
        }

        final int BSIZE = 8192;
        final byte[] buf = new byte[BSIZE];
        final DexRewriter deOpt = odr.getRewriter();

        for (String jarName : dexFileGroup.keySet()) {
            File outputFile = MiscUtil.changeExt(new File(outputFolder, jarName), "jar");
            String classesIdx = "";
            int i = 1;
            int readSize;
            try (JarOutputStream jos = new JarOutputStream(new FileOutputStream(outputFile))) {
                for (Oat.DexFile dex : dexFileGroup.get(jarName)) {
                    jos.putNextEntry(new ZipEntry("classes" + classesIdx + ".dex"));
                    final int dexSize = dex.mHeader.file_size_;
                    ByteBuffer dexBytes = ByteBuffer.allocateDirect(dexSize);
                    dex.mReader.seek(dex.mDexPosition);
                    int remain = dexSize;
                    int read = BSIZE > dexSize ? dexSize : BSIZE;
                    while ((readSize = dex.mReader.readRaw(buf, 0, read)) != -1 && remain > 0) {
                        dexBytes.put(buf, 0, readSize);
                        remain -= readSize;
                        if (remain < BSIZE) {
                            read = remain;
                        }
                    }

                    int length = dexBytes.position();
                    dexBytes.flip();
                    byte[] data = new byte[length];
                    dexBytes.get(data);
                    DexFile d = new DexBackedDexFile(opcodes, data);
                    d = deOpt.rewriteDexFile(d);
                    if (!OatDexRewriter.isValid(d)) {
                        throw new IOException("Failed to rewrite dex file: " + outputFile);
                    }

                    MemoryDataStore m = new MemoryDataStore(dexSize + 512);
                    DexPool.writeTo(m, d);

                    jos.write(m.mBuffer.mData, 0, m.mBuffer.mMaxDataPosition);
                    classesIdx = String.valueOf(++i);
                    jos.closeEntry();
                }

                // Copy files from original jar
                try (JarFile jarFile = new JarFile(new File(noClassJarFolder, jarName))) {
                    final Enumeration<JarEntry> entries = jarFile.entries();
                    while (entries.hasMoreElements()) {
                        final JarEntry e = entries.nextElement();
                        String name = e.getName();
                        if (name.startsWith("classes") && name.endsWith(".dex")) {
                            continue;
                        }
                        jos.putNextEntry(new ZipEntry(name));
                        try (InputStream is = jarFile.getInputStream(e)) {
                            int bytesRead;
                            while ((bytesRead = is.read(buf)) != -1) {
                                jos.write(buf, 0, bytesRead);
                            }
                        }
                        jos.closeEntry();
                    }
                }
            }
        }
    }

    /**
     * Resizeable binary data container
     */
    static class ByteData {
        private int mMaxDataPosition;
        private int mPosition;
        private byte[] mData;

        public ByteData(int initSize) {
            mData = new byte[initSize];
        }

        private void ensureCapacity(int writingPos) {
            int oldSize = mData.length;
            if (writingPos >= oldSize) {
                int newSize = (oldSize * 3) / 2 + 1;
                if (newSize <= writingPos) {
                    newSize = writingPos + 1;
                }
                mData = Arrays.copyOf(mData, newSize);
            }
            if (writingPos > mMaxDataPosition) {
                mMaxDataPosition = writingPos;
            }
        }

        public void put(byte c) {
            ensureCapacity(mPosition);
            mData[mPosition] = c;
        }

        public void put(byte[] bytes, int off, int len) {
            ensureCapacity(mPosition + len);
            System.arraycopy(bytes, off, mData, mPosition, len);
        }

        public byte get() {
            return mData[mPosition];
        }

        public void get(byte[] bytes, int off, int len) {
            System.arraycopy(mData, mPosition, bytes, off, len);
        }

        public boolean isPositionHasData() {
            return mPosition <= mMaxDataPosition;
        }

        public int remaining() {
            return mMaxDataPosition - mPosition;
        }

        public void position(int p) {
            mPosition = p;
        }
    }

    /**
     * Memory-backed storage for a dex file.
     */
    static class MemoryDataStore implements DexDataStore {
        final ByteData mBuffer;

        public MemoryDataStore(int size) {
            mBuffer = new ByteData(size);
        }

        @Override
        @Nonnull
        public OutputStream outputAt(final int offset) {
            return new OutputStream() {
                private int mPos = offset;

                @Override
                public void write(int b) throws IOException {
                    mBuffer.position(mPos);
                    mPos++;
                    mBuffer.put((byte) b);
                }

                @Override
                public void write(byte[] bytes, int off, int len) throws IOException {
                    mBuffer.position(mPos);
                    mPos += len;
                    mBuffer.put(bytes, off, len);
                }
            };
        }

        @Override
        @Nonnull
        public InputStream readAt(final int offset) {
            mBuffer.position(offset);
            return new InputStream() {
                private int mPos = offset;

                @Override
                public int read() throws IOException {
                    mBuffer.position(mPos);
                    if (!mBuffer.isPositionHasData()) {
                        return -1;
                    }
                    mPos++;
                    return mBuffer.get() & 0xff;
                }

                @Override
                public int read(byte[] bytes, int off, int len) throws IOException {
                    mBuffer.position(mPos);
                    if (mBuffer.remaining() == 0 || !mBuffer.isPositionHasData()) {
                        return -1;
                    }
                    len = Math.min(len, mBuffer.remaining());
                    mPos += len;
                    mBuffer.get(bytes, off, len);
                    return len;
                }
            };
        }

        @Override
        public void close() throws IOException {
        }
    }

    public static class OatDexRewriter extends DexRewriter {
        public OatDexRewriter(OatDexRewriterModule module) {
            super(module);
        }

        @Override
        @Nonnull
        public DexFile rewriteDexFile(@Nonnull DexFile dexFile) {
            try {
                return ImmutableDexFile.of(super.rewriteDexFile(dexFile));
            } catch (Exception e) {
                return new FailedDexFile();
            }
        }

        public static boolean isValid(DexFile dexFile) {
            return !(dexFile instanceof FailedDexFile);
        }

        static final class FailedDexFile implements DexFile {
            @Override
            @Nonnull
            public Set<? extends ClassDef> getClasses() {
                return new java.util.HashSet<>(0);
            }
        }
    }

    /**
     * Convert optimized dex to a normal dex.
     */
    public static class OatDexRewriterModule extends RewriterModule {
        private final ClassPath mBootClassPath;
        private Method mCurrentMethod;
        
        public OatDexRewriterModule(String bootClassPath, Opcodes opcodes, String ext) {
            mBootClassPath = MiscUtil.getClassPath(bootClassPath, opcodes, ext);
        }

        public OatDexRewriterModule(String bootClassPath, Opcodes opcodes) {
            this(bootClassPath, opcodes, ".dex");
        }

        public DexRewriter getRewriter() {
            return new OatDexRewriter(this);
        }

        @Override
        @Nonnull
        public Rewriter<MethodImplementation> getMethodImplementationRewriter(@Nonnull Rewriters rewriters) {
            return new MethodImplementationRewriter(rewriters) {
                @Override
                @Nonnull
                public MethodImplementation rewrite(@Nonnull MethodImplementation methodImplementation) {
                    return new MethodImplementationRewriter.RewrittenMethodImplementation(methodImplementation) {
                        @Override
                        @Nonnull
                        public Iterable<? extends Instruction> getInstructions() {
                            MethodAnalyzer ma = new MethodAnalyzer(mBootClassPath, mCurrentMethod, null);
                            if (!ma.analysisInfo.isEmpty()) {
                                StringBuilder sb = new StringBuilder(256);
                                sb.append("Analysis info of ").append(mCurrentMethod.getDefiningClass())
                                        .append(" : ").append(mCurrentMethod.getName()).append(":\n");
                                for (String info : ma.analysisInfo) {
                                    sb.append(info).append("\n");
                                }
                                LLog.i(sb.toString());
                            }
                            AnalysisException ae = ma.getAnalysisException();
                            if (ae != null) {
                                LLog.e("Analysis error in class=" + mCurrentMethod.getDefiningClass()
                                    + " method=" + mCurrentMethod.getName() + "\n" + ae.getContext());
                                LLog.ex(ae);
                            }
                            return ma.getInstructions();
                        }
                    };
                }
            };
        }

        @Override
        @Nonnull
        public Rewriter<Method> getMethodRewriter(@Nonnull Rewriters rewriters) {
            return new MethodRewriter(rewriters) {
                @Override
                @Nonnull
                public Method rewrite(@Nonnull Method method) {
                    return new MethodRewriter.RewrittenMethod(method) {
                        @Override
                        public MethodImplementation getImplementation() {
                            mCurrentMethod = method;
                            return super.getImplementation();
                        }
                    };
                }
            };
        }
    }
}
