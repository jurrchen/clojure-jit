package clojure.lang.jit;

import java.io.*;
import java.util.*;

public class ClassWriter {

    static public void writeClassFile(String internalName, byte[] bytecode, String genPath)
	throws Exception{
	String[] dirs = internalName.split("/");
	String p = genPath;
	for(int i = 0; i < dirs.length - 1; i++)
	    {
		p += File.separator + dirs[i];
		(new File(p)).mkdir();
	    }
	String path = genPath + File.separator + internalName + ".class";
	File cf = new File(path);
	cf.createNewFile();
	FileOutputStream cfs = new FileOutputStream(cf);
	try
	    {
		cfs.write(bytecode);
		cfs.flush();
		cfs.getFD().sync();
	    }
	finally
	    {
		cfs.close();
	    }
    }
    
    

}