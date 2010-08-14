
package clojure.lang.jit;

import clojure.lang.IFn;
import java.util.concurrent.ConcurrentHashMap;

public class StaticFunctionCache{
    private static ConcurrentHashMap<String,IFn> cache = new ConcurrentHashMap<String,IFn>();
    
    public static void put(String key, IFn fun){
	cache.put(key,fun);
    }
    
    public static IFn get(String key){
	return cache.get(key);
    }
   
    public static void clear(){
	cache.clear();
    }
}
