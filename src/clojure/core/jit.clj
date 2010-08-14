(ns clojure.core.jit
  (:use clojure.core)
  (:require [clojure.contrib.trace :as trace])
  (:import (java.lang.reflect Modifier Constructor)
	   (clojure.asm ClassWriter ClassVisitor Opcodes Type)
	   (clojure.asm.commons Method GeneratorAdapter)
	   (clojure.lang IPersistentMap)
	   (clojure.lang.jit StaticFunctionCache))
  )



;;from core.clj
(defn- descriptor [^Class c] (clojure.asm.Type/getDescriptor c))

(declare process-annotation)

(defn- is-annotation? [c]
  (and (class? c)
       (.isAssignableFrom java.lang.annotation.Annotation c)))

(defn- is-runtime-annotation? [^Class c]
  (boolean 
   (and (is-annotation? c)
        (when-let [^java.lang.annotation.Retention r 
                   (.getAnnotation c java.lang.annotation.Retention)] 
          (= (.value r) java.lang.annotation.RetentionPolicy/RUNTIME)))))

(defn- add-annotation [^clojure.asm.AnnotationVisitor av name v]
  (cond
   (vector? v) (let [avec (.visitArray av name)]
                 (doseq [vval v]
                   (add-annotation avec "value" vval))
                 (.visitEnd avec))
   (symbol? v) (let [ev (eval v)]
                 (cond 
                  (instance? java.lang.Enum ev)
                  (.visitEnum av name (descriptor (class ev)) (str ev))
                  (class? ev) (.visit av name (clojure.asm.Type/getType ev))
                  :else (throw (IllegalArgumentException. 
                                (str "Unsupported annotation value: " v " of class " (class ev))))))
   (seq? v) (let [[nested nv] v
                  c (resolve nested)
                  nav (.visitAnnotation av name (descriptor c))]
              (process-annotation nav nv)
              (.visitEnd nav))
   :else (.visit av name v)))

(defn- process-annotation [av v]
  (if (map? v) 
    (doseq [[k v] v]
      (add-annotation av (name k) v))
    (add-annotation av "value" v)))

(defn- add-annotations
  ([visitor m] (add-annotations visitor m nil))
  ([visitor m i]
     (doseq [[k v] m]
       (when (symbol? k)
         (when-let [c (resolve k)]
           (when (is-annotation? c)
                                        ;this is known duck/reflective as no common base of ASM Visitors
             (let [av (if i
                        (.visitParameterAnnotation visitor i (descriptor c) 
                                                   (is-runtime-annotation? c))
                        (.visitAnnotation visitor (descriptor c) 
                                          (is-runtime-annotation? c)))]
               (process-annotation av v)
               (.visitEnd av))))))))



;;from genclass.clj
(defn- non-private-methods [^Class c]
  (loop [mm {}
         considered #{}
         c c]
    (if c
      (let [[mm considered]
            (loop [mm mm
                   considered considered
                   meths (seq (concat
                                (seq (. c (getDeclaredMethods)))
                                (seq (. c (getMethods)))))]
              (if meths
                (let [^java.lang.reflect.Method meth (first meths)
                      mods (. meth (getModifiers))
                      mk (method-sig meth)]
                  (if (or (considered mk)
                          (not (or (Modifier/isPublic mods) (Modifier/isProtected mods)))
                          ;(. Modifier (isPrivate mods))
                          (. Modifier (isStatic mods))
                          (. Modifier (isFinal mods))
                          (= "finalize" (.getName meth)))
                    (recur mm (conj considered mk) (next meths))
                    (recur (assoc mm mk meth) (conj considered mk) (next meths))))
                [mm considered]))]
        (recur mm considered (. c (getSuperclass))))
      mm)))

(defn- ctor-sigs [^Class super]
  (for [^Constructor ctor (. super (getDeclaredConstructors))
        :when (not (. Modifier (isPrivate (. ctor (getModifiers)))))]
    (apply vector (. ctor (getParameterTypes)))))

(defn- escape-class-name [^Class c]
  (.. (.getSimpleName c) 
      (replace "[]" "<>")))

(defn- overload-name [mname pclasses]
  (if (seq pclasses)
    (apply str mname (interleave (repeat \-) 
                                 (map escape-class-name pclasses)))
    (str mname "-void")))

(defn- ^java.lang.reflect.Field find-field [^Class c f]
  (let [start-class c]
    (loop [c c]
      (if (= c Object)
        (throw (new Exception (str "field, " f ", not defined in class, " start-class ", or its ancestors")))
        (let [dflds (.getDeclaredFields c)
              rfld (first (filter #(= f (.getName ^java.lang.reflect.Field %)) dflds))]
          (or rfld (recur (.getSuperclass c))))))))

(def ^{:private true} prim->class
     {'int Integer/TYPE
      'long Long/TYPE
      'float Float/TYPE
      'double Double/TYPE
      'void Void/TYPE
      'short Short/TYPE
      'boolean Boolean/TYPE
      'byte Byte/TYPE
      'char Character/TYPE})

(defn- ^Class the-class [x] 
  (cond 
   (class? x) x
   (contains? prim->class x) (prim->class x)
   :else (let [strx (str x)]
           (clojure.lang.RT/classForName 
            (if (some #{\. \[} strx)
              strx
              (str "java.lang." strx))))))


(defn generate-class-jit [options-map]
  (let [default-options {:state "state"}
	{:keys [name extends implements constructors methods main factory state init exposes 
                exposes-methods post-init]}
	(merge default-options options-map)
	methods-with-func methods
	methods (map #(vec (take 3 %)) methods)
        name-meta (meta name)
        name (str name)
        super (if extends (the-class extends) Object)
        interfaces (map the-class implements)
        supers (cons super interfaces)
        ctor-sig-map (or constructors (zipmap (ctor-sigs super) (ctor-sigs super)))
        cv (new ClassWriter (. ClassWriter COMPUTE_MAXS))
        cname (. name (replace "." "/"))
        pkg-name name
        ctype (. Type (getObjectType cname))
        iname (fn [^Class c] (.. Type (getType c) (getInternalName)))
        totype (fn [^Class c] (. Type (getType c)))
        to-types (fn [cs] (if (pos? (count cs))
                            (into-array (map totype cs))
                            (make-array Type 0)))
        obj-type ^Type (totype Object)
        arg-types (fn [n] (if (pos? n)
                            (into-array (replicate n obj-type))
                            (make-array Type 0)))
        super-type ^Type (totype super)
        init-name "init"
        post-init-name "post-init"
	main-name "main"
        factory-name (str factory)
        state-name (str state)
        class-type  (totype Class)
        rt-type  (totype clojure.lang.RT)
        var-type ^Type (totype clojure.lang.Var)
        ifn-type (totype clojure.lang.IFn)
        iseq-type (totype clojure.lang.ISeq)
        ex-type  (totype java.lang.UnsupportedOperationException)
	;;fixed issue where nil inputs comes up as [nil], which fucks up overrides
        all-sigs (distinct (concat (map #(let[[m p] (key %)] {m (vec p)}) (mapcat non-private-methods supers))
                                   (map (fn [[m p]] {(str m) (vec p)}) methods)))
        sigs-by-name (apply merge-with concat {} all-sigs)
        ;;overloads (into {} (filter (fn [[m s]] (next s)) sigs-by-name))
	overloads {}
        var-fields (concat (when init [init-name]) 
                           (when post-init [post-init-name])
                           (when main [main-name])
                           ;(when exposes-methods (map str (vals exposes-methods)))
                           (distinct (concat (keys sigs-by-name)
                                             (mapcat (fn [[m s]] (map #(overload-name m (map the-class %)) s)) overloads)
                                             (mapcat (comp (partial map str) vals val) exposes))))
	emit-get-var (fn [^GeneratorAdapter gen v]
		       (let [false-label (. gen newLabel)
			     end-label (. gen newLabel)]
			 ;; method is bound?
			 (. gen getStatic ctype (str v "__active") (totype Boolean/TYPE))
			 (. gen ifZCmp (. GeneratorAdapter EQ) false-label)
			 
			 ;; yeup
			 (. gen getStatic ctype (str v "__func") ifn-type)
			 (. gen goTo end-label)
			 
			 (. gen mark false-label)
			 (. gen visitInsn (. Opcodes ACONST_NULL))
			 (. gen mark end-label)))
        emit-unsupported (fn [^GeneratorAdapter gen ^Method m]
                           (. gen (throwException ex-type (str (. m (getName)) " ("
                                                               "/" (.getName m)
                                                               " not defined?)"))))
        emit-forwarding-method
        (fn [name pclasses rclass as-static else-gen]
          (let [mname (str name)
                pmetas (map meta pclasses)
                pclasses (map the-class pclasses)
                rclass (the-class rclass)
                ptypes (to-types pclasses)
                rtype ^Type (totype rclass)
                m (new Method mname rtype ptypes)
                is-overload (seq (overloads mname))
                gen (new GeneratorAdapter (+ (. Opcodes ACC_PUBLIC) (if as-static (. Opcodes ACC_STATIC) 0)) 
                         m nil nil cv)
                found-label (. gen (newLabel))
                else-label (. gen (newLabel))
                end-label (. gen (newLabel))]
            (add-annotations gen (meta name))
            (dotimes [i (count pmetas)]
              (add-annotations gen (nth pmetas i) i))
            (. gen (visitCode))
            (if (> (count pclasses) 18)
              (else-gen gen m)
              (do
                (when is-overload
                  (emit-get-var gen (overload-name mname pclasses))
                  (. gen (dup))
                  (. gen (ifNonNull found-label))
                  (. gen (pop)))
                (emit-get-var gen mname)
                (. gen (dup))
                (. gen (ifNull else-label))
                (when is-overload
                  (. gen (mark found-label)))
                                        ;if found
                (.checkCast gen ifn-type)
                (when-not as-static
                  (. gen (loadThis)))
                                        ;box args
                (dotimes [i (count ptypes)]
                  (. gen (loadArg i))
                  (. clojure.lang.Compiler$HostExpr (emitBoxReturn nil gen (nth pclasses i))))
                                        ;call fn
                (. gen (invokeInterface ifn-type (new Method "invoke" obj-type 
                                                      (to-types (replicate (+ (count ptypes)
                                                                              (if as-static 0 1)) 
                                                                           Object)))))
                                        ;(into-array (cons obj-type 
                                        ;                 (replicate (count ptypes) obj-type))))))
                                        ;unbox return
                (. gen (unbox rtype))
                (when (= (. rtype (getSort)) (. Type VOID))
                  (. gen (pop)))
                (. gen (goTo end-label))
                
                                        ;else call supplied alternative generator
                (. gen (mark else-label))
                (. gen (pop))
                
                (else-gen gen m)
            
                (. gen (mark end-label))))
            (. gen (returnValue))
            (. gen (endMethod))))
        ]
                                        ;start class definition
    (. cv (visit (. Opcodes V1_5) (+ (. Opcodes ACC_PUBLIC) (. Opcodes ACC_SUPER))
                 cname nil (iname super)
                 (when-let [ifc (seq interfaces)]
                   (into-array (map iname ifc)))))

                                        ; class annotations
    (add-annotations cv name-meta)
    
                                        ;static fields for vars
    (doseq [v var-fields]
      ;;flag if method is user defined
      (. cv (visitField (+ Opcodes/ACC_PRIVATE Opcodes/ACC_FINAL Opcodes/ACC_STATIC)
			(str v "__active")
			(. (totype Boolean/TYPE) getDescriptor)
			nil nil))
      ;;function associated with method
      (. cv (visitField (+ Opcodes/ACC_PRIVATE Opcodes/ACC_FINAL Opcodes/ACC_STATIC)
			(str v "__func")
			(. ifn-type getDescriptor)
			nil nil))
     )
                                        ;instance field for state
    (when state
      (. cv (visitField (+ (. Opcodes ACC_PUBLIC) (. Opcodes ACC_FINAL))
                        state-name 
                        (. obj-type getDescriptor)
			nil nil)))
    
                                        ;static init to set up var fields and load init
    (let [gen (new GeneratorAdapter (+ (. Opcodes ACC_PUBLIC) (. Opcodes ACC_STATIC))
		   (. Method getMethod "void <clinit> ()")
		   nil nil cv)
	  staticcache-type (totype StaticFunctionCache)
	  ;;maps method name to definition
	  method-map (reduce (fn [start end]
			       (if (nil? start)
				 {(first end) (second end)}
				 (assoc start (first end) (second end))))
			     nil
			     (map #(vector (first %)
					   (try (nth % 3)
						(catch java.lang.IndexOutOfBoundsException e
						  nil))) methods-with-func))
	  ;; adds constructor, main and post-init if they exist
	  method-map (if init (assoc method-map init-name init) method-map)
	  method-map (if post-init (assoc method-map post-init-name post-init) method-map)
	  method-map (if main (assoc method-map main-name main) method-map)
	  ]
      (. gen (visitCode))
      ;; sets up methods and constructor
      (doseq [v var-fields]
	(let [meth (get method-map v)]
	  (if meth
	    (do
	      (StaticFunctionCache/put v meth)
	      (. gen push v)
	      (. gen (invokeStatic staticcache-type (. Method (getMethod "clojure.lang.IFn get(String)"))))
	      (. gen putStatic ctype (str v "__func") ifn-type)
	      (. gen push true)
	      )
	    (. gen push false))
	  (. gen putStatic ctype (str v "__active") (totype Boolean/TYPE)))
	)
      
      (. gen (returnValue))
      (. gen (endMethod)))
    
                                        ;ctors
    (doseq [[pclasses super-pclasses] ctor-sig-map]
      (let [pclasses (map the-class pclasses)
            super-pclasses (map the-class super-pclasses)
            ptypes (to-types pclasses)
            super-ptypes (to-types super-pclasses)
            m (new Method "<init>" (. Type VOID_TYPE) ptypes)
            super-m (new Method "<init>" (. Type VOID_TYPE) super-ptypes)
            gen (new GeneratorAdapter (. Opcodes ACC_PUBLIC) m nil nil cv)
            no-init-label (. gen newLabel)
            end-label (. gen newLabel)
            no-post-init-label (. gen newLabel)
            end-post-init-label (. gen newLabel)
            nth-method (. Method (getMethod "Object nth(Object,int)"))
            local (. gen newLocal obj-type)]
        (. gen (visitCode))
        
        (if init
          (do
            (emit-get-var gen init-name)
            (. gen dup)
            (. gen ifNull no-init-label)
            (.checkCast gen ifn-type)
                                        ;box init args
            (dotimes [i (count pclasses)]
              (. gen (loadArg i))
              (. clojure.lang.Compiler$HostExpr (emitBoxReturn nil gen (nth pclasses i))))
                                        ;call init fn
            (. gen (invokeInterface ifn-type (new Method "invoke" obj-type 
                                                  (arg-types (count ptypes)))))
                                        ;expecting [[super-ctor-args] state] returned
            (. gen dup)
            (. gen push 0)
            (. gen (invokeStatic rt-type nth-method))
            (. gen storeLocal local)
            
            (. gen (loadThis))
            (. gen dupX1)
            (dotimes [i (count super-pclasses)]
              (. gen loadLocal local)
              (. gen push i)
              (. gen (invokeStatic rt-type nth-method))
              (. clojure.lang.Compiler$HostExpr (emitUnboxArg nil gen (nth super-pclasses i))))
            (. gen (invokeConstructor super-type super-m))
            
            (if state
              (do
                (. gen push 1)
                (. gen (invokeStatic rt-type nth-method))
                (. gen (putField ctype state-name obj-type)))
              (. gen pop))
            
            (. gen goTo end-label)
                                        ;no init found
            (. gen mark no-init-label)
            (. gen (throwException ex-type (str "/" init-name " not defined")))
            (. gen mark end-label))
          (if (= pclasses super-pclasses)
            (do
              (. gen (loadThis))
              (. gen (loadArgs))
              (. gen (invokeConstructor super-type super-m)))
            (throw (new Exception ":init not specified, but ctor and super ctor args differ"))))

        (when post-init
          (emit-get-var gen post-init-name)
          (. gen dup)
          (. gen ifNull no-post-init-label)
          (.checkCast gen ifn-type)
          (. gen (loadThis))
                                       ;box init args
          (dotimes [i (count pclasses)]
            (. gen (loadArg i))
            (. clojure.lang.Compiler$HostExpr (emitBoxReturn nil gen (nth pclasses i))))
                                       ;call init fn
          (. gen (invokeInterface ifn-type (new Method "invoke" obj-type 
                                                (arg-types (inc (count ptypes))))))
          (. gen pop)
          (. gen goTo end-post-init-label)
                                       ;no init found
          (. gen mark no-post-init-label)
          (. gen (throwException ex-type (str "/" post-init-name " not defined")))
          (. gen mark end-post-init-label))

        (. gen (returnValue))
        (. gen (endMethod))
                                        ;factory
        (when factory
          (let [fm (new Method factory-name ctype ptypes)
                gen (new GeneratorAdapter (+ (. Opcodes ACC_PUBLIC) (. Opcodes ACC_STATIC)) 
                         fm nil nil cv)]
            (. gen (visitCode))
            (. gen newInstance ctype)
            (. gen dup)
            (. gen (loadArgs))
            (. gen (invokeConstructor ctype m))            
            (. gen (returnValue))
            (. gen (endMethod))))))
    
                                        ;add methods matching supers', if no fn -> call super
    (let [mm (non-private-methods super)]
      (doseq [^java.lang.reflect.Method meth (vals mm)]
             (emit-forwarding-method (.getName meth) (.getParameterTypes meth) (.getReturnType meth) false
                                     (fn [^GeneratorAdapter gen ^Method m]
                                       (. gen (loadThis))
                                        ;push args
                                       (. gen (loadArgs))
                                        ;call super
                                       (. gen (visitMethodInsn (. Opcodes INVOKESPECIAL) 
                                                               (. super-type (getInternalName))
                                                               (. m (getName))
                                                               (. m (getDescriptor)))))))
                                        ;add methods matching interfaces', if no fn -> throw
      (reduce (fn [mm ^java.lang.reflect.Method meth]
                (if (contains? mm (method-sig meth))
                  mm
                  (do
                    (emit-forwarding-method (.getName meth) (.getParameterTypes meth) (.getReturnType meth) false
                                            emit-unsupported)
                    (assoc mm (method-sig meth) meth))))
              mm (mapcat #(.getMethods ^Class %) interfaces))
					;extra methods
      ;;ignore if already handled by super or interfaces
      ;;pretty inefficient
      (doseq [[mname pclasses rclass :as msig] methods]
	(let [supermeths (set (map #(.getName %)
				   (vals (mapcat non-private-methods supers))))]
	  (if (not (get supermeths mname))
	    (emit-forwarding-method mname pclasses rclass (:static (meta msig))
				    emit-unsupported))))
                                        ;expose specified overridden superclass methods
      (doseq [[local-mname ^java.lang.reflect.Method m]
	      (reduce (fn [ms [[name _ _] m]]
			(if (contains? exposes-methods (symbol name))
			  (conj ms [((symbol name) exposes-methods) m])
			  ms)) [] (seq mm))]
	(let [ptypes (to-types (.getParameterTypes m))
	      rtype (totype (.getReturnType m))
	      exposer-m (new Method (str local-mname) rtype ptypes)
	      target-m (new Method (.getName m) rtype ptypes)
	      gen (new GeneratorAdapter (. Opcodes ACC_PUBLIC) exposer-m nil nil cv)]
	  (. gen (loadThis))
	  (. gen (loadArgs))
	  (. gen (visitMethodInsn (. Opcodes INVOKESPECIAL) 
				  (. super-type (getInternalName))
				  (. target-m (getName))
				  (. target-m (getDescriptor))))
	  (. gen (returnValue))
	  (. gen (endMethod)))))
                                        ;main
    (when main
      (let [m (. Method getMethod "void main (String[])")
            gen (new GeneratorAdapter (+ (. Opcodes ACC_PUBLIC) (. Opcodes ACC_STATIC)) 
                     m nil nil cv)
            no-main-label (. gen newLabel)
            end-label (. gen newLabel)]
        (. gen (visitCode))

        (emit-get-var gen main-name)
        (. gen dup)
        (. gen ifNull no-main-label)
        (.checkCast gen ifn-type)
        (. gen loadArgs)
        (. gen (invokeStatic rt-type (. Method (getMethod "clojure.lang.ISeq seq(Object)"))))
        (. gen (invokeInterface ifn-type (new Method "applyTo" obj-type 
                                              (into-array [iseq-type]))))
        (. gen pop)
        (. gen goTo end-label)
                                        ;no main found
        (. gen mark no-main-label)
        (. gen (throwException ex-type (str "/" main-name " not defined")))
        (. gen mark end-label)
        (. gen (returnValue))
        (. gen (endMethod))))
                                        ;field exposers
    (doseq [[f {getter :get setter :set}] exposes]
      (let [fld (find-field super (str f))
            ftype (totype (.getType fld))
            static? (Modifier/isStatic (.getModifiers fld))
            acc (+ Opcodes/ACC_PUBLIC (if static? Opcodes/ACC_STATIC 0))]
        (when getter
          (let [m (new Method (str getter) ftype (to-types []))
                gen (new GeneratorAdapter acc m nil nil cv)]
            (. gen (visitCode))
            (if static?
              (. gen getStatic ctype (str f) ftype)
              (do
                (. gen loadThis)
                (. gen getField ctype (str f) ftype)))
            (. gen (returnValue))
            (. gen (endMethod))))
        (when setter
          (let [m (new Method (str setter) Type/VOID_TYPE (into-array [ftype]))
                gen (new GeneratorAdapter acc m nil nil cv)]
            (. gen (visitCode))
            (if static?
              (do
                (. gen loadArgs)
                (. gen putStatic ctype (str f) ftype))
              (do
                (. gen loadThis)
                (. gen loadArgs)
                (. gen putField ctype (str f) ftype)))
            (. gen (returnValue))
            (. gen (endMethod))))))
                                        ;finish class def
    (. cv (visitEnd))
    [cname (. cv (toByteArray))]))


(defn gen-class-jit
  [& options]
  (let [options-map (into {} (map vec (partition 2 options)))
	[cname bytecode] (generate-class-jit options-map)]
    (.defineClass (deref clojure.lang.Compiler/LOADER)
		  (:name options-map)
		  bytecode nil)))

(defn write-class-jit
  [& options]
  (let [options-map (into {} (map vec (partition 2 options)))
	[cname bytecode] (generate-class-jit (dissoc options-map :location))]
    (clojure.lang.jit.ClassWriter/writeClassFile cname bytecode (:location options-map))))