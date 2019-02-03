;;{
;; # A bag full of sets
;; 
;; For both trained mathematicians and laypersons, set theory is at the root
;; of mathematics. And indeed, most mathematical objects can be founded
;; upon the axiomatic set theory, namely ZF or ZFC. But sets are also
;; used almost everywhere in maths and, well, everywhere. Even children
;; practice sets quite early: think "the set of available ice cream
;; flavors"!
;; 
;; Type theory (TT) is, in a way, an alternative construction of mathematical
;; objects, and while TT can be justified in terms of "standard" set theory
;; (through the so-called BHK-interpretation), it clearly has a foundational role.
;; Hence if the "foundational" sets and "layperson" sets are in general not
;; distinguished, type theory makes such a distinction in that types replace
;; sets in the foundational role. But what about the "layperson" sets?
;; Can't children select their prefered ice cream flavour in type theory? 
;;}

(ns latte-tutorial.ch05-set-thoery
  (:require [latte.core :as latte :refer [definition defthm deflemma
                                          example try-example
                                          proof try-proof
                                          assume have qed]]
            [latte-prelude.prop :as p :refer [and and* or or* not <=>]]
            [clojure.repl :refer [doc]]
            
            ;; set theory requirements
            [latte-sets.core :as set :refer [set elem]]
            )

  
  ;; also, these belong to logic or formal arithmetic
  (:refer-clojure :exclude [and or not set]))

;;{
;; As a first approach, it seems natural to think of types as sets.
;; In typed programming saying that "a variable is of type
;; `int`" is the same as saying that it can store a value in the
;; set of (machine-representable) integers. In the library `latte-integers`
;; there is such a type, and indeed all the (infinite) integer numbers
;; inhabit this type. But suppose now we would like to talk about the
;; set of positive integer. In mathematics we would use the following notation:
;; 
;; $$\{n \in \mathbb{Z} \mid n \geq 0\}$$
;; 
;; In set theory we would also probably say that this is the set $\mathbb{N}$
;; (although sometimes the zero is omitted, which it clearly shouldn't!).
;; It is possible to define a type `nat` for the natural number (e.g. as a variant
;; of the way `int` is constructed), however it would not be a subset of `int`.
;; 
;; What we are looking for is a way to constrains a type, i.e. something of the form:
;; 
;; $$\{x : T \mid P(x) \}$$
;; 
;; The set of all $x$'s of type $T$ such that $P(x)$ is true, for some predicate $P$. 
;; Some proof assistants introduce the notion of a "sigma-type" ($\Sigma$-type)
;; to enable the construction of such a "subset of a type". But in fact, we have already
;; all the necessary tools in LaTTe to make such a construction.
;; 
;; If we consider that `P` is of type `(==> T :type)` then
;; we can build our set as follows:
;; 
;; ```clojure
;; (lambda [x T] (P x))
;; ```
;; 
;; This function represents exactly what we need: all the `x`'s of type `T` such that `(P x)` holds.
;; We will now see how much (if not all?) of the "layperson" set theory
;; can be rebuilt based on this simple idea. 
;;
;; As a first example, we can define the "emptyset" of type `T`.
;;}

(definition my-emptyset [[T :type]]
  (lambda [x T] p/absurd))
;; => [:defined :term my-emptyset]

;;{
;; We know from the previous chapter that there cannot be any value of type
;; `absurd`, thus there is no `x` to satisfy `my-emptyset`, and thus `my-emptyset` is empty!
;; Remark that unlike in classical set theory, there is no universal notion of an emptyset in
;; type theory. Each type `T` possesses its own emptyset: this is *typed* set theory!
;;}

;;{
;; ## Set membership
;;
;; The definition of a set (precisely `latte-sets.core/set`) in LaTTe is as follows:
;;
;; ```clojure
;; (definition set
;;   "The type of sets whose elements are of type `T`."
;;   [[T :type]]
;;   (==> T :type))
;; ```
;;
;; So it is a function from a type `T` to `:type`, the type of propositions.
;; Put in other terms, it is a proposition conditioned by a type.
;; We can check that our definition of an emptyset satisfies this definition.
;;}

(latte/type-of [T :type]
               (my-emptyset T))
;; => (==> T *)

;;{
;; Set theory is all about *membership*: making a clear separation about who is
;; in the type, and who isn't? In LaTTe set membership is very simple: it is (again!) function application.
;;
;; > For an element `e` and a set `E`, `e`∈`E` iff `(E e)` !
;;
;; As an example, we can show that an emptyset cannot contain any element.
;;}

(defthm my-emptyset-empty [[T :type]]
  (forall [x T] (not ((my-emptyset T) x))))
;; => [:declared :theorem my-emptyset-empty]

;;{
;; The proof is by contradiction, and it is very simple.
;;}

(proof 'my-emptyset-empty
  (assume [x T
           ;; We assume that x is in the emptyset
           H ((my-emptyset T) x)]
    ;; and it is absurd by definition of the emptyset
    (have <a> p/absurd :by H))
  (qed <a>))
;; => [:qed my-emptyset-empty]

;;{
;; The only drawback of the "lambda-as-set" approach is that the
;; way things are written do not look like the traditional set notations.
;; The `latte-sets` library introduce the notation `(elem e E)` which
;; looks more like the traditional notation `e`∈`E` than `(E e)`.
;; Thus, we can rewrite our theorem and proof as follows:
;;}

(defthm my-emptyset-empty-v2 [[T :type]]
  (forall [x T] (not (elem x (my-emptyset T)))))
;; => [:declared :theorem my-emptyset-empty-v2]

(proof 'my-emptyset-empty-v2
  (assume [x T
           ;; We assume that x is in the emptyset
           H (elem x (my-emptyset T))]
    ;; and it is absurd by definition of the emptyset
    (have <a> p/absurd :by H))
  (qed <a>))
;; => [:qed my-emptyset-empty-v2]

;;{
;; This is probably more readable for the mathematics (and lisp) practionner.
;; Note, also, that there is aspecific notation for the definition
;; of a set by comprehension:
;;
;; ```clojure
;; { x : T | P(x) }  is  (set-of [x T] (P x))
;; ... which is (lambda [x T] (P x))
;; ```
;; Note that it is important to remember that `set-of` constructions are still `lambda`'s.
;;}

;;{
;; ## Subsets and set-equality
;;
;; TODO
;;}
