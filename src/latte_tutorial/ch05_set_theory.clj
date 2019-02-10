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

(ns latte-tutorial.ch05-set-theory
  (:require [latte.core :as latte :refer [definition defthm deflemma
                                          lambda forall
                                          example try-example
                                          proof try-proof
                                          assume have qed]]
            [latte-prelude.prop :as p :refer [and and* or or* not <=>]]
            [clojure.repl :refer [doc]]
            
            ;; set theory requirements
            [latte-sets.core :as set :refer [set elem set-of subset seteq]]
            ;; boolean algebra of sets
            [latte-sets.algebra :as setops :refer [union inter diff complement]]
            )

  
  ;; also, these belong to logic or formal arithmetic
  (:refer-clojure :exclude [and or not set complement]))

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
  "We assume that x is in the emptyset ..."
  (assume [x T
           H ((my-emptyset T) x)]
    "... and it is absurd by definition of the emptyset"
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
           H (elem x (my-emptyset T))]
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
;; It is important to remember that `set-of` constructions are still `lambda`'s.
;;}

;;{
;; ## Subsets and set-equality
;; 
;; There is an important relationship between implication and being *a subset of* another set.
;; This is clearly apparent in the following definition:
;;
;; ```clojure
;; (definition subset-def
;;   "The subset relation for type `T`.
;; The expression `(subset-def T s1 s2)` means that
;;  the set `s1` is a subset of `s2`, i.e. `s1`⊆`s2`."
;;   [[T :type] [s1 (set T)] [s2 (set T)]]
;;   (forall [x T]
;;     (==> (elem x s1)
;;          (elem x s2))))
;; ```
;; In the library a shortcut `(subset s1 s2)` is also defined.
;; The definition says that a set (`s2`) is a subset of another
;; set (`s1`), both defined over a type `T`, if for any element `x` of the
;; considered type `T`,  `x`∈`s1` implies `x`∈`s2`. If we rewrite slightly
;; our two sets as follows:
;;
;; ```clojure
;; s1 ≡ { x:T | P1(x) }  and s1 ≡ { y:T | P2(x) }  
;; ```
;;
;; The definition simply says that `P1` should imply `P2`.
;; You probably know that the emptyset is vacuously a subset
;; of any other set. Let's prove this as a Lemma.
;;}

(deflemma empty-subset
  [[T :type] [s (set T)]]
  (subset (my-emptyset T) s))

(proof 'empty-subset
  (assume [x T
           Hempty (elem x (my-emptyset T))]
    "Of course we proceed by contradiction,
because we know that there is no such element x"
    (have <a> (not (elem x (my-emptyset T)))
          :by ((my-emptyset-empty T) x))
    "Hence we obtain absurdity"
    (have <b> p/absurd :by (<a> Hempty))
    "We can have anything we want here!"
    (have <c> (elem x s) :by (<b> (elem x s))))
  (qed <c>))
;; => [:qed empty-subset]

;;{
;; **Exercise**: prove the following theorems:
;; 
;; - `subset-refl`: the subset relation is *reflexive*: `(subset s s)` for any set `s`
;; - `subset-trans`: it is *transitive*: if `(subset s1 s2)` and `(subset s2 s3)` then `(subset s1 s3)`
;;}

;;{
;; We can define a useful notion of equality based on the subset relation.
;; It is technically-speaking rather an equivalence relation, so let's
;; call it *"set equivalence"*.
;; 
;; ```clojure
;; (definition seteq-def
;;   "Set equivalence.
;;   This is a natural notion of \"equal sets\"
;;   based on the subset relation."
;;   [[T :type] [s1 (set T)] [s2 (set T)]]
;;   (and (subset s1 s2)
;;        (subset s2 s1)))
;; ```
;; And you may rewrite `(seteq-def T s1 s2)` as `(seteq s1 s2)`.
;; 
;; It is rather a trivial fact that this equivalence is symmetric.
;;}

(defthm seteq-sym
  [[T :type] [s1 (set T)] [s2 (set T)]]
  (==> (seteq s1 s2)
       (seteq s2 s1)))

;;{
;; The proof is a one-liner.
;;}

(proof 'seteq-sym
  (qed (lambda [H (seteq s1 s2)] (p/and-sym H))))
;; => [:qed seteq-sym]

;;{
;; Well, maybe it's a little bit too crytpic, let's decompose
;; the proof.
;;}

(proof 'seteq-sym
  (assume [H (seteq s1 s2)]
    "We can decompose the conjunction."
    (have <a> (subset s1 s2) :by (p/and-elim-left H))
    (have <b> (subset s2 s1) :by (p/and-elim-right H))
    "Now let's rebuild a conjunction by reversing
the two previous steps"
    (have <c> (and (subset s2 s1)
                   (subset s1 s2))
          :by (p/and-intro <b> <a>))
    "This is set equivalence!"
    (have <d> (seteq s2 s1) :by <c>))
  (qed <d>))
  ;;=>  [:qed seteq-sym]

;;{
;; The following exercise (if solved) shows that `seteq` is a
;; proper *equivalence relation* (together with symmetry).
;; 
;; **Exercise**: prove the following theorems:
;; 
;; - `seteq-refl`: reflexivity of set equality
;; - `seteq-trans`: transitivity of set equality`
;; 
;; We will go back to this notion of equality/equivalence,
;; and compare it with other "competing" notions.
;;}

;;{
;; ## Boolean algebra of sets
;;
;; One major contribution of *George Boole* was its discovery (and study) of the
;; relation between algebra (at that time, mostly developed for numbers) and
;; logic. There is for example a simple correspondance between calculating
;; in base 2 arithmetics, and propositional logic. `True` is 1, `False` is 0,
;; `and` is `times`, `or` is `plus`, etc.
;;
;; Important algebraic properties follow the correspondance: `False` is a
;; unit of disjunction and "absorbing" for conjunection, `True` is simply
;; the converse.
;;
;; A similar boolean algebra of sets can be constructed. More precisely, for each type `T` a
;; specific boolean algebra can be constructed, based on the following ingredients:
;; 
;; - the emptyset corresponds to `False`
;; - the fullset corresponds to `True`
;; - the "disjunction" ("plus") is *set union*
;; - the "conjunction" ("times") is *set intersection*
;; - the "negation" is *set complement*
;;
;; Let's define (or see the definition of) all these ingredients.
;; We already have the emptyset, so let's define the fullset.
;;}

(definition my-fullset
  [[T :type]]
  (set-of [x T] (not p/absurd)))
;; => [:defined :term my-fullset]

;;{
;; Everything is "not absurd", hence this should be a good candidate for
;; being the set of "all possible `T`'s". Let's check this.
;;}

(deflemma my-fullset-elem
  [[T :type]]
  (forall [x T] (elem x (my-fullset T))))
;; => [:declared :lemma my-fullset-elem]

(proof 'my-fullset-elem
  (assume [x T]
    "I would like to have `(==> p/absurd p/absurd)`."
    (assume [H p/absurd]
      (have <a> p/absurd :by H))
    "And here it is!"
    (have <b> (==> p/absurd p/absurd) :by <a>)
    "This is a synonym for the following:"
    (have <c> (not p/absurd) :by <b>))
  "And we're done."
  (qed <c>))

;;{
;; This can of course be rewritten as a one-liner.
;;}

(proof 'my-fullset-elem
  (qed (lambda [x T] 
         (lambda [H p/absurd] H))))
;; => [:qed my-fullset-elem]

;;{
;; ### Union
;;
;; The union of two sets is a concept similar to logical disjunction.
;; Indeed, an element is member of the union of `s1` and `s2` if
;; it is a member of `s1` *or* a member of `s2` (or both).
;;
;; This is trivial to translate this in LaTTe:
;;}

(definition my-union
  [[T :type] [s1 (set T)] [s2 (set T)]]
  (set-of [x T] (or (elem x s1)
                    (elem x s2))))
;; => [:defined :term my-union]

;;{
;; Let's prove, as an example, that the emptyset set
;; is a left unit of union (like `False` is a left unit
;; of disjunction).
;;}

(defthm my-union-left-unit
  [[T :type] [s (set T)]]
  (seteq (my-union T (my-emptyset T) s)
         s))
;; => [:declared :theorem my-union-left-unit]

;;{
;; Proving `(seteq s1 s2)` consists in building a conjunction of two "sub-proofs":
;;
;; - an "if" proof of `(subset s1 s2)`
;; - a "only-if" proof of `(subset s2 s1)`
;;
;; We will state and prove each one of these as an auxiliary lemma. 
;;}

(deflemma my-union-left-unit-if
  [[T :type] [s (set T)]]
  (subset (my-union T (my-emptyset T) s)
          s))
;; => [:declared :lemma my-union-left-unit-if]

(proof 'my-union-left-unit-if
  (assume [x T
           Hx (elem x (my-union T (my-emptyset T) s))]
    "We simplify a little bit the assumption."
    (have <Hx>  (or (elem x (my-emptyset T))
                   (elem x s)) :by Hx)
    "We have now to prove that x ∈ s.
Union is disjunction hence we consider two cases."
    (assume [H1 (elem x (my-emptyset T))]
      (have <a1> p/absurd :by ((my-emptyset-empty T) x H1))
      (have <a> (elem x s) :by (<a1> (elem x s))))
    "Second case is trivial."
    (assume [H2 (elem x s)]      
      (have <b> (elem x s) :by H2))
    "Or elimination can be performed now."
    (have <c> _ :by (p/or-elim Hx (elem x s) <a> <b>)))
  (qed <c>))
;; => [:qed my-union-left-unit-if]

;;{
;; And now for the opposite "only-if" direction.
;;}

(deflemma my-union-left-unit-only-if
  [[T :type] [s (set T)]]
  (subset s
          (my-union T (my-emptyset T) s)))
;; => [:declared :lemma my-union-left-unit-only-if]

;;{
;; The proof is much simpler for this case.
;;}

(proof 'my-union-left-unit-only-if
  (assume [x T
           Hx (elem x s)]
    (have <a> (or (elem x (my-emptyset T)) (elem x s))
          :by (p/or-intro-right (elem x (my-emptyset T)) Hx)))
  (qed <a>))
;; => [:qed my-union-left-unit-only-if]

;;{
;; And now we can prove the "equivalence" theorem.
;;}

(proof 'my-union-left-unit
  (qed (p/and-intro (my-union-left-unit-if T s)
                    (my-union-left-unit-only-if T s))))
;; => [:qed my-union-left-unit]

;;{
;; **Exercise**: prove the "right unit" theorem for union.
;;}

(defthm my-union-right-unit
  [[T :type] [s (set T)]]
  (seteq (my-union T s (my-emptyset T))
         s))

;;{
;; **Exercise**: prove that the fullset is "lef-absorbing", i.e:
;; 
;; ```clojure
;; (seteq (my-union T (my-fullset T) s)
;;        (my-fullset T))
;; ```
;; (of course it is also "right-absorbing")
;;}

;;{
;; ### Intersection
;; 
;; *Set intersection* is almost copy-and-paste for `union`, replacing `or` by `and`.
;;}

(definition my-inter
  [[T :type] [s1 (set T)] [s2 (set T)]]
  (set-of [x T] (and (elem x s1)
                     (elem x s2))))
;; => [:defined :term my-inter]

;;{
;; ### Complement
;; 
;; Logical negation is connected to the notion of a *set complement*. 
;;}

(definition my-complement
  [[T :type] [s (set T)]]
  (set-of [x T] (not (elem x s))))
;; => [:defined :term my-complement]

;;{
;; I really like this definition, because it gives a very concise and concrete
;; argument in favor of a "typed" reconstruction of set theory.
;; In classical axiomatic set theory, the complement has a rather, let's say
;; unwieldy definition. Let's e.g. what Wikipedia is saying:
;; 
;; > If A is a set, then the absolute complement of A (or simply the complement of A) is the set of elements not in A. In other words, if U is the universe that contains all the elements under study, and there is no need to mention it because it is obvious and unique, then the absolute complement of A is the relative complement of A in U.
;; 
;; [from Wikipedia (retrieved Feb. 10, 2019)](https://en.wikipedia.org/wiki/Complement_(set_theory))
;; 
;; In "everyday mathematics", this notion of an *universe* is not really problematic (because "it is obvious and unique"),
;; but in formal mathematics it is a rather unsettling notion. In type theory, things are much more natural,
;; the universe is simply the type `T` in `(set T)`. The complement is all those `T` that are not in the set `s`, a very
;; natural definition is you ask me.
;; 
;;}

