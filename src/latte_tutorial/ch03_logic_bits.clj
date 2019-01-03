
;;{
;; # Chapter 3: Bits of logic with natural deduction
;; 
;; Now that we have some knowledge of the rules of the game,
;; we can start playing with the LaTTe proof assistant, and
;; do some actual logic.
;;}

(ns latte-tutorial.ch03-logic-bits
  ;; In this namespace we will start to use LaTTe "for real",
  ;; so we introduce the main forms from the core namespace
  (:require [latte.core :as latte :refer [definition defthm try-example proof try-proof
                                          assume have qed]]
            ;; we will also exploit the basic proposition from the prelude
            [latte-prelude.prop :as p :refer [and or not]])

  ;; also, these belong to logic
  (:refer-clojure :exclude [and or not]))

;;{
;;*Natural deduction* is a way of presenting and formalizing logics
;; based on:
;; - introduction rules, or how to construct logical statements
;; - elimination rules, or how to take them apart.
;; 
;; We already encountered introduction and elimination rules that
;; are in a way primitive in type theory and LaTTe:
;; - the introduction of a universal quantifier - or an implication
;; as a special case - using a lambda abstraction
;; - the elimination of a universal quantifier or an implication
;; using function application.
;; 
;; In this chapter of the tutorial, we will discuss the introduction
;; and elimination rules for other important logical constructs.
;; The implementation of this basic rules can be found in the
;; `prop` namespace `latte-prelude` library.
;; 
;; cf. https://github.com/latte-central/latte-prelude/blob/master/src/latte_prelude/prop.clj
;;}

;;{
;; ## Conjunction
;; 
;; Conjunction, or logical `and` is where most presentations of natural
;; deduction start, so let's follow the tradition.
;; 
;; The definition is provided in the prelude:
;; 
;; ```clojure
;; (definition and
;;    "logical conjunction."
;;    [[A :type] [B :type]]
;;    (forall [C :type]
;;            (==> (==> A B C)
;;                 C)))
;; ```
;; 
;; This is called the "second order characterization
;; of conjunction". While this can be interpreted as a
;; generic proof scheme based on the knowledge of two
;; propositions `A` and `B`, in natural deduction we
;; prefer to decompose the scheme in two parts: the
;; introduction of a conjunction, or its eliminations.
;; Informally, the introduction rule for conjunction
;; is often presented as follows:
;; 
;; ```
;;    A     B
;; =============
;;  (and A B)
;; ```
;; 
;; The horizontal "double bar" means implication, thus this reads as follows:
;; 
;; > if both proposition `A` and `B` hold, then we can deduce
;; > that the conjunction `(and A B)` also holds.
;; 
;; This is often introduced in an axiomatic way, i.e. without any justification,
;; but in type theory the definition above can be used to prove this as a theorem.
;; To introduce a theorem, we use the `defthm' form, and this is how we
;; can formalize the introduction rule in LaTTe:
;;}

(defthm my-and-intro
  "Introduction rule for conjunction."
  [[A :type] [B :type]]
  (==> A B
       (and A B)))
;; => [:declared :theorem my-and-intro]

;;{
;; As LaTTe explains us, the theorem is now *declared*, however
;; we cannot use it because we first have to prove that the
;; theorem indeed *is* a theorem.
;; 
;; Note that the internal representation of the theorem is not
;; hidden from the user, and we can find a few interesting informations
;; by inspecting it.
;;}

my-and-intro
;; => #latte_kernel.defenv.Theorem{
;;       :name my-and-intro,
;;       :params [[A ✳] [B ✳]],
;;       :arity 2,
;;       :type (Π [⇧ A]
;;                (Π [⇧ B]
;;                   (#'latte-prelude.prop/and A B))),
;;       :proof nil}

;;{
;; In the Clojure terminology this is a *record* with a few self-explicit
;; fields. We can see that the `:proof` field is `nil`.
;; To understand that "everything is under control", let's try to use
;; the theorem somehow.
;;}

(try-example [[A :type]]
    (==> A A (and A A))
  (qed (my-and-intro A A)))
;; = > [:failed "Proof failed: Qed step failed: cannot infer term type."
;;              {:cause {:msg "Theorem has no proof.",
;;                       :thm-name my-and-intro},
;;               :meta {:line 3, :column 3}}]

