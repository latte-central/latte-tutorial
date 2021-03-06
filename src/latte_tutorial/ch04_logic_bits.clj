
;;{
;; # Bits of logic with natural deduction
;; 
;; Now that we have some knowledge of the rules of the game,
;; we can start playing with the LaTTe proof assistant, and
;; do some actual logic.
;;}

(ns latte-tutorial.ch04-logic-bits
  ;; In this namespace we will start to use LaTTe "for real",
  ;; so we introduce the main forms from the core namespace
  (:require [latte.core :as latte :refer [definition defthm deflemma
                                          example try-example
                                          proof try-proof
                                          assume have pose qed
                                          forall lambda]]
            ;; we will also exploit the basic proposition from the prelude
            [latte-prelude.prop :as p :refer [and and* or or* not <=>]]

            ;; and existentials require the following namespace
            [latte-prelude.quant :as q :refer [exists ex ex-def]]

            ;; we will also use the documentation
            [clojure.repl :refer [doc]])

  
  ;; also, these belong to logic or formal arithmetic
  (:refer-clojure :exclude [and or not]))

;;{
;; [Natural deduction](https://en.wikipedia.org/wiki/Natural_deduction)
;; is, very roughly, a way of presenting and formalizing logics based on:

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
;; [prop](https://github.com/latte-central/latte-prelude/blob/master/src/latte_prelude/prop.clj) and 
;; [quant](https://github.com/latte-central/latte-prelude/blob/master/src/latte_prelude/quant.clj) namespaces
;; of the [latte-prelude](https://github.com/latte-central/latte-prelude) library, a.k.a. the "standard" library.
;;}

;;{
;; ## Conjunction
;; 
;; Conjunction, or logical `and`, is where most presentations of natural
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
;; But we will write our own version so that we can "play" with it
;; (the one defined in the prelude is declared *opaque* which means
;; the definition is hidden from the user).
;;}

(definition my-and
  "logical conjunction, a remake"
  [[A :type] [B :type]]
  (forall [C :type]
    (==> (==> A B C)
         C)))
;; => [:defined :term my-and]

;;{
;; A mathematical definition in LaTTe is of the form:
;; 
;; ```clojure
;; (definition <name>
;;    "<docstring>"
;;    [[x1 T1] ... [xN TN]] ;; <parameters>
;;    <body-type>)
;; ```
;; 

;; The `<body>` of the definition is a type, hence a term of type `:type` that
;; is parameterized.
;; Such a definition is also a `def` in the Clojure sense, it has e.g. a
;; documentation:
;;}

(doc my-and)
;;{
;; 
;; > ```
;; > latte-tutorial.ch04-logic-bits/my-and
;; > ([[A :type] [B :type]])
;; >   
;; > (forall [C :type] (==> (==> A B C) C))
;; > ```
;; > 
;; > **Definition**: logical conjunction, a remake.
;; 
;;}

;;{ 
;; We will see many definitions in this tutorials, so let's
;; go back to what is called the "second order characterization
;; of conjunction" (originating from [System F](https://en.wikipedia.org/wiki/System_F)).
;; While this can be interpreted as a
;; generic proof scheme based on the knowledge of two
;; propositions `A` and `B`, in natural deduction we
;; prefer to decompose the scheme in two parts: the
;; introduction of a conjunction, or its eliminations.
;; 

;; ### Introduction rule
;; 

;; Informally, the introduction rule for conjunction
;; is often presented as follows:
;; 
;; ```
;;    A     B
;; ============= (and-intro)
;;   (and A B)
;; ```
;; 
;; The horizontal "double bar" means implication, thus this reads as follows:
;; 
;; > If both proposition `A` and `B` hold, then we can deduce
;; > that the conjunction `(and A B)` also holds.
;; 
;; This is often introduced in an axiomatic way, i.e. without any justification,
;; but in type theory the definition above can be used to prove this as a theorem.
;; To introduce a theorem, we use the `defthm` form, and this is how we
;; can formalize the introduction rule in LaTTe:
;;}

(defthm my-and-intro
  "Introduction rule for conjunction."
  [[A :type] [B :type]]
  (==> A B
       (my-and A B)))
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
;;                   (#'latte-tutorial.ch04-logic-bits/my-and A B))),
;;       :proof nil}

;;{
;; In the Clojure terminology this is a *record* with a few self-explicit
;; fields. We can see that the `:proof` field is `nil`.
;; To understand that "everything is under control", let's try to use
;; the theorem somehow.
;;}

(try-example [[A :type]]
    (==> A A (my-and A A))
  (qed (my-and-intro A A)))
;; = > [:failed "Proof failed: Qed step failed: cannot infer term type."
;;              {:cause {:msg "Theorem has no proof.",
;;                       :thm-name my-and-intro},
;;               :meta {:line 165, :column 3}}]


;;{
;; The `try-example` form let us state propositions together with
;; their proof. It is like a theorem that we do not plan to save for further
;; use. In real developments, the use of the `example` variant is recommended
;; since it will throw an exception in case of a problem, hence it is a
;; nice utility for both documenting by example as well as self-testing.
;; We will go back to the way the proofs are written at a later stage,
;; so let's just observe that using a theorem without a proof is forbidden
;; in LaTTe (or at least [it should be](https://github.com/latte-central/latte-kernel/commit/0ae1f187de15d60ff0376520575e9bdf9a68e21c)).
;;}

;;{
;; Thus we have to write a formal proof that `my-and-intro` really is a theorem.
;; There are two options in LaTTe to do so:
;; 
;;  1. we can write a proof term, using the proof-as-program side of the Curry-Howard correspondance, like we did previously
;;  2. or we can write a declarative proof following the natural deduction style.
;; 
;; We already know how to write a proof term, so let's first demonstrate the first possibility.
;; To prove a theorem in LaTTe, we have to use the `proof` function (it is not a macro because it doesn't have to be), which expects arguments of the following form:
;; 
;; 
;; ```clojure
;; (proof '<theorem-name>
;;    <proof-script>)
;; ```
;; 
;; The `<proof-script>` part is based on a very reduced set of constructions, the simplest one
;; being `(qed <proof-term>)` when we want to conclude the proof using a proof term.
;; Here is an example of a direct demonstration using `qed`:
;;}

(proof 'my-and-intro
  (qed (λ [x A]
          (λ [y B]
             (λ [C :type]
                (λ [z (==> A B C)]
                   ((z x) y)))))))
;; => [:qed my-and-intro]

;;{
;; The proof is accepted but even for this simple fact writing explicitly
;; the whole proof term is cumbersome at the very least and, most of all, quite unlike 
;; a "pencil & paper" mathematical proof.
;; So we will rewrite this proof using a more *declarative* style.
;; We will also use the variant `try-proof` which doesn't generate
;; an exception when a proof fails. This is a very useful tool when
;; elaborating proofs step by step.
;; 
;; First we have our basic assumptions: that the propositions `A` and `B` hold.
;; We can write the following:
;;}

(try-proof 'my-and-intro
  (assume [x A
           y B]))
;; => [:failed my-and-intro {:msg "Proof incomplete."}]

;;{
;; Assumptions as introduced by the following form:
;; 
;; ```clojure
;; (assume [hyp1 typ1
;;          ...
;;         [hypN typN]
;;    <script-within-assumptions>)
;; ```
;; 

;; Technically speaking, this creates the enclosing
;; lambda's corresponding to the assumptions. But from a logical
;; point of view, we just have to see this as a statement of assumptions.
;; 
;; When evaluating the form above the "error" message we get is that
;; the proof is incomplete. This  is good because it also says
;; that there is no error in our reasoning, only we're not finished.
;; 

;; To finish the proof we have to find a term of type `(my-and A B)`.
;; Now, let's remind the internal definition of conjunction:
;; 

;; ```clojure
;; (forall [C :type] (==> (==> A B C) C))
;; ```
;; 

;; There are two further assumptions here: that we have an arbitrary
;; type `C` and an assumption, let's say `H` that `(==> A B C)`
;; (from `A` and `B` we can deduce `C`). So in the next step we get
;; the following:
;;}

(try-proof 'my-and-intro
  (assume [x A
           y B]
    (assume [C :type
             H (==> A B C)])))
;; => [:failed my-and-intro {:msg "Proof incomplete."}]

;;{
;; Note that we could use a single `assume` form here but
;; we have here perhaps a cleaner separation between the
;; theorem assumptions (often called the *hypotheses*),
;; and the ones corresponding to the definition of `my-and`.
;; In the next step, we have to build, from all these
;; assumptions, a term of type `C`. We say that our current *goal*
;; is the proposition `C`. Let's proceed step-by-step.
;; First, we can see `H` as a function that expects a first
;; argument of type `A`, and returns a function of type `(==> B C)`.
;; We can use the `have` form to create such an intermediate result.
;;}

(try-proof 'my-and-intro
  (assume [x A
           y B]
    (assume [C :type
             H (==> A B C)]
      (have <a> (==> B C) :by (H x)))))
;; => [:failed my-and-intro {:msg "Proof incomplete."}]

;;{
;; A `have` proof step has the following form:
;; 

;; ```clojure
;; (have <step-name> <prop/type> :by <proof-term>)
;; ```
;; This an intermediate proof that the proposition `<prop/type>` (remember proposition-as-type)
;; holds with the given `<proof-term>`. Hence this is like a statement and proof of an intermediate
;; lemma, a building block for a full proof.
;; 

;; Once again there is no error here, and what we did is to simultaneously:
;; 
;;  - from a computational point of view created a function named `<a>` of type `(==> B C)`
;;  - from a logical point of view demonstrated that `(==> B C)` holds, under the specified hypotheses.
;; 
;; This is really the Curry-Howard correspondance at work.
;; Not that such an intermediate result is checked by LaTTe. To observe this, let's write
;; a wrong statement:
;;}

(try-proof 'my-and-intro
  (assume [x A
           y B]
    (assume [C :type
             H (==> A B C)]
      (have <a> (==> C C) :by (H x)))))
;; => [:failed my-and-intro
;;       {:msg "Have step elaboration failed: synthetized term type and expected type do not match",
;;        :have-name <a>,
;;        :expected-type (Π [⇧ C] C),
;;        :synthetized-type (Π [⇧' B] C), :meta {:line 302, :column 7}}]

;;{
;; As we can see, LaTTe is very verbose in its error message, which is often a good thing but
;; only after some practice with the environment.
;; Going back to our *correct* intermediate result, we can easily produce a desired term
;; of type `C`, because we have now our function `<a>` of type `(==> B C)`.
;;}

(try-proof 'my-and-intro
  (assume [x A
           y B]
    (assume [C :type
             H (==> A B C)]
      (have <a> (==> B C) :by (H x))
      (have <b> C :by (<a> y)))))
;; => [:failed my-and-intro {:msg "Proof incomplete."}]

;;{
;; You would maybe expect that the proof was complete, but what we did
;; here was just asserting two intermediate propositions under the specified
;; assumptions. What LaTTe did was to check these to be correct, but we
;; are still missing the connection with our initial objective.
;; To conclude our proof we have to use the `qed` form, as follows:
;;}

(try-proof 'my-and-intro
  (assume [x A
           y B]
    (assume [C :type
             H (==> A B C)]
      (have <a> (==> B C) :by (H x))
      (have <b> C :by (<a> y))))
  (qed <b>))
;; => [:qed my-and-intro]

;;{
;; Note that we first closed our assumptions, and used the intermediate
;; step `<b>` outside the assumptions. Technically speaking, this builds
;; up the term `<b>` within the required lambdas. Put in other terms,
;; our direct proof and this declarative version are exactly the same
;; internally. But as we will see, the fact that proofs can be elaborated
;; in a step-by-step manner like what we did last really makes LaTTe
;; a proof assistant and not just a type-checker. We can do *real* mathematics
;; with only three constructs: `assume`, `have` and a final `qed`.
;; 

;; And now we can write our example:
;;}

(example [[A :type]]
    (==> A A (my-and A A))
  (qed (my-and-intro A A)))
;; => [:checked :example]

;;{
;; In the LaTTe prelude the introduction rule is called `and-intro-thm` thus
;; we can rewrite the example as follows:
;;}

(example [[A :type]]
    (==> A A (and A A))
  (qed (p/and-intro-thm A A)))
;; => [:checked :example]

;;{
;; We'll see that there is a variant named `and-intro` in the prelude that is
;; used much more often in practice.
;;}

;;{
;; 

;; ### Elimination rules
;; 

;; Let's see now if we can do the same for the elimination rules.
;; There are two ways to "eliminate" a conjunction:
;; 

;; ```
;;  (and A B)                      (and A B) 
;; =========== (and-elim-left)    =========== (and-elim-right)
;;      A                              B
;; ```
;; 
;; This is obvious: if both `A` and `B` hold then *either*
;; `A` or `B` can be deduced. Let's state and prove the left version.
;;}

(defthm my-and-elim-left
  "Left-elimination of conjunction."
  [[A :type] [B :type]]
  (==> (my-and A B)
       A))

;;{
;; The proof for this is easy but not trivial. Let's first sketch it.
;; Having `(and A B)` means `(forall [C :type] (==> (==> A B C) C))` by definition.
;; Hence, specializing for proposition `A` we get `(==> (==> A B A) A)`.
;; (we just replaced `C` by `A` in the definition).
;; So we can obtained our expected goal `A` if we can prove that `(==> A B A)` is
;; true. Let's state this as an intermediate lemma:
;;}

(deflemma my-impl-ignore
  [[A :type] [B :type]]
  (==> A B A))

;;{
;; A *lemma* is like a theorem but with the purpose of being used as an
;; intermediate step in the proof of an *actual* theorem. The way we
;; interprete this in Clojure is that a theorem is exported in the namespace
;; whereas a lemma remains *private*. This can be of course changed by
;; playing with Clojure's metadata (a very neat mechanism by the way!).
;; I find it quite interesting to give precise interpretation of relatively
;; subjective mathematical concepts: a theorem is public/exported, a lemma
;; is not.
;; 
;; The proof of the lemma is straightforward so let's write it in the declarative style:
;;}

(proof 'my-impl-ignore
  (assume [x A
           y B]
    (have <a> A :by x))
  (qed <a>))

;;{
;; And now we are ready for the proof of the left elimination:
;;}

(proof 'my-and-elim-left
  (assume [H (my-and A B)]
    "We first specialize the definition of `my-and`"
    (have <a> (==> (==> A B A) A) :by (H A))
    "Then we use our intermediate lemma"
    (have <b> (==> A B A) :by (my-impl-ignore A B))
    "And we reach our goal"
    (have <c> A :by (<a> <b>)))
  (qed <c>))

;;{
;; Note that we intersped some comments in the proof, so that it can
;; be read almost like a traditional mathematical proof.
;; 

;; In the LaTTe prelude, the left elimination rule is called `and-elim-left-thm`.
;; There is a variant, named `and-elim-left`, that is used in most cases, we'll
;; see why in a moment.
;; 

;; **Exercise**: state and prove the right elimination rule: `my-and-elim-right`.
;; (in the prelude, the rule is `and-elim-right-thm` and the one used in practice
;; is `and-elim-right`).
;; 

;; Now that we have our reasoning rules for conjunction, let's try to use them.
;; For this we state the following proposition (as a side note, I personnally
;; like to call a yet unproven theorem a proposition).
;;}

(defthm my-and-trans
  "A kind of transitivity for conjunction."
  [[A :type] [B :type] [C :type]]
  (==> (my-and A B) (my-and C B)
       (my-and A C)))

;;{
;; This is not a very interesting proposition, but it should hold and intuitively
;; we should only need the introduciton and left-elimination rules we just
;; proved.
;; 

;; Let's write again our proof sketch before writing the LaTTe code
;; (in practice, we would rather use the incremental construction of
;; "incomplete proofs" until reaching our goal, but we'll start to be
;; less verbose from now on).
;; 

;; First, our assumptions are, say:
;; - an hypothesis that `(my-and A B)` holds, let's call it `H1`
;; - an hypothesis tha  `(my-and C B)` holds, let's call it `H2`
;; Now, we'll first prove that `A` holds, using our left elimination rule.
;; The definition of the term `(my-and-elim-left A B)` is the following:
;; ```clojure
;; (==> (my-and A B) A)
;; ```
;; Hence, in computational terms, it is a function taking as a parameter
;; a term of type `(my-and A B)` and returning an `A`.
;; Hence, to obtain an `A` we simply have to apply this function to our
;; term `H1`.
;; Similarly, to obtain a `B` we have to apply the term `H2` to the
;; function `(my-and C B)`.
;; And now that we have an `A` and a `B` we can build a conjunction
;; using the introdution rule.
;; The complete proof is as follows:
;;}

(proof 'my-and-trans
  (assume [H1 (my-and A B)
           H2 (my-and C B)]
    (have <a> A :by ((my-and-elim-left A B) H1))
    (have <b> C :by ((my-and-elim-left C B) H2))
    (have <c> (my-and A C) :by ((my-and-intro A C) <a> <b>)))
  (qed <c>))
;; => [:qed my-and-trans]

;;{
;; This works! We performed our first elimnation-then-introduciton reasoning,
;; which is a very frequent proof scheme.
;; 

;; But we can argue that from a mathematical point of view, the proof
;; is a little bit verbose and with some redundancy.
;; 

;; LaTTe offers some extra features, being basic type theory, to address
;; some of these issues. Let's restate our theorem based on the
;; prelude library.
;;}

(defthm and-trans
  "A kind of transitivity for conjunction."
  [[A :type] [B :type] [C :type]]
  (==> (and A B) (and C B)
       (and A C)))

;;{
;; This is the same as before, but this time using the prelude definition
;; for conjunction.
;; Now we remark that the assumptions are written in the theorem statement,
;; so we might wonder why we have to restate them in the proof.
;; This is sometimes useful, because there can be some "distance" between
;; the theorem and its proof (e.g. because we need to state and proof intermediate
;; lemmas), but very often the proof is "just below" the theorem.
;; Here our hypotheses are short so it's not really a problem, but sometimes
;; hypotheses are large multiline statements.
;; In such cases, we can simply use the underscode character `_` and let
;; LaTTe figure out the hypotheses given the definition. Of course there is
;; no magic: they will be exaclty like before.
;; 

;; So the beginning of our proof will be as follows:
;; 

;; ```clojure
;; (assume [H1 _ H2 _]
;;    <rest-of-the-proof>)
;; ```
;; Of course we have then to look at the hypotheses in the theorem body.
;;}

;;{
;; In the previous proof, it was also a little bit cumbersome to explicitly
;; write the types for the elimination and introduction rules. For example,
;; it should be obvious for `H1` that the involved types as `A` and `B`
;; (in this order), and similarly `C` and `B` for `H2`.
;; In a proof assistant such as Coq or Agda, a very powerfull type inference
;; "algorithm" (I use quotes since the problem is indecidable in type theory, i.e.
;; the inference can fail or loops). In LaTTe I decided not to rely on such
;; an algorithm because of its complexity: both from the implementor and
;; the user point of view. In the current state of affairs, we use the
;; notion of an *implicit*, which consists in allowing the user of LaTTe
;; to write an arbitrary Clojure program to analyse and transform a term.
;; There are many such implicits in the prelude, and in particular:
;; 
;; - the introduction rule for conjunction `and-intro`
;; - the left and right elimination rules: `and-elim-left` and `and-elim-right`.
;; 
;; Let's see their documentation:
;;}

(doc p/and-intro)
;;{
;; > ```
;; > latte-prelude.prop/and-intro
;; >  
;; > (and-intro a b)
;; > ```
;; > 
;; > An introduction rule that takes a proof
;; > `a` of type `A`, a proof `b` of type `B` and yields
;; > a proof of type `(and A B)`.
;; > 
;; > This is an implicit version of [[and-intro-thm]].
;; 
;;}

(doc p/and-elim-left)
;;{
;; > ```
;; > latte-prelude.prop/and-elim-left
;; >   
;; > (and-elim-left and-term)
;; > ```
;; > 
;; > An implicit elimination rule that takes a proof
;; > of type `(and A B)` and yields a proof of `A`.
;; > 
;; > This is an implicit version of [[and-elim-left-thm]].
;; 
;;}

(doc p/and-elim-right)
;;{
;; 
;; > ```
;; > latte-prelude.prop/and-elim-right
;; >   
;; > (and-elim-right and-term)
;; > ```
;; > 
;; > An implicit elimination rule that takes a proof
;; > of type `(and A B)` and yields a proof of `B`.
;; > 
;; > This is an implicit version of [[and-elim-right-thm]].
;; 
;;}

;;{
;; Using these implicit variants, we do not need to state the
;; types explicitly when introducing or eliminating the conjunctions.
;; Our proof then is simplified as follows.
;;}

(proof 'and-trans
  (assume [H1 _ H2 _]
    (have <a> A :by (p/and-elim-left H1))
    (have <b> C :by (p/and-elim-left H2))
    (have <c> (and A C) :by (p/and-intro <a> <b>)))
  (qed <c>))
;; => [:qed and-trans]

;;{
;; ### N-ary variants
;; 
;; The conjunction is LaTTe is a binary operator, like it is always the case
;; in mathematical logics. However as Lispers we know the interest of n-ary
;; associative operators. While we cannot do so at the primitive level,
;; the prelude handles such cases, as illustrated by the following examples.
;;}

;; n-ary introduction
(example [[A :type] [B :type] [C :type] [D :type]
          [a A] [b B] [c C] [d D]]
    (p/and* A B C D)
  (qed (p/and-intro* a b c d)))
;; => [:checked :example]

;; n-ary eliminations
(example [[A :type] [B :type] [C :type] [D :type]]
    (==> (p/and* A B C D)
         A)
  (assume [H _]
    ;; eliminate first operand (A)
    (have <a> A :by (p/and-elim* 1 H)))
  (qed <a>))
;; => [:checked :example]

(example [[A :type] [B :type] [C :type] [D :type]]
    (==> (p/and* A B C D)
         C)
  (assume [H _]
    ;; eliminate third operand (C)
    (have <a> C :by (p/and-elim* 3 H)))
  (qed <a>))
;; => [:checked :example]

;;{
;; An important advice is to avoid mixing the binary and nary constructs:
;; 
;;  - use `and-intro`, `and-elim-left` and `and-elim-right` with binary conjunction: `and`
;;  - use `and-intro*` and `and-elim*` with the nary variant: `and*`
;;}

;;{
;; ### Equivalence = conjunction of implications
;; 
;; An important construct of logic is the equivalence of two propositions,
;; which is defined as follows in the prelude:
;; 
;; ```clojure
;; (definition <=>
;;   "Logical equivalence or 'if and only if'."
;;   [[A :type] [B :type]]
;;   (and (==> A B)
;;        (==> B A)))
;; ```
;; The introduction rule is `iff-intro-thm` in the prelude, but it's
;; quite easy to reconstruct one.
;;}

(defthm my-iff-intro-thm
  "Introduction of equivalence."
  [[A :type] [B :type]]
  (==> (==> A B)
       (==> B A)
       (<=> A B)))
;; => [:declared :theorem my-iff-intro-thm]

(proof 'my-iff-intro-thm
  (assume [Hif (==> A B)
           Honly-if (==> B A)]
    (have <a> (<=> A B) :by (p/and-intro Hif Honly-if)))
  (qed <a>))
;; => [:qed my-iff-intro-thm]

;;{
;; In the same spirit the elimination rules `iff-elim-if-thm` and `if-elim-only-if-thm`
;; of the prelude are conjunction eliminations in disguise.
;;}

(defthm my-iff-elim-if-thm
  "Elimination of \"if\" part of an equivalence."
  [[A :type] [B :type]]
  (==> (<=> A B)
       (==> A B)))
;; => [:declared :theorem my-iff-elim-if-thm]

(proof 'my-iff-elim-if-thm
  (assume [Heq (<=> A B)]
    (have <a> (==> A B) :by (p/and-elim-left Heq)))
  (qed <a>))
;; => [:qed my-iff-elim-if-thm]

;;{
;; **Exercise**: define and prove the "only if" elimination.
;;}

;;{
;; Note that in the prelude the rules to use in practice are
;; the implicit ones: `iff-intro`, `iff-elim-if` and `iff-elim-only-if`.
;;}

(example [[A :type] [B :type]]
    (==> (==> A B)
         (==> B A)
         (<=> A B))
  (assume [H1 _ H2 _]
    (have <a> (<=> A B) :by (p/iff-intro H1 H2)))
  (qed <a>))
;; => [:checked :example]

(example [[A :type] [B :type]]
    (==> (<=> A B)
         (==> A B))
  (qed (lambda [H (<=> A B)]
         (p/iff-elim-if H))))
;; => [:checked :example]

(example [[A :type] [B :type]]
    (==> (<=> A B)
         (==> B A))
  (qed (lambda [H (<=> A B)]
         (p/iff-elim-only-if H))))
;; => [:checked :example]

;;{
;; With some practice, and inspecting the quite readable sources
;; of the prelude, you will quickly master the use of implicits.
;; But don't forget that the non-implicit versions are always
;; useable. Moreover, implicit variants are not always proposed,
;; so consulting the documentation is always a good thing.
;;}

;;{
;; ## Disjunction and proof-by-cases
;; 
;; Instead of reconstructing things like we did with conjunction, we will
;; directly use the introduction and elimination for disjunction (logical *or*)
;; as they are defined in the prelude, and not redefine them (it is a good exercise).
;; 
;; There are two introduction rules and one elimination rule for `or`, which is exactly
;; the opposite of conjunction. The introduction rules are as follows:
;; 
;; ```clojure
;; (defthm or-intro-left-thm
;;   [[A :type] [B :type]]
;;   (==> A
;;        (or A B)))
;; 
;; (defthm or-intro-right-thm
;;   [[A :type] [B :type]]
;;   (==> B
;;        (or A B)))
;; ```
;; The meaning is obvious, if `A` holds then the disjunction `A` *or* `B` also holds, this is the left introduction.
;; And the right introduction can be applied if `B` holds. We can also use the *implicits* `or-intro-left` (resp. `or-intro-right`)
;; with which the types `B` (resp. `A`) are inferred.
;; 
;; 
;; There are of course implicit variants of the rules.
;;}

(doc p/or-intro-left)
;;{
;; > ```
;; > (or-intro-left proofA B)```
;; > 
;; > Left introduction for a disjunction `(or A B)`, with `proofA` a proof of `A`.
;; > ```
;;}

(doc p/or-intro-right)
;;{
;; > ```
;; > (or-intro-right A proofB)```
;; > 
;; > Right introduction for a disjunction `(or A B)`, with `proofB` a proof of `B`.
;; > ```
;; 
;; As an illustration, if you know that both `A` and `B` holds, then there are two ways to prove that either of them holds.
;;}

(example [[A :type] [B :type]]
    (==> (and A B)
         (or A B))
  ;; The "left" proof:
  (assume [H (and A B)]
    (have <a> A :by (p/and-elim-left H))
    "We have A thus we can introduce (or A B) from the left"
    (have <b> (or A B) :by (p/or-intro-left <a> B)))
                           ;; a.k.a. ((p/or-intro-left-thm A B) <a>)))
  (qed <b>))
;; => [:checked :example]

(example [[A :type] [B :type]]
    (==> (and A B)
         (or A B))
  ;; The "right" proof:
  (assume [H (and A B)]
    (have <a> B :by (p/and-elim-right H))
    "We have B thus we can introduce (or A B) from the right"
    (have <b> (or A B) :by (p/or-intro-right A <a>)))
                           ;; a.k.a. ((p/or-intro-right-thm A B) <a>)))
  (qed <b>))
;; => [:checked :example]

;;{
;; The elimination rule is a little bit more complex because it implements
;; a very general *proof-by-case* scheme.
;; 
;; ```clojure
;; (defthm or-elim-thm
;;   [[A :type] [B :type]]
;;   (==> (or A B)
;;        (forall [C :type]
;;          (==> (==> A C)
;;               (==> B C)
;;               C))))
;; ```
;; 
;; Its informal reading is as follows. If you know that either the proposition `A` or the proposition `B` holds
;; (it is not exclusive: `A` and `B` may be true also, but then it is either to use this fact), then suppose
;; your goal is to prove some proposition `C`. Then you have two things to do to demonstrate that `C` holds:
;; 
;; - the first "left" case: under the assumption that `A` holds, you prove that also `C` holds, i.e. `A` implies `C`
;; - the second "right" case: you prove that `B` implies `C` also
;; 
;; Hence, since in both case `C` is true you know that `(or A B)` is enough as an assumption.
;; There is of course an implicit version `or-elim` which is the one we will use in practice.
;;}

(doc p/or-elim)
;;{
;; > ```
;; > (or-elim or-term prop left-proof right-proof)
;; > ```
;; > 
;; > An elimination rule that takes a proof
;; > `or-term` of type `(or A B)`, a proposition `prop`,
;; > a proof `left-proof` of type `(==> A prop)`, 
;; > a proof `right-proof` of type `(==> B prop)`, and thus
;; > concludes that `prop` holds by `or-elim-thm`.
;; 
;; As an illustration, let's prove the following theorem:
;;}

(defthm my-or-assoc
  "Associativity of disjunction"
  [[A :type] [B :type] [C :type]]
  (==> (or A (or B C))
       (or (or A B) C)))

;;{
;; This is an expected property of disjunction: associativity.
;; Our assumption is `(or A (or B C))`, thus a disjunction and the
;; rule `or-elim` gives the proof-by-case scheme we should follows:
;; 
;; - the first case is for the assumption of `A` alone,
;; - the second case is for assumption `(or B C)`
;; 
;; If in both cases we can reach the conclusion, then we'll have
;; a proof of the theorem... Let's try this...
;;}

(try-proof 'my-or-assoc
  (assume [H (or A (or B C))]
    "First case, we assume `A`."
    (assume [H1 A]
      (have <a1> (or A B) :by (p/or-intro-left H1 B))
      "We reach our first goal below."
      (have <a> (or (or A B) C) :by (p/or-intro-left <a1> C)))
    "Second case, we assume `(or B C)`"
    (assume [H2 (or B C)]
      "...")))
;; => [:failed my-or-assoc {:msg "Proof incomplete."}]

;;{
;; The second case is a little more complex. Our goal is to
;; prove the following, expressed as a lemma:
;;}

(deflemma my-or-assoc-aux
  [[A :type] [B :type] [C :type]]
  (==> (or B C)
       (or (or A B) C)))

(proof 'my-or-assoc-aux
  (assume [H (or B C)]
    "First case: assuming `B`"
    (assume [H1 B]
      (have <a1> (or A B) :by (p/or-intro-right A H1))
      "Ok, we reach the goal"
      (have <a> (or (or A B) C) :by (p/or-intro-left <a1> C)))
    "Seconde case: assuming `C`"
    (assume [H2 C]
      "This is immediate."
      (have <b> (or (or A B) C) :by (p/or-intro-right (or A B) H2)))
    "We can now use the or-elimination"
    (have <c> _ :by (p/or-elim H ; this is the disjunction to eliminate
                               (or (or A B) C) ; and this is ou goal
                               <a> ; proof of the first case
                               <b> ; proof of the second case
                               )))
  "We can conclude"
  (qed <c>))
;; => [:qed my-or-assoc-aux]

;;{
;; At proof step `<c>`, what we want to "have" is `(or (or A B) C)` and
;; we us the `or-elim` rule to obtain this. The reason we use the
;; underscode placeholder `_` is that the type we expect is already the
;; second argument or `or-elim` so there is nothing to gain to
;; repeat it. The `or-elim` is one of the rare occasion when using
;; the underscode is actually useful in `have` steps.
;; 
;; Now that we demonstrated our Lemma, we can finish the proof for
;; our main theorem.
;;}

(proof 'my-or-assoc
  (assume [H (or A (or B C))]
    "First case, we assume `A`."
    (assume [H1 A]
      (have <a1> (or A B) :by (p/or-intro-left H1 B))
      "We reach our first goal below."
      (have <a> (or (or A B) C) :by (p/or-intro-left <a1> C)))
    "Second case, we assume `(or B C)`"
    (assume [H2 (or B C)]
      (have <b> (or (or A B) C) :by ((my-or-assoc-aux A B C) H2)))
    "We eliminate the disjunction."
    (have <c> _ :by (p/or-elim H (or (or A B) C) <a> <b>)))
  (qed <c>))
;; => [:qed my-or-assoc]

;;{
;; Tadaaa! We did it, we reused an auxiliary lemma to prove a main theorem.
;; And we also used the elimination rule for disjunction twice-in-a-row,
;; I think we should be satisfied somehow.
;;}

;;{
;; **Exercise**: state and prove the following:
;; 
;; - Under the assumption `(or A A)` prove `A`  (for an arbitrary proposition `A`)
;; - From `(or A B)` prove `(or B A)`
;;}

;;{
;; ### Proof by "many" cases
;; 
;; There is also an n-ary variant `or*` for disjunction. There is only ones
;; generic introduction rule, as illustrated in the following examples:
;;}

(example [[A :type] [B :type] [C :type] [D :type]]
    (==> B (or* A B C D))
  (qed (lambda [x B] (p/or-intro* A x C D))))
;; => [:checked :example]

(example [[A :type] [B :type] [C :type] [D :type]]
    (==> D (or* A B C D))
  (qed (lambda [x D] (p/or-intro* A B C x))))
;; => [:checked :example]

;;{
;; The elimination rules enables to make a proof with more than two cases,
;; without having to nest multiple occurrences of `or-elim`. 
;;}

(example [[A :type] [B :type] [C :type] [D :type] [E :type]]
    (==> (or* A B C D)
         (==> A E)
         (==> B E)
         (==> C E)
         (==> D E)
         E)
  (assume [Hor _ HA _ HB _ HC _ HD _]
    (have <a> _ :by (p/or-elim* Hor ;; the or* term
                                E ;; our goal
                                HA HB HC HD ;; the 4 cases
                                )))
  (qed <a>))
;; => [:checked :example]

;;{
;; ## Proving by contradiction
;; 
;; It is not because we are doing *logic* that we should *absurdity* at all cost.
;; It is in fact definable in type theory, and in LaTTe it is as follows:
;; 
;; ```clojure
;; (definition absurd
;;   "Absurdity."
;;   []
;;   (forall [α :type] α))
;; ```
;; 
;; If read litteraly, this definition means *everything is provable*.
;; It is thankfully safe to *define* such a concept, what would be dramatic
;; would be if we could prove it as a theorem. Of course, without introducing
;; an axiom (and trusting type theory and its implementation in LaTTe), it
;; is not possible to find a proof of `absurd`.
;; We might wonder, then, what is the interest of writing such an "absurd"
;; formal definition!
;; The first element of answer is the following incursion of the venerable
;; latin language:
;; 
;; ```clojure
;; (defthm ex-falso
;;  "Ex falso sequitur quodlibet
;;   (proof by contradiction, elimination for absurdity)."
;;  [[A :type]]
;;  (==> absurd A))
;; ```
;; 
;; This theorem statement is the definition of *a proof by contradiction*.
;; One of the most frequent "fake news" about intuitionistic logic
;; (and constructive mathematics) is that it would not be possible to
;; make such a proof by contradiction, everything should be "true", and
;; classical reasoning is required to reason about "false" things.
;; Of course this is totally incorrect. We can as an illustration demonstrate
;; the *ex-falso* proof principle:
;;}

(try-example [[A :type]]
    (==> p/absurd A)
  ;; the proof of absurdity
  (assume [H p/absurd]
    (have <a> A :by (H A)))
  (qed <a>))
;; => [:checked :example]

;;{
;; 
;; The proof principle available only in classical logic is the *principle
;; of the exluded middle*, the fact that a proposition can only be
;; true or false. So one can reason that something is true because it "cannot"
;; be false. In intuitionistic logic, one must show *how* something
;; is true or false. We will go back to this discussion in a later chapter
;; but for now just remember that *proof by contradiction* is a different matter. 
;; 
;; In terms of reasoning, the *ex-falso* principle is important. It says that
;; when an assumption is *contradictory*, then it is by showing that absurd
;; is derivable from it. If we manage to do so, then the `ex-falso` theorem
;; allows to prove the expected conclusion.
;; 
;; Before making some trivial examples of proofs by contradiction, the last
;; piece of the puzzle is the operator of logical negation. In type theory
;; it is defined from the absurdity, and in LaTTe it is the following:
;; 
;; ```clojure
;; (definition not
;;   "Logical negation."
;;   [[A :type]]
;;  (==> A absurd))
;; ```
;; Let's put this definition in practice. One basic principle of logic is that
;; nothing can be *at the same* true and false, thus the following should hold:
;;}

(defthm not-and
  [[A :type]]
  (not (and A (not A))))

;;{
;; Note that the statement can be rewritten `(==> (and A (not A)) p/absurd)`.
;;}

(proof 'not-and
  "We first restate the hypothesis."
  (assume [H (and A (not A))]
    "First, we have `A` by assumption."
    (have <a> A :by (p/and-elim-left H))
    "Now, we can 'feed' it to `(not A)`"
    (have <b> p/absurd :by ((p/and-elim-right H) <a>)))
  "this is absurd!"
  (qed <b>))
;; => [:qed not-and]

;;{
;; 
;; We will see other proofs by contradiction in the rest of the tutorial.
;; 
;; **Exercise**: prove the following theorem about "double negation".
;;}

(defthm my-impl-not-not
  [[A :type]]
  (==> A (not (not A))))

;;{
;; What about the converse? Can you prove it?
;;}

;;{
;; ## To be or not to be? That is the existential question!
;; 
;; There is no direct support for *existential quantification* in the
;; kernel theory of LaTTe, unlike the universal (∀) case. However, there is
;; a beautiful encoding of the existential quantifier, which is defined
;; in the [quant](https://github.com/latte-central/latte-prelude/blob/master/src/latte_prelude/quant.clj)
;; library of the LaTTe prelude. It is as follows.
;; 
;; ```clojure
;; (definition ex-def
;;   [[T :type] [P (==> T :type)]]
;;  (forall [α :type]
;;    (==> (forall [x T] (==> (P x) α))
;;         α)))
;; ```
;; The details are not so important but roughly if we write in LaTTe:
;; ```clojure
;; (ex-def T (λ [x T] (P x)))
;; ```
;; for all intent and purpose it has the same logical meaning as saying:
;; 
;; > there exists an `x` of type `T` such that `(P x)` is true.
;; 
;; In LaTTe a convenient *notation* is defined so that `ex-def` expressions
;; are written in a more conventional manner, as follows:
;; 
;; ```clojure
;; (exists [x T] (P x))
;; ```
;; Thus, we now how to write an existential quantification, but *what is* precisely
;; the logical meaning of it requires the associated introduction and elimination rules.
;; 
;;}

;;{
;; ### Introduction rule
;; 
;; For the introduction rule we have:
;; 
;; ```clojure
;; (defthm ex-intro-thm
;;   [[T :type] [P (==> T :type)] [x T]]
;;   (==> (P x)
;;        (ex P)))
;; ```
;; The notation `(ex P)` is a shortcut for when we do not need to isolated the `x` variable
;; in the existential (and `(ex P)` is exactly the same as `(ex-def T P)` with `T` the domain
;; of `P` that is in fact inferred from it).
;; So the rule simply says that if the predicate `P` is true for some `x` then the existential
;; quantification old.
;; 
;; > If `x` is a jupitarian, then there *exists* a jupitarian!
;;  
;; **Exercise**: Given the following definition
;;}

(definition my-ex-def
  [[T :type] [P (==> T :type)]]
  (forall [A :type]
     (==> (forall [x T] (==> (P x) A))
          A)))
;;{
;; Prove the following:
;;}

(defthm my-ex-intro-thm
  [[T :type] [P (==> T :type)] [x T]]
  (==> (P x)
       (my-ex-def T P)))

;;{
;; **Hint**: look at the definition of `my-ex-def`, it's just forall and implication, so 
;; it just a question of following the rules of the game presented in the previous chapter.
;;}

;;{
;; Here is an example of usage of the introduction rule.
;;}

(defthm ex-and-intro
  [[T :type] [P (==> T :type)] [Q (==> T :type)] [x T]]
  (==> (P x)
       (Q x)
       (exists [y T] (and (P y) (Q y)))))

;;{
;; The proof is rather simple.
;;}

(proof 'ex-and-intro
  (assume [HP _ HQ _]
    (have <a> (and (P x) (Q x)) :by (p/and-intro HP HQ))
    (have <b> (exists [y T] (and (P y) (Q y))) 
          :by ((q/ex-intro (lambda [y T] (and (P y) (Q y))) x) <a>)))
  (qed <b>))
;; => [:qed ex-and-intro]

;;{
;; The only non-trival part is the `<b>` step. We are invoking the `ex-intro`
;; rule which require a predicate `P` and a witness `x` that the predicate holds.
;; We then provide the result of step `<a>`, i.e. a proof that `(P x)` holds to
;; the introduction rule, which produces the required existential. 
;;}

;;{
;; **Exercise**: redo the last proof using your own `my-ex-intro-thm`.
;;}

;;{
;; ### Elimination rule
;; 
;; The elimination rule for the existential is the following one:
;; 
;; ```clojure
;; (defthm ex-elim-thm
;;   [[T :type] [P (==> T :type)] [A :type]]
;;   (==> (ex P)
;;        (forall [x T] (==> (P x) A))
;;        A))
;; ```
;; 
;; Considering an arbitrary proposition `A`, the definition says that if we know that there exists an 
;; `x` of type `T` such that `(P x)`  (which is simply denoted by `(ex P)`), 
;; and moreover if forall `x`'s of type `T` from `(P x)` we can deduce `A`, then `A` is true.
;; 
;; One way to explain this definition is that the assumption `(forall [x T] (==> (P x) A))` is very strong.
;; We could deduce `A` by exhibiting a `z` such that `(P z)` and we would obtain `A`. But since we know
;; that one exists, we don't need to explicitely provide this particular `z`.
;; Let's prove this manually, using directly `my-ex-def`.
;;}

(defthm my-ex-elim-thm
  [[T :type] [P (==> T :type)] [A :type]]
  (==> (my-ex-def T P)
       (forall [x T] (==> (P x) A))
       A))

(proof 'my-ex-elim-thm
  (assume [Hex (my-ex-def T P)
           Hall (forall [x T] (==> (P x) A))]    
    "First let's expand the definition of `my-ex-def`."
    (have <a> (==> (forall [x T] (==> (P x) A))
                   A) :by (Hex A))
    "And know it is easy to obtain `A`."
    (have <b> A :by (<a> Hall)))
  "And we're done."
  (qed <b>))
;; => [:qed my-ex-elim-thm]

;;{
;; Let's consider a first example.
;;}

(defthm ex-and-elim-left
  [[T :type] [P (==> T :type)] [Q (==> T :type)]]
  (==> (exists [x T] (and (P x) (Q x)))
       (exists [x T] (P x))))

;;{
;; One possible proof is as follows. 
;;}

(proof 'ex-and-elim
  (assume [Hex _]
    (assume [y T
             Hy (and (P y) (Q y))]
      (have <a> (P y) :by (p/and-elim-left Hy))
      "We need to introduce the existential of the goal."
      (have <b> (exists [x T] (P x)) 
            :by ((q/ex-intro (lambda [x T] (P x)) y) <a>)))
    "Now we are ready for the existential elimination"
    (have <c> _  ;; the obtain proposition is the second argument
          :by ((q/ex-elim (lambda [x T] (and (P x) (Q x))) 
                          ;; below is what we want
                          (exists [x T] (P x)))
               Hex ;; the proof for the existential 
               <b> ;; the proof for the generalization
               )))
  (qed <c>))
;; => [:qed ex-and-elim]

;;{
;; In this proof we used the `ex-elim` implicit, which is like `ex-elim-thm` 
;; but with the first type synthetized, i.e. `(ex-elim P x)` is the 
;; same as `(ex-elim-thm T P x)` provided `P` is of type `(==> T :type)`.
;; 
;; Note that when applying the elimination rule (step `<c>` above), 
;; we used the underscore `_` so that the type of the step is inferred.
;; This is because the type we target is an argument of the elimination rule.
;; In fact the situation is similar to the `or-elim` rule for disjunction,
;; and indeed there is a tight connection between existential and or.
;; Consider the following statement:
;; 
;; > a prime number is 2, or 3, or, 5, or etc. (infinitely) 
;; 
;; This does not define the prime numbers, but merely says that we could
;; list them all because there is \emph{at least} one of them.
;; So from a purely logical point of view, the previous informal statement
;; (an infinite disjunction) can be formalized as a single existential:
;; 
;; > there exists some prime number
;; 
;;}

;;{
;; **Exercise** : state and prove the complement right elimination.
;; Try to use your own `my-ex-elim-thm` in the proof.
;;}

;;{
;; We will now consider a more complex example of a proof involving the existential.
;; The statemenent is as follows:
;;}

(defthm exists-commute
  [[A :type] [B :type] [P (==> A B :type)]]
  (==> (exists [a A]
         (exists [b B] (P a b)))
       (exists [b B]
         (exists [a A] (P a b)))))

;;{
;; This is an apparently trivial property of nested existentials: the order of
;; the quantifier does not matter. While this sounds like a simple property, we
;; already know that we will have to eliminate two existentials in the hypothesis,
;; and we will then have to introduce two existentials in the conclusion.
;; Hence, we will need to use both `q/ex-intro` and `q/ex-elim` twice, but in
;; a nested way. So we can alreay imagine that the proof structure is not as simple
;; as it may seem.
;; 
;; To simplify a little bit the matter, we will also introduce a local definition
;; using the `pose` proof command. Writing:
;; 
;; ```clojure
;; (pose X := <expr>)
;; ```
;; 
;; is exactly the same as writing:
;; 
;; ```clojure
;; (have X _ :by <expr>)
;; ```
;; 
;; Let's dig into the commutation proof.
;;}

(proof 'exists-commute
  (assume [Hex _] ;; cf. the assumption in the theorem
    "We state our goal so that we do not have to write it everywhere."
    (pose GOAL := (exists [b B]
                    (exists [a A] (P a b))))
    "We begin to eliminate the outer existential (for variable `a`)"
    (assume [x A
             Hx (exists [b B] (P x b))]
      "The hypothesis `Hx` is our (P x) in the elimination rule.
our objective is to prove the `GOAL` from it, but first we have
to eliminate the inner existential (for variable `b`)."
      (assume [y B
               Hy (P x y)]
        "We introduce first the inner existential of the `GOAL` 
(i.e. for variable `a`)."
        (have <a> (exists [a A] (P a y)) 
              :by ((q/ex-intro (lambda [a A] (P a y)) x) Hy))
        "And the we introduce the outer existential, reaching the `GOAL`."
        (have <b> GOAL
              :by ((q/ex-intro (lambda [b B] (exists [a A] (P a b))) y) 
                   <a>)))
      "We are now ready to eliminate the inner existential."
      (have <c> _ :by ((q/ex-elim (lambda [y B] (P x y)) GOAL)
                          Hx <b>)))
    "And we can ultimately eliminate the outer existential."
    (have <d> _ :by ((q/ex-elim (lambda [x A] (exists [b B] (P x b))) GOAL)
                        Hex <c>)))
  "We're done!"
  (qed <d>))
;; => [:qed exists-commute]

;;{
;; This should illustrate the relative complexity of the existential
;; proof methods, especially the elimination part. However, we should
;; keep in mind that existential reasoning is quite a powerful concept!
;; I do not think there's too much incidental complexity involved here.
;; 
;; **Exercise** : prove the following theorem.
;;}

(defthm ex-impl
  [[T :type] [P (==> T :type)] [Q (==> T :type)]]
  (==> (exists [x T] (P x))
       (forall [y T] (==> (P y) (Q y)))
       (exists [x T] (Q x))))

;;{
;; ## Natural logic, in summary
;; 
;; In this chapter, we discussed the following topics.
;; 
;; - Natural logic is based on introduction and elimination rules,
;; - The implication and universal quantification are primitive in type theory in LaTTe.
;; They are introduced with `lambda` and eliminated with function application.
;; - Conjunction (logical `and`) is a derived principles, with rules `and-intro`, `and-elim-left` and `and-elim-righ` (also the n-ary variants `and*` etc.).
;; - Logical equivalence is a conjunction of two implications, thus ultimately a conjunction. 
;; - Disjunction (logical `or`) is also a derived principle. The rules are `or-intro-left`, `or-intro-right` and `or-elim`. The elimination rule implements the important principle of *proof by case*. For more than two cases, you may use `or*`, `or-intro*` and `or-elim*`.
;; - Negation (logical `not`) is derived from absurdity, and from absurdity one can prove everything. This enables *proofs by contradiction* in LaTTe.
;; - There is a simple yet effective encoding of existential quantification in type theory, with deduction rules `ex-intro` and `ex-elim`.
;;
;; Now that we have a fairly complete logic, we will start to see how to do more traditional mathematics
;; in LaTTe, starting with *set theory*.
;;}


