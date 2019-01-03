
;;{
;; # Chapter 2: The rules of the game
;; 
;; We are now ready to begin our first mathematical development
;; in LaTTe. This will be in a `ch02-game-rules` namespace whose
;; declaration is as follows:
;;}


(ns latte-tutorial.ch02-game-rules
  ;; In this namespace we will only play with (lambda-)terms and types,
  ;; so we require only very few top-level forms from the `core` namespace.
  (:require [latte.core :refer [term type-of type-check?]]))
;; => nil

;;{
;; **Remark**: the `nil` returned by the `ns` form is in general quite a good
;; thing. It means that the requirements are satisfied.
;;}

;;{
;; ## Lambda the ultimate
;;
;; One assumption I make is that you, the reader, you know the "pure" (i.e. untyped) lambda-calculus.
;; This is not a very strong assumption because you can find it right at the core of you favorite
;; programming language.  Indeed, in Clojure the `lambda` is called `fn`, which we use to define
;; anonymous functions. Note that `fn` corresponds to (the classical) `lambda` only if it accepts
;; a single parameter.
;; 
;; As a trivial example consider the identity function:
;; 
;; ```clojure
;; (fn [x] x)
;; ```
;; 
;; This function can be applied to anything to yield the very *same* anything:
;;}

((fn [x] x) 42)
;; => 42

((fn [z] z) :anything)
;; => :anything

;;{
;; We also show that the variables, e.g. `x`, `z`, can be renamed without changing
;; the function, it's still the identity function (unless there's some clash in the renaming).
;; In the set of useful functions, this is maybe the simplest of all and it even deserve
;; a name in the standard Clojure library:
;;}

(identity 42)
;; => 42

;;{
;; As a second, slightly more complex example, consider the composition of two functions
;; `f` and `g`:
;; 
;; ```clojure
;; (fn [f] (fn [g] (fn [x] (g (f x)))))
;; ```
;; Now we can apply this function a few times to see how it works:
;;}

((((fn [f] (fn [g] (fn [x] (g (f x)))))
   even?)                       ;; (==> int boolean)
  (fn [y] (if y "even" "odd"))) ;; (==> boolean string)
 42)
;; => "even"

;;{
;; We took our composition function, and provided the predicate `even?`
;; as the `f` function. As we comment above, this takes an `int` and returns a `boolean`.
;; Then, the `g` function that we use takes a `boolean` and returns a `string`.
;; Thus the composition `g°f` takes an `int` and returns a `string`, either
;; `"even"` if the input of `f` is even, and `"odd"` otherwise.
;;}

((((fn [f] (fn [g] (fn [x] (g (f x)))))
   even?)                       ;; (==> int boolean)
  (fn [y] (if y "even" "odd"))) ;; (==> boolean string)
 41)
;; => "odd"

;;{
;; This is also an important basic functional building block, and it is named `comp` in
;; the Clojure standard library.
;;}

((comp (fn [y] (if y "even" "odd")) even?) 42)
;; => "even"

((comp (fn [y] (if y "even" "odd")) even?) 41)
;; => "odd"

;;{
;; These are roughly the only things you need to know about Clojure
;; to begin exploring the LaTTe features.
;;}

;;{
;; ## Types, really ?
;; 
;; In the composition example above we did something rather unusual in Clojure:
;; we described the type of functions using the notation `(==> T U)` with `T` the
;; type of the input, and `U` the type of the returned value.
;; 
;; As we'll quickly see, in a type theory the explicit mentioning of type becomes
;; an essential part of the mathematical language. As I often say if I am not
;; totally sold to the use of (static) types in programming (otherwise I would maybe
;; not use Clojure for starters), I am totally sold to the use of types in logic
;; and mathematics. I find much more interests in having a "set of integers" rather
;; than a "set" without further mentioning of the type of things I'll find as elements.
;; 
;; So if we want to define e.g. the identity function not directly in Clojure but
;; this time in LaTTe (which is also Clojure by the way), we will have to add some type annotations.
;; 
;; In LaTTe, `lambda` is called `lambda`, or `λ`, rather than `fn`. In this part of the tutorial
;; we will rather use the beautiful `λ` rather than its ascii spelling. This is to emphasis
;; that we are not yet at the user-level of the proof assistant, we only play with its λ-calculus kernel.
;; 
;; Thus our starting point is this:
;; 
;; ```clojure
;; ;; The identity function in latte (initial version)
;; (term
;;   (λ [x] x))
;;  --> Unhandled clojure.lang.ExceptionInfo
;;      Parse error
;;      {:msg "Wrong bindings in λ form",
;;       :term (λ [x] x),
;;       :from {:msg "Binding must have at least 2 elements", :term [x]}}
;; ```
;;}

;;{
;; The `term`  (or `latte.core/term`) form takes a LaTTe expression in input, parses it, typecheck's it
;; and returns the internal representation of the term as Clojure data.
;; As the exception raised by LaTTe makes clear, there is something missing in our identity function.
;; In fact we need to give an explicit type to the variable `x`, let's try with an arbitrary type named `A`:
;; 
;; ```clojure
;; (term
;;  (λ [x A] x))
;;  --> Unhandled clojure.lang.ExceptionInfo
;;      Type checking error
;;      {:msg "Cannot calculate codomain type of abstraction.",
;;       :term (λ [x A] x),
;;       :from {:msg "Cannot calculate type of variable.",
;;       :term x,
;;       :from {:msg "No such variable in type context", :term A}}}      
;; ```
;;}

;;{
;; As you can see LaTTe is quite verbose when something goes wrong,
;; which is rather a good thing when debugging mathematics!
;; Here we have a type error, and the ultimate reason is that
;; the variable `A` is defined nowhere.
;; 
;; What we would like is to make `A` an arbitrary type, so for
;; this we will add an extra layer of abstraction to our λ.
;;}

(term
 (λ [A :type] (λ [x A] x)))
;; => (λ [A ✳] (λ [x A] x))

;;{
;; This time the form evaluates! The `:type` keyword denotes the "type of all types".
;; Hence in LaTTe the (type-)generic identity function first takes an arbitrary type
;; `A` as a first argument, and returns a function that takes an arbibrary `x` of type
;; `A` to finally return `x` itself. That's generic as it can be!
;; 
;; The value returned by the `term` form (technically a Clojure macro) is the internal
;; representation of the terms in LaTTe. It's almost like what is written except that
;; the type of types is written `✳` internally.
;; Note also that if we use the ascii `lambda` we get the same result:
;;}

(term
 (lambda [A :type] (lambda [x A] x)))
;; => (λ [A ✳] (λ [x A] x))

;;{
;; ## The type of lambda
;; 
;; In LaTTe most terms have types, and the identity function of the previous
;; section is no exception. Thus the question is: *what is the type of the following?*
;; 
;; ```clojure
;; (λ [A :type] (λ [x A] x))
;; ```
;; The answer to this question is perhaps the most important feature of type theory,
;; and in fact it is a very simple answer:
;; 
;; > the type of λ (`lambda`) is ∀ (`forall`)
;; 
;; You might read somewhere that it is a (kind of) product, but it's much simpler
;; to relate *functions* (constructed with λ) and *universal quantifications*
;; (introduced with ∀).
;; 
;; In general, the typing formula is something like:
;; 
;; ```clojure
;; (type-of (λ [x T] e)) ≡ (∀ [x T] (type-of e)) 
;; ```
;; (note that this formula is not actual Clojure code)
;; 
;; Let's try to find the type of the identity function.
;; We have something like:
;; 
;; ```clojure
;; (type-of (λ [A :type] (λ [x A] x)))
;; ≡ (∀ [A :type] (∀ [x A] (type-of x))) 
;; ```
;; Since `x` is supposed of type `A`, we should have:
;; 
;; ```clojure
;; (type-of x) ≡ A
;; ```
;; 
;; Hence:
;; 
;; (type-of (λ [A :type] (λ [x A] x)))
;; ≡ (∀ [A :type] (∀ [x A] A)) 
;; 
;; To try if LaTTe agrees with this, we can use the
;; `type-check?` predicate of LaTTe.
;; 
;;}

(type-check?
 ;; is the term:
 (λ [A :type] (λ [x A] x))
 ;; of type:
 (∀ [A :type] (∀ [x A] A))
 ;; ?
 ) ;; and the answer is:
;; => true

;;{
;; The proof assistant seems to agree... good!
;; 
;; Note that in case you don't find λ or ∀ on your
;; keyboard, you can alternatively "type" the following
;; (pun intended):
;;}

(type-check?
 (lambda [A :type] (lambda [x A] x))
 (forall [A :type] (forall [x A] A)))
;; => true


;;{
;; ## Curry Howard Part One: Propositions as Types
;; 
;; We are now ready for the Curry Howard enlightenment, take one.
;; If you have some level of mathematical background, then the ∀ symbol and its
;; spelling as "for all" should sound rather familiar. The logical interpretation is
;; that of *universal quantification*.
;; 
;; Taken literally, the type:
;; 
;; ```clojure
;; (∀ [A :type] (∀ [x A] A))
;; ```
;; 
;; means something like:
;; 
;; > for all `A` of type `:type`, and for all `x` of type `A`, then `A`
;; 
;; That's not very effective as a logical statement. But everything is *here*
;; except it is not *that* apparent. To obtain a simpler reading (of the
;; same type), we first change a little bit the way we talk about the type `A`.
;; 
;; Saying that `A` is of type `:type` is exactly the same as saying that `A` is a type,
;; and as a synonym in type theory:
;; 
;; >`A` is a proposition (expressed as a type)
;; 
;; (*"proposition as type"* anyone?)
;; 
;; Moreover, remark that in the subterm `(∀ [x A] A)`
;; the variable `x` remains *unusued* (technically we say that
;; there is no free occurence of the variable `x` in the body
;; of the quantified (which is `A` in our example).
;; Informally, this is when the variable remains *"unused"*.
;; 
;; When this is the case, we can use the following simplified notation:
;; 
;; > In a term of the form `(∀ [x A] E)` with an arbitrary expression `e`
;; > if there is no free occurrence of `x` in `e` then the term is the same as:
;; > `(==> A E)`
;; 
;; According to this rule, we thus have:
;; 
;; ```clojure
;; (∀ [A :type] (∀ [x A] A))
;; ≡ (∀ [A :type] (==> A A)) 
;; ```
;; 
;; We can see directly in LaTTe that both notations are considered "the same":
;;}

(term
 (∀ [A :type] (∀ [x A] A)))
;; => (Π [A ✳] (==> A A))

(term
 (∀ [A :type] (==> A A)))
;; => (Π [A ✳] (==> A A))

;;{
;; The internal terms are the same, and in fact the so-called "unparser" of
;; LaTTe automatically applies the simplification.
;; 
;; As a side note, we can see that our universal quantification was rewritten
;; using the capital greek letter Pi (Π). This "new" quantifier is called a **product**
;; and there are some reasons why this terminology is favored over universal quantification
;; in many type theories. But in LaTTe at least there is no difference at all,
;; and the reason we use Π rather than ∀ in the internal representation mostly
;; relates to "historical filiation". Users are encouraged to use the usual
;; mathematical notation for universal quantification.
;; 
;; Hitherto we can propose a better logical meaning for the type of
;; the identity function:
;; 
;; > for all proposition (type) `A`, `A` implies `A`
;; 
;; This is when we interpret `(==> P Q)` as the implication that
;; if `P` holds then also `Q` holds (but maybe not the converse).
;; or the more concise logical property that **implication is reflexive**.
;; 
;; Let's try to put the simplified notation into practice:
;; 
;;}

(type-check?
 ;; term:
 (λ [A :type] (λ [x A] x))
 ;; of type:
 (∀ [A :type] (==> A A)))
;; => true

;;{
;; It works! The identity function captures the fact that implication is
;; reflexive, nice!
;; 
;; Also, the (non-obviously) equivalent computational interpretation is unsurprising:
;; 
;; > for all type `A`, the identity function for this type takes an argument of type `A` and
;; > returns a value of type `A` also
;; 
;; Here we are at the heart of the Curry Howard correspondance.
;; A lambda-abstraction (i.e. a single argument anonyous function) such as identity, has two complementary and in fact equivalent
;; interpretations:
;; 1. a computational interpretation: the arrow type `(==> P Q)` saying that the function takes a value of type `P` as input, and outpus a value of type `Q`.
;; 2. a logical interpretation: the implication `(==> P Q)` saying that if `P` holds then so is `Q`. 
;; 
;; This is an important take away!
;; 
;; **Exercise**
;; 
;; A LaTTe version of the composition function we wrote in Clojure is the following:
;;}

(term
 ;; in Clojure: (fn [f] (fn [g] (fn [x] (g (f x))
 (λ [A B C :type]
    (λ [f (==> A B)]
       (λ [g (==> B C)]
          (λ [x A] (g (f x)))))))
;; => (λ [A B C ✳] ... etc ...

;;{
;; **Remark**: the so-called "telescoped" notation `(λ [A B C :type] ...)`
;; is the same as `(λ [A :type] (λ [B :type] (λ [C :type] ...)`
;; This is a common and useful notational facility (internal lambda's have only one argument).
;; 
;; **Question**:
;; - write the type of the term above  (the telescope notation is also avaiable
;; for ∀). Check your answer with `type-check?`  (or *cheat* with what's come next but that's cheating!).
;; - what is the logical interpretation of this type? Does it say something interesting about implication?
;; (hint: it should!)
;; 
;;}

;;{
;; ## Tell me your type!
;; 
;; So we saw terms, e.g. the (type-generic) identity function, and we saw types such as the reflexivity of implication.
;; In most typed programming language there is a clear distinction between:
;; - the terms that express the dynamics of the programs
;; - their types that are checked statically at compile-time
;; 
;; In LaTTe as in most type theories there is no such a strong distinction.
;; - first types are *also* terms!
;; - but many terms are *not* types.
;; 
;; So how do we make the distinction now?
;; The first and principal rule is the following:
;; 
;; > only terms whose type is `:type`  (or ✳ internally) are actually called *types*
;; 
;; Thus, when we write `(λ [A :type] ...)` we explicitly say that `A` is indeed a type, since it is of type `:type`.
;; 
;; The term `:type` (equivalently ✳) is thus called *"the type of types"*.
;; 
;; But we might wonder if `:type` has itself a type, and in this case what would be this *"type of the type of types*" (sic!).
;; In some old type theories, the type of `:type` was `:type` itself... And in fact it was shown at a much later time that this
;; cyclic definition yields an inconsistent theory: a paradox similar to the problematic notion of
;; a set potentially containing itself.
;; 
;; In modern type theories, an unbounded hierarchy of universe levels are introduced.
;; The type of types is called the universe of lavel 0. The type of the universe 0 is universe 1, etc.
;; However this is in the case of LaTTe too much a complex solution to the problem at hand.
;; 
;; So we are back to the question: what is the type of `:type`, if any?
;; 
;; As it happen, we can ask LaTTe directly, and this is how we ask:
;;}

(type-of :type)
;; => □

;;{
;; The type of a star (✳) is thus a square (□)!
;; Well, we know that ✳ is `:type`, the type of all "actual" types. Since the type of `:type` cannot be
;; `:type` (for the sake of logical consistency) it is not an "actual" type and is thus called *a sort*.
;; So we have the rule:
;; 
;; > The type of all types is **the sort** `:type`
;; 
;; The term represented as a square □ is also a sort, and it is called `:kind`. So we have:
;; 
;; > The type of the sort `:type` is the sort `:kind`
;; 
;; Let's check if `:kind` has a type too, now that we know the `type-of` trick:
;;}

(type-of :kind)
;; --> Unhandled clojure.lang.ExceptionInfo
;;     Type checking error
;;     {:msg "Kind has not type", :term □}

;;{
;; How unfriendly, we got an exception!
;; But at least the message is clear:
;; 
;; > The sort `:kind` has no type!
;; 
;; In fact `:kind` (or □) is the *only* term in LaTTe that has no type.
;; This is thanks to this "escape hatch" that we avoid the inconsistency of
;; cyclic definitions, and the complexity of universe levels.
;; 
;; The fact that we do not need more "machinery" in LaTTe is because it is
;; a very simple type theory, much simpler than the ones found in most
;; other proof assistants. And unlike most proof assistants, the simple
;; type theory used in LaTTe offers a decisive and distinguishing feature
;; 
;; > it is decidable, and quite efficient, to compute the type of an arbitrary (well-formed) term
;; 
;; This is what the `type-of` form allows us to do: ask the type of a term.
;; Let's try on the identity function:
;;}

(type-of (λ [A :type] (λ [x A] x)))
;; => (Π [A ✳] (==> A A))

;;{
;; The returned value should be a type then, so let's check this:
;;}

(type-of (Π [A ✳] (==> A A)))
;; => ✳

;;{
;; Yes! it's a type since we obtain the sort `:type`.
;; 
;; The `type-of` form decides what is called the *"type synthesis"* problem, and we will
;; see at a later stage that it's quite a useful component of our logical toolbox.
;; 
;; **Exercise** : compute the type of the composition function using `type-of`
;; (so *now* you are encouraged to "cheat"!)
;;}

;;{
;; ## Curry Howard Part Two: Programs as Proofs
;; 
;; We are now ready for the Curry Howard enlightenment, take two.
;;
;; With what we learn in the previous sections, we are now able to build implications
;; and universal quantifications using lambda's, but we are missing one important piece
;; of the puzzle: a way to *use* an implication or universal quantification to perform a *deduction*.
;;
;; In the so-called *natural deduction*, an inference rule called the *modus ponens* explains
;; how an implication can be used in a reasoning step. In plain english, the rule states:
;;
;; > If we know that "A implies B", and if moreover "A holds".
;; > Then we can deduce that "B holds" too.
;;
;; This proposition, which is undoubtedly among the most important rules of logic, can be rephased as a type:
;;
;; ```clojure
;; (==> (==> A B) A
;;      B)
;; ```
;;
;; Note that the outermost implication is used here as a kind of "trailed" conjunction: if we *first*
;; have `(==> A B)` and *then* we have `A`, then we can deduce `B`.
;;
;; In the next chapter we will define the more traditional conjunction (`and`) operator, but in type theory
;; the "trailed" implication is used most of the time since it is primitive.
;;
;; According to natural deduction (and logical reasoning indeed), the proposition above should be *true*.
;; This could be a basic law of our logic, which would make the proposition true *philosophically*.
;; But if philosophical truth is OK, mathematical proof is best!
;;
;; The question thus becomes: *what is a proof?*
;; If in philosophy and "everyday" mathematics this question can bring us quite far, once again type theory
;; offers a very simple and "natural" answer: a *proof* is simply a *program* expressed as a lambda-term.
;; This is the programs-as-proofs part of the Curry-Howard correspondance.
;;
;; In LaTTe, this means that in order to prove a proposition $P$, we have to find a term $t$ whose type
;; is $P$. Note that we are not trying to find a particular program/term $t$ but *any* term $t$ whose type
;; is $P$ will do. This notion of *proof irrelevance* makes proving with programs slightly different from
;; programming *per se*. However some proofs are more elegant than others, more efficient (i.e. smaller) than
;; others, etc. So this is not totally unlike programming when before reaching for an efficient solution,
;; one often begins with a naive solution.
;;
;; Going back to our *modus ponens* proposition, we are thus trying to fill the star symbol below with:
;; an adequate term:
;;}

(type-check?
 [A :type] [B :type]
 ;; find a term ...
 ✳
 ;; of type
 (==> (==> A B) A
      B))
;; => false  (for the moment)

;;{
;; To avoid having to many nested lambda's, we introduce a *context*  (akin to a lexical environment
;; in programming terms) composed of two arbitrary variables: `A` and `B` both of type `types`, hence
;; arbitrary propositions/types. We could have introduced then using universal quantifiers but we would
;; have lost the core of what we want to prove. Similarly in Clojure we write:
;;
;; ```clojure
;; (defn myfun [A B] ...)
;; ```
;; rather than:
;; ```clojure
;; (def myfun (fn [A] (fn [B] ...)))
;; ```
;;
;; It is a good exercise to make the `type-check?' form above returns `true` but it is our first formal proof so let's
;; do it together.
;;
;; We know by now (it's in our knowhow) that an implication is build using a lambda abstraction, i.e.:
;;
;; > a type of the form `(==> X Y)` is built using a term of the form `(λ [v X] e)`
;; > with  `e` a term of type `Y`,  which in most cases must use the variable `v` declared of type `X`.
;;
;; Our implication has three members so this becomes:
;;
;; > a type of the form `(==> X Y Z)` is built using a term of the form `(λ [v X] (λ [w Y] e))`
;; > with  `e` a term of type `Z`, using the variable `v` declared of type `X`, and `w` of type `Y`.
;;
;; The inner implication `(==> A B)` resembles a *function type*: a function from type `A` to type `B`.
;; Let's called this function `f`. And then we have a variable of type `A`: let's call it `x`.
;; Hence we could use something of the form:
;;
;; ```clojure
;; (λ [f (==> A B)]
;;   (λ [x A]
;;       ? ;; should be of type B
;; ))
;; ```
;; Let's think in terms of programs now. We have a function `f` from `A` to `B` and a variable `x` of type A`.
;; Applying `f` to `x`, hence `(f x)`, should produce a value of type `B`, exactly what we need.
;; Let's try this!
;;}

(type-check?
 [A :type] [B :type]
 ;; is the term ...
 (λ [f (==> A B)]
    (λ [x A]
       (f x)))
 ;; of type
 (==> (==> A B) A
      B) ;; ?
 )
;; => true  (it works!)

;;{
;; We just wrote a formal proof of the *modus ponens*, and it was like a very
;; basic typed functional program!
;;
;; An very important take away is the tight relation between:
;; - *computation* with function application on the one side, and
;; - *logic* on the other side, with *modus ponens* a.k.a. deduction.
;;
;;}


;;{
;; ## Universal quantification
;; 
;; In type theory, implication is a special case of universal quantification,
;; both are introduced by lambda's. So it is not a surprise that using a
;; universally quantified proposition is *also* related to function application.
;;
;; To demonstrate this, we will take a typical example from the logic curriculum:
;;
;; > All mens are mortal.
;; > Socrates is a man.
;; > Hence Socrates is mortal.
;;
;; This is a *syllogism* attributed to Aristotle. We are very far from modern
;; logic but at least we can use this to illustrate the instantiation of
;; universal quantification: the particular Socrates is an instantiation of "all men".
;;
;; We can translate the proposition in LaTTe, e.g. as follows:
;;
;;}

(type-check?
 [Thing :type] [man (==> Thing :type)] [mortal (==> Thing :type)]
 [socrates Thing]
 ;; we want to replace the following by a term ...
 ✳
 ;; of type
 (==> (∀ [t Thing]
       (==> (man t) (mortal t))) ;; all men are mortal
      (man socrates)  ;; socrates is a man
      ;; thus
      (mortal socrates))) ;; socrates is mortal
;; => false  (for now ...)

;;{
;; Once again we have an implication hence the term we are looking for is
;; of the form:
;;
;; ```clojure
;; (λ [H1 (∀ [t Thing]
;;          (==> (man t) (mortal t)))]
;;   (λ [H2 (man socrates)]
;;      ?  ;; should be a term of type  (mortal socrates)
;; ))
;; ```
;; In the first step, we can build a term of type `(==> (man socrates) (mortal socrates))`
;; by instantiating the universal quantification on "all things" using the particular
;; `socrates`, hence the term: `(H1 socrates)`. Our "puzzle" then becomes:
;;
;; ```clojure
;; (λ [H1 (∀ [t Thing]
;;          (==> (man t) (mortal t)))]
;;   (λ [H2 (man socrates)]
;;      ((H1 socrates)
         ?  ;; should be a term of type  (man socrates)
;; )))
;; ```
;; The term `H2` has exactly the required type, hence in the final step we have:
;;}

(type-check?
 [Thing :type] [man (==> Thing :type)] [mortal (==> Thing :type)]
 [socrates Thing]
 ;; the term ...
 (λ [H1 (∀ [t Thing]
         (==> (man t) (mortal t)))]
    (λ [H2 (man socrates)]
       ((H1 socrates)
         H2)))
 ;; is of type
 (==> (∀ [t Thing]
       (==> (man t) (mortal t)))
      (man socrates)
      (mortal socrates)))
;; => true  (yes!)

;;{
;; We thus wrote a formal proof that Aristotle's syllogism is indeed a
;; theorem in type theory and LaTTe.
;;
;;}

;;{
;; ## The rules of the game, in summary
;; 
;; 1. the type of a lambda-abstraction is a universal quantification
;; 2. if the universally quantified variable is unused, then we have a logical implication, which is *also* an arrow type from the computational point of view
;; 3. function application is instantiation of universal quantification, it is *also* logical deduction in the case of implication
;; 4. types are propositions (a.k.a. Curry Howard part one)
;; 5. programs are proofs (a.k.a. Curry Howard part two)
;; 6. the type of `:type` is the sort `:kind`, and kind is the only term without a type 
;; 
;; These are the basic rules, but we are still far from being able to do actual
;; mathematical developments using only these basic rules. Indeed, directly writing lamda-terms
;; to prove mathematical statements quickly becomes cumbersome and too far away from the
;; way proofs are generally expressed in mathematics. Moreover, we need higher level
;; abstractions, so in the next chapter we will meet the actual LaTTe proof assistant.
;;}
