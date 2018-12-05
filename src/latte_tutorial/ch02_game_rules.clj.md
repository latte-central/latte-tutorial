

# Chapter 2: The rules of the game

We are now ready to begin our first mathematical development
in LaTTe. This will be in a `ch02-game-rules` namespace whose
declaration is as follows:



```clojure
(ns latte-tutorial.ch02-game-rules
  ;; In this namespace we will only play with (lambda-)terms and types,
  ;; so we require only very few top-level forms from the `core` namespace.
  (:require [latte.core :refer [term type-of type-check?]]))
;; => nil

```

**Remark**: the `nil` returned by the `ns` form is in general quite a good
thing. It means that the requirements are satisfied.



## Lambda the ultimate

One assumption I make is that you, the reader, you know the "pure" (i.e. untyped) lambda-calculus.
This is not a very strong assumption because you can find it right at the core of you favorite
programming language.  Indeed, in Clojure the `lambda` is called `fn`, which we use to define
anonymous functions. Note that `fn` corresponds to (the classical) `lambda` only if it accepts
a single parameter.

As a trivial example consider the identity function:

```clojure
(fn [x] x)
```

This function can be applied to anything to yield the very *same* anything:


```clojure
((fn [x] x) 42)
;; => 42

((fn [z] z) :anything)
;; => :anything

```

We also show that the variables, e.g. `x`, `z`, can be renamed without changing
the function, it's still the identity function (unless there's some clash in the renaming).
In the set of useful functions, this is maybe the simplest of all and it even deserve
a name in the standard Clojure library:


```clojure
(identity 42)
;; => 42

```

As a second, slightly more complex example, consider the composition of two functions
`f` and `g`:

```clojure
(fn [f] (fn [g] (fn [x] (g (f x)))))
```
Now we can apply this function a few times to see how it works:


```clojure
((((fn [f] (fn [g] (fn [x] (g (f x)))))
   even?)                       ;; (==> int boolean)
  (fn [y] (if y "even" "odd"))) ;; (==> boolean string)
 42)
;; => "even"

```

We took our composition function, and provided the predicate `even?`
as the `f` function. As we comment above, this takes an `int` and returns a `boolean`.
Then, the `g` function that we use takes a `boolean` and returns a `string`.
Thus the composition `g°f` takes an `int` and returns a `string`, either
`"even"` if the input of `f` is even, and `"odd"` otherwise.


```clojure
((((fn [f] (fn [g] (fn [x] (g (f x)))))
   even?)                       ;; (==> int boolean)
  (fn [y] (if y "even" "odd"))) ;; (==> boolean string)
 41)
;; => "odd"

```

This is also an important basic functional building block, and it is named `comp` in
the Clojure standard library.


```clojure
((comp (fn [y] (if y "even" "odd")) even?) 42)
;; => "even"

((comp (fn [y] (if y "even" "odd")) even?) 41)
;; => "odd"

```

These are roughly the only things you need to know about Clojure
to begin exploring the LaTTe features.



## Types, really ?

```
               _..._
             .'     '.
            /`\     /`\    |\         But ...
           (__|     |__)|\  \\  /|
           (     "     ) \\ || //
            \         /   \\||//            Wait !?!
             \   _   /  |\|`  /
              '.___.'   \____/
               (___)    (___)
             /`     `\  / /
            |         \/ /
            | |     |\  /
            | |     | "`
            | |     |
            | |     |
            |_|_____|
           (___)_____)
           /    \   |
          /   |\|   |
         //||\\  Y  |
        || || \\ |  |
        |/ \\ |\||  |
            \||__|__|
             (___|___)
        jgs  /   A   \
            /   / \   \
           \___/   \___/
```



In the composition example above we did something rather unusual in Clojure:
we described the type of functions using the notation `(==> T U)` with `T` the
type of the input, and `U` the type of the returned value.

As we'll quickly see, in a type theory the explicit mentioning of type becomes
an essential part of the mathematical language. As I often say if I am not
totally sold to the use of (static) types in programming (otherwise I would maybe
not use Clojure for starters), I am totally sold to the use of types in logic
and mathematics. I find much more interests in having a "set of integers" rather
than a "set" without further mentioning of the type of things I'll find as elements.

So if we want to define e.g. the identity function not directly in Clojure but
this time in LaTTe (which is also Clojure by the way), we will have to add some type annotations.

In LaTTe, `lambda` is called `lambda`, or `λ`, rather than `fn`. In this part of the tutorial
we will rather use the beautiful `λ` rather than its ascii spelling. This is to emphasis
that we are not yet at the user-level of the proof assistant, we only play with its λ-calculus kernel.

Thus our starting point is this:

```clojure
;; The identity function in latte (initial version)
(term
  (λ [x] x))
 --> Unhandled clojure.lang.ExceptionInfo
     Parse error
     {:msg "Wrong bindings in λ form",
      :term (λ [x] x),
      :from {:msg "Binding must have at least 2 elements", :term [x]}}
```



The `term`  (or `latte.core/term`) form takes a LaTTe expression in input, parses it, typecheck's it
and returns the internal representation of the term as Clojure data.
As the exception raised by LaTTe makes clear, there is something missing in our identity function.
In fact we need to give an explicit type to the variable `x`, let's try with an arbitrary type named `A`:

```clojure
(term
 (λ [x A] x))
 --> Unhandled clojure.lang.ExceptionInfo
     Type checking error
     {:msg "Cannot calculate codomain type of abstraction.",
      :term (λ [x A] x),
      :from {:msg "Cannot calculate type of variable.",
      :term x,
      :from {:msg "No such variable in type context", :term A}}}      
```



As you can see LaTTe is quite verbose when something goes wrong,
which is rather a good thing when debugging mathematics!
Here we have a type error, and the ultimate reason is that
the variable `A` is defined nowhere.

What we would like is to make `A` an arbitrary type, so for
this we will add an extra layer of abstraction to our λ.


```clojure
(term
 (λ [A :type] (λ [x A] x)))
;; => (λ [A ✳] (λ [x A] x))

```

This time the form evaluates! The `:type` keyword denotes the "type of all types".
Hence in LaTTe the (type-)generic identity function first takes an arbitrary type
`A` as a first argument, and returns a function that takes an arbibrary `x` of type
`A` to finally return `x` itself. That's generic as it can be!

The value returned by the `term` form (technically a Clojure macro) is the internal
representation of the terms in LaTTe. It's almost like what is written except that
the type of types is written `✳` internally.
Note also that if we use the ascii `lambda` we get the same result:


```clojure
(term
 (lambda [A :type] (lambda [x A] x)))
;; => (λ [A ✳] (λ [x A] x))

```

## The type of lambda

In LaTTe most terms have types, and the identity function of the previous
section is no exception. Thus the question is: *what is the type of the following?*

```clojure
(λ [A :type] (λ [x A] x))
```
The answer to this question is perhaps the most important feature of type theory,
and in fact it is a very simple answer:

> the type of λ (`lambda`) is ∀ (`forall`)

You might read somewhere that it is a (kind of) product, but it's much simpler
to relate *functions* (constructed with λ) and *universal quantifications*
(introduced with ∀).

In general, the typing formula is something like:

```clojure
(type-of (λ [x T] e)) ≡ (∀ [x T] (type-of e)) 
```
(note that this formula is not actual Clojure code)

Let's try to find the type of the identity function.
We have something like:

```clojure
(type-of (λ [A :type] (λ [x A] x)))
≡ (∀ [A :type] (∀ [x A] (type-of x))) 
```
Since `x` is supposed of type `A`, we should have:

```clojure
(type-of x) ≡ A
```

Hence:

(type-of (λ [A :type] (λ [x A] x)))
≡ (∀ [A :type] (∀ [x A] A)) 

To try if LaTTe agrees with this, we can use the
`type-check?` predicate of LaTTe.



```clojure
(type-check?
 ;; is the term:
 (λ [A :type] (λ [x A] x))
 ;; of type:
 (∀ [A :type] (∀ [x A] A))
 ;; ?
 ) ;; and the answer is:
;; => true

```

The proof assistant seems to agree... good!

Note that in case you don't find λ or ∀ on your
keyboard, you can alternatively "type" the following
(pun intended):


```clojure
(type-check?
 (lambda [A :type] (lambda [x A] x))
 (forall [A :type] (forall [x A] A)))
;; => true


```

## Curry Howard Part One: Propositions as Types

We are now ready for the Curry Howard enlightenment, take one.
If you have some level of mathematical background, then the ∀ symbol and its
spelling as "for all" should sound rather familiar. The logical interpretation is
that of *universal quantification*.

Taken literally, the type:

```clojure
(∀ [A :type] (∀ [x A] A))
```

means something like:

> for all `A` of type `:type`, and for all `x` of type `A`, then `A`

That's not very effective as a logical statement. But everything is *here*
except it is not *that* apparent. To obtain a simpler reading (of the
same type), we first change a little bit the way we talk about the type `A`.

Saying that `A` is of type `:type` is exactly the same as saying that `A` is a type,
and as a synonym in type theory:

>`A` is a proposition (expressed as a type)

(*"proposition as type"* anyone?)

Moreover, remark that in the subterm `(∀ [x A] A)`
the variable `x` remains *unusued* (technically we say that
there is no free occurence of the variable `x` in the body
of the quantified (which is `A` in our example).
Informally, this is when the variable remains *"unused"*.

When this is the case, we can use the following simplified notation:

> In a term of the form `(∀ [x A] E)` with an arbitrary expression `e`
> if there is no free occurrence of `x` in `e` then the term is the same as:
> `(==> A E)`

According to this rule, we thus have:

```clojure
(∀ [A :type] (∀ [x A] A))
≡ (∀ [A :type] (==> A A)) 
```

We can see directly in LaTTe that both notations are considered "the same":


```clojure
(term
 (∀ [A :type] (∀ [x A] A)))
;; => (Π [A ✳] (==> A A))

(term
 (∀ [A :type] (==> A A)))
;; => (Π [A ✳] (==> A A))

```

The internal terms are the same, and in fact the so-called "unparser" of
LaTTe automatically applies the simplification.

As a side note, we can see that our universal quantification was rewritten
using the capital greek letter Pi (Π). This "new" quantifier is called a **product**
and there are some reasons why this terminology is favored over universal quantification
in many type theories. But in LaTTe at least there is no difference at all,
and the reason we use Π rather than ∀ in the internal representation mostly
relates to "historical filiation". Users are encouraged to use the usual
mathematical notation for universal quantification.

Hitherto we can propose a better logical meaning for the type of
the identity function:

> for all proposition (type) `A`, `A` implies `A`

This is when we interpret `(==> P Q)` as the implication that
if `P` holds then also `Q` holds (but maybe not the converse).
or the more concise logical property that **implication is reflexive**.

Let's try to put the simplified notation into practice:



```clojure
(type-check?
 ;; term:
 (λ [A :type] (λ [x A] x))
 ;; of type:
 (∀ [A :type] (==> A A)))
;; => true

```

It works! The identity function captures the fact that implication is
reflexive, nice!

Also, the (non-obviously) equivalent computational interpretation is unsurprising:

> for all type `A`, the identity function for this type takes an argument of type `A` and
> returns a value of type `A` also

Here we are at the heart of the Curry Howard correspondance.
A lambda-abstraction (i.e. a single argument anonyous function) such as identity, has two complementary and in fact equivalent
interpretations:
1. a computational interpretation: the arrow type `(==> P Q)` saying that the function takes a value of type `P` as input, and outpus a value of type `Q`.
2. a logical interpretation: the implication `(==> P Q)` saying that if `P` holds then so is `Q`. 

This is an important take away!

**Exercise**

A LaTTe version of the composition function we wrote in Clojure is the following:


```clojure
(term
 ;; in Clojure: (fn [f] (fn [g] (fn [x] (g (f x))
 (λ [A B C :type]
    (λ [f (==> A B)]
       (λ [g (==> B C)]
          (λ [x A] (g (f x)))))))
;; => (λ [A B C ✳] ... etc ...

```

**Remark**: the so-called "telescoped" notation `(λ [A B C :type] ...)`
is the same as `(λ [A :type] (λ [B :type] (λ [C :type] ...)`
This is a common and useful notational facility (internall lambda's have only one argument).

**Question**:
- write the type of the term above  (the telescope notation is also avaiable
for ∀). Check your answer with `type-check?`  (or *cheat* with what's come next but that's cheating!).
- what is the logical interpretation of this type? Does it say something interesting about implication?
(hint: it should!)




## Tell me your type!

So we saw terms, e.g. the (type-generic) identity function, and we saw types such as the reflexivity of implication.
In most typed programming language there is a clear distinction between:
- the terms that express the dynamics of the programs
- their types that are checked statically at compile-time

In LaTTe as in most type theories there is no such a strong distinction.
- first types are *also* terms!
- but many terms are *not* types.

So how do we make the distinction now?
The first and principal rule is the following:

> only terms whose type is `:type`  (or ✳ internally) are actually called *types*

Thus, when we write `(λ [A :type] ...)` we explicitly say that `A` is indeed a type, since it is of type `:type`.

The term `:type` (equivalently ✳) is thus called *"the type of types"*.

But we might wonder if `:type` has itself a type, and in this case what would be this *"type of the type of types*" (sic!).
In some old type theories, the type of `:type` was `:type` itself... And in fact it was shown at a much later time that this
cyclic definition yields an inconsistent theory: a paradox similar to the problematic notion of
a set potentially containing itself.

In modern type theories, an unbounded hierarchy of universe levels are introduced.
The type of types is called the universe of lavel 0. The type of the universe 0 is universe 1, etc.
However this is in the case of LaTTe too much a complex solution to the problem at hand.

So we are back to the question: what is the type of `:type`, if any?

As it happen, we can ask LaTTe directly, and this is how we ask:


```clojure
(type-of :type)
;; => □

```

The type of a star (✳) is thus a square (□)!
Well, we know that ✳ is `:type`, the type of all "actual" types. Since the type of `:type` cannot be
`:type` (for the sake of logical consistency) it is not an "actual" type and is thus called *a sort*.
So we have the rule:

> The type of all types is **the sort** `:type`

The term represented as a square □ is also a sort, and it is called `:kind`. So we have:

> The type of the sort `:type` is the sort `:kind`

Let's check if `:kind` has a type too, now that we know the `type-of` trick:


```clojure
(type-of :kind)
;; --> Unhandled clojure.lang.ExceptionInfo
;;     Type checking error
;;     {:msg "Kind has not type", :term □}

```

How unfriendly, we got an exception!
But at least the message is clear:

> The sort `:kind` has no type!

In fact `:kind` (or □) is the *only* term in LaTTe that has no type.
This is thanks to this "escape hatch" that we avoid the inconsistency of
cyclic definitions, and the complexity of universe levels.

The fact that we do not need more "machinery" in LaTTe is because it is
a very simple type theory, much simpler than the ones found in most
other proof assistants. And unlike most proof assistants, the simple
type theory used in LaTTe offers a decisive and distinguishing feature

> it is decidable, and quite efficient, to compute the type of an arbitrary (well-formed) term

This is what the `type-of` form allows us to do: ask the type of a term.
Let's try on the identity function:


```clojure
(type-of (λ [A :type] (λ [x A] x)))
;; => (Π [A ✳] (==> A A))

```

The returned value should be a type then, so let's check this:


```clojure
(type-of (Π [A ✳] (==> A A)))
;; => ✳

```

Yes! it's a type since we obtain the sort `:type`.

The `type-of` form decides what is called the *"type synthesis"* problem, and we will
see at a later stage that it's quite a useful component of our logical toolbox.

**Exercise** : compute the type of the composition function using `type-of`
(so *now* you are encouraged to "cheat"!)



## Deduction with application

(TODO)



## Curry Howard Part Two: Proofs as Programs




## Universal quantification, silogistically

(TODO)


## The rules of the game, in summary

1. the type of a lambda-abstraction is a universal quantification
2. if the universally quantified variable is unused, then we have a logical implication, which is *also* an arrow type from the computational point of view
3. function application is instantiation of universal quantification, it is *also* logical deduction in the case of implication
4. types are propositions (a.k.a. Curry Howard part one)
5. programs are proofs (a.k.a. Curry Howard part two)
6. the type of `:type` is the sort `:kind`, and kind is the only term without a type 

Now that we know the rules, let's put them into practice.

