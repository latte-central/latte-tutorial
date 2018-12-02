

# Chapter 2: The rules of the game
;;
We are now ready to begin our first mathematical development
in LaTTe. This will be in a `ch02-game-rules` namespace whose
declaration is as follows:



```clojure
(ns latte-tutorial.ch02-game-rules

```

In this namespace we will only play with (lambda-)terms and types,
so we require only very few top-level forms from the `core` namespace.

```clojure
  (:require [latte.core :refer [term type-of type-check?]]))
;; => nil

```

**Remark**: the `nil` returned by the `ns` form is in general quite a good
thing. It means that the requirements are satisfied.



## Lambda the ultimate
;;
One assumption I make is that you, the reader, you know the "pure" (i.e. untyped) lambda-calculus.
This is not a very strong assumption because you can find it right at the core of you favorite
programming language.  Indeed, in Clojure the `lambda` is called `fn`, which we use to define
anonymous functions. Note that `fn` corresponds to (the classical) `lambda` only if it accepts
a single parameter.
;;
As a trivial example consider the identity function:
;;
```clojure
(fn [x] x)
```
;;
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
;;
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
;;
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
;;
As we'll quickly see, in a type theory the explicit mentioning of type becomes
an essential part of the mathematical language. As I often say if I am not
totally sold to the use of (static) types in programming (otherwise I would maybe
not use Clojure for starters), I am totally sold to the use of types in logic
and mathematics. I find much more interested in having a "set of integers" rather
than a "set" without further mentioning of the type of things I'll find as elements.
;;
So if we want to define e.g. the identity function not directly in Clojure but
this time in LaTTe (which is also Clojure by the way), we will have to add some type annotations.
;;
In LaTTe, `lambda` is called `lambda`, or `λ`, rather than `fn`. In this part of the tutorial
we will rather use the beautiful `λ` rather than its ascii spelling. This is to emphasis
that we are not yet at the user-level of the proof assistant, we only play with its λ-calculus kernel.
;;
Thus our starting point is this:
;;
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
;;
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
;;
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
;;
The value returned by the `term` form (technically a Clojure macro) is the internal
representation of the terms in LaTTe. It's almost like what is written except that
the type of types is written `✳` internally.
Note also that if we use the ascii `lambda` we get the same result:


```clojure
(term
 (lambda [A :type] (lambda [x A] x)))
;; => (λ [A ✳] (λ [x A] x))

```
