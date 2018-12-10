

# Introduction


```clojure
(ns latte-tutorial.ch00-front-matter)

```

((((
((((
))))             or
_ .---.                Curry     
( |`---'|                    Howard
\|     |                       without the fuss
: .___, :
`-----'  -Karl



## About this document

This document is a tutorial introduction to the LaTTe proof assistant.

Here are the primary goals:
- a quick startup guide to LaTTe
- a pedagogical overview of its main features
- a first experiment with important proof rules

The main non-goals are:
- a complete course about e.g. type theory or logic, or whatever
- an exhaustive manual for the proof assistant
- a maths lecture

So I'll go straight-to-the-point, often omitting (probably) important
aspects.

The tutorial is heavily inspired by the talk about LaTTe that I gave
at EuroClojure'2016, cf. https://www.youtube.com/watch?v=5YTCY7wm0Nw
... note that LaTTe changed a lot since the talk. But it is still an
interesting experience of "live coding mathematics".

Note that this is a *literate programming* document, which means it is
both a textual document with Clojure (and LaTTe) code examples, and also
a set of heavy commented Clojure source files that can be compiled, executed,
tested, etc.

For each namespace `nsp` (in the Clojure terminology), you'll find :
- one file `nsp.clj` containing the Clojure **code source view** with all the explanations
(e.g. this very sentence) as comments
- a corresponding file `nsp.clj.md` containing the **document view** as a markdown
text with all the source code.

For example, the following line is an expression of the Clojure language that
can be evaluated directly when loading the code source view


```clojure
((fn [x] x) 42)
;; => 42

```

For many examples the expected evaluation results is show as a `=> <value>` comment.

**Remark**: The translation of the code source view to the document view is handled
by a very simple *Markownize* tool that you can find at: https://github.com/fredokun/markdownize

Also, there are a few exercises and questions in the `master` branch of the tutorial.
The solutions are available in the `solution' branch (which should be at least one commit beyond `master`).




## Author

I think it is good to introduce oneself when talking to other people.

My name is Frederic Peschanski, I am associated professor in computer science
at Sorbonne University in Paris, France. I do research mostly on the theoretical
sides, but my main hobby is programming thus I try sometimes to mix the work and pleasure.

On my spare time I develop largely experimental free (as in freedom) software,
and for a few of them I do get some users which thus involves some maintenance.

You can reach me professionally at the following address:
`frederic.peschanski@lip6.fr`.  I will be happy to answer
but don't mind to much if it takes some time.



## Acknowledgments

I developed LaTTe after reading (devouring, more so) the following book:

**Type Theory and Formal Proof: an Introduction**
- Rob Nederpelt and Herman Geuvers
- Cambridge University Press, 2012

__...--~~~~~-._   _.-~~~~~--...__
//               `V'               \\ 
//                 |                 \\ 
//__...--~~~~~~-._  |  _.-~~~~~~--...__\\ 
//__.....----~~~~._\ | /_.~~~~----.....__\\
====================\\|//====================
dwb `---`  

That's a heavily recommended lecture, but it's not a prerequisite
for learning and using LaTTe (only a very nice complement).

I would also like to thank Yeonathan Sharvit and Hiram Madelaine as well as
the (few) contributors to LaTTE. And of course "big five" to the Clojure core
dev. team and all the community.

## About LaTTe

**LaTTe** stands for "Laboratory for Type Theory Experiments" but it
is in fact a perfectly usable **proof assistant** for doing formal mathematics
and logic on a computer. It's far from being the most advanced proof assistance
technology but it still provides some interesting features.

**Remark**: The double *TT* of LaTTe is also looking like
Π the Greek capital letter Pi, which is one of the very few
constructors of the type theory used by LaTTe, a very simple dependently typed
lambda-calculus. This will be explained, at least superficially, in the tutorial.

The basic activity of a proof assistant user is to:
- write **definitions** of mathematical concepts (e.g. what it is to be a bijection)
- state properties about these concepts based on their definitions, in the form of **axioms** and (yet unproven) **theorems** (or lemmas)
- and for each theorem, help in writing a **formal proof** that it indeed holds

So it's of no surprise that these are the main features of LaTTe.
But it is also a library for the Clojure programming language, which is unlike
many other proof assistants designed as standalone tools (one exception being the
members of the HOL family, another important source of inspiration).
Thanks to the power of the Lisp language in general,
and its Clojure variant in particular, all the main features of the proof assistant
are usable directly in Clojure programs or at the REPL (Read-Eval-Print-Loop).

Also this means that any Clojure development environment (e.g. Cider, Cursive) can
be used as a proof assistant GUI. And this is where most of the power of LaTTe lies.
Indeed, the Clojure IDEs support very advanced interactive features. Moreover, one can
extend the assistant directly in Clojure and without any intermediate such as a
plugins system or complex API. We'll see, however, that there are a few places where
writing Clojure code is required in LaTTe in particular to write *implicits*.

Moreover, the mathematical contents developed using LaTTe can be distributed
using the very powerful Clojure ecosystem based on the Maven packaging tool.
Also, there is a simple yet effective *proof certification* scheme that
corresponds to a form of compilation for the distributed content.
Proving things in type theory can become rather computationally intensive,
but a certified proof can be "taken for granted".
In fact, you develop mathematics in Clojure *exactly like* you develop programs
in general, there's not difference at all!

Last but not least, the main innovative feature of LaTTe is its *declarative proof language*,
which makes the proofs follow the *natural deduction* style, which means that LaTTe proofs
really look like standard mathematical proofs, at least strucutrally, and of course if you're
able to cope with the Clojure-enhanced Lisp notation. There aren't just parentheses (but there's
still a bunch of them).




## Intended audience

You might be interested in LaTTe because as a Clojure developer you are curious
about type theory, the lambda-calculus with dependent types, the Curry-Howard correspondance,
or simply formal logic and mathematics.

You might also be interested in LaTTe to develop some formal mathematical contents, based on
an approach that is not exactly like other proof assistants. I very much welcome mathematical
contributions to the project!

Finally, you might be intersted in how one may embed a *domain-specific language*, the
Lisp way in Clojure (thus with an extra-layer of data-orientation). Clojure the language
is still there when using Clojure, but you're doing not only programming but also
mathematics and reasoning... The *same* difference, the Lisp way...

Or maybe you're here and that's it!

In any case you are very **Welcome**!




## Prerequisites

Since LaTTe is a Clojure library, it is required to know at least a bit of
Clojure and one of its development environment to follow this tutorial.
LaTTe works pretty well in Cider or Cursive, or simply with a basic editor
and the REPL.

Note that beyond basic functional programming principles, there's nothing much to
learn on the Clojure side. Still, if you don't know Clojure  I can only recommend
to read the first few chapters of an introductory Clojure book.
I don't want to give any specific recommendation since most of the introductory
books I've read are quite good ...




## Tutorial plan

The following steps should be followed in order:

1. first steps (install & friends)
2. the rules of the game (a.k.a. lambda, forall and friends)
3. a bit of logic: natural deduction
4. a glimpse of (typed) set theory
5. a sip of integer arithmetics
6. proving in the large: from proof certification to Clojars deploy



```clojure
(println "Let's begin!")
;; => nil
```
