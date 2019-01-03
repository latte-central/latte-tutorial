
# Chapter 1 : first steps


```clojure
(ns latte-tutorial.ch01-first-steps)

```

In this short chapter I will quickly explain how to
install LaTTe and start to work with it.

If you are a seasoned Clojure programmer, there is
in fact nothing that distinguishes the installation
of LaTTe and the installation of any leiningen-powered
Clojure library.

Other build tools, such as boot or deps, could be used
but I am personally enjoying working with leiningen and
find it also a fantastic build tool for mathematical
developments !




## Step 1: the project structure

I will take the current `latte-tutorial` project as an example.
I have created the basic directory structure with leiningen, using
something like the following:

```
$ lein new app latte-tutorial
```
(note that the `$` symbol represents the Shell prompt)

I use the `app` template because as you'll see in the final chapter
we will write a `main` function in the final chapter of the tutorial.

After some cleanup I get a `latte-tutorial/` root directory
with the following contents:
- `project.clj` the leiningen project file
- `src/latte_tutorial/` the source files (`.clj` or `.clj.md` extensions)
- `LICENSE`, `README.md` some auxiliary files




## Step 2: the project files

As for any leiningen the `project.clj` file contains the
build informations of our project, in particular its dependencies.

At the time of writing the document, the file contains the following
informations:

```clojure
(defproject latte-tutorial "0.1.0-SNAPSHOT"
  :description "A gentle introduction to the LaTTe proof assistant."
  :url "https://github.com/latte-central/latte-tutorial"
  :license {:name "MIT License"
            :url "http://opensource.org/licenses/MIT"}
  :dependencies [[org.clojure/clojure "1.10.0"]
                 [latte "1.0b2"]
                 [latte-prelude "1.0b2"]
                 [latte-sets "1.0b2"]
                 [latte-integers "1.0b2"]])
```
The `:dependencies` key is most interesting.
We first require the Clojure implementation itself, of course.
And our LaTTe dependencies are as follows:
- The core `latte` implementation, which provides the main user interface
  of the proof assistant. It itself depends on the `latte-kernel` project which
  implements the type theory used in LaTTe
- the `latte-prelude` standard library, which provides the fundamental reasoning
tools such as propositional operators, equality, quantifiers, etc.
- the `latte-sets` library of (typed) set theory, which we will use in the tutorial
- the `latte-integers` arithmetic library, which we will also discuss

To be sure that everything's fine regarding the dependencies, you might try the
following on the command line:

```
$ lein deps
```

In case there is a problem with the dependencies, some error message will be
printed out. Otherwise, if nothing happens, you're good to go!



## Step 3: coding mathematics

In this final step, we begin our work with LaTTe. As for any Clojure program
we simply have to create a namespace source file with the `.clj` extension
and start coding.

We will proceed to the file `src.latte_tutorial.ch02_game_rules.clj` corresponding
to the namespace `latte-tutorial.ch02-game-rules` in which we'll start coding
mathematics.

Please proceed ...

