;;{
;; # More logic bits
;;
;; Logic is  not just about propositional operators like `and`, `or`, etc.
;; In this part of the tutorial, we'll see three other important logical
;; concepts: (various forms of) *equality*, the *existential* quantifier,
;; and finally we'll talk about the perhaps slightly less famous but
;; highly important concept of a *definite description*, also known
;; as the "iota" (ι) quantifier.
;;}

(ns latte-tutorial.ch06-more-logic
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
            ))

;;{
;; # 
;;}
