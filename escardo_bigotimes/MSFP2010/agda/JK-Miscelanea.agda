module JK-Miscelanea where

open import Logic
open import LogicalFacts
open import JK-Monads
open import Equality

-----------------------------------------------------------------------
-- Some properties of J and K that are interesting and some useful.  --
-----------------------------------------------------------------------

-- This can be seen as a generalization of J-functor (but its proof
-- uses J-functor):

J-gfunctor : {R : Ω} {X : Set} {A : X → Ω} → 
----------
          (∀(x : X) → A x) → J R X → J R (∃ \(x : X) → A x) 

J-gfunctor f = J-functor (λ x → ∃-intro x (f x))

-- This can be considered as a generalization of J-strength:

J-∃-shift : {R : Ω} {X : Set} {A : X → Ω} →
---------
             (∃ \(x : X) → J R (A x)) → J R (∃ \(x : X) → A x)

J-∃-shift {R} {X} {A} premise = δ
  where x : X
        x = ∃-witness premise

        ε : J R (A x)
        ε = ∃-elim premise

        f : A x → ∃ \(x : X) → A x
        f = ∃-intro x

        δ : J R (∃ \(x : X) → A x)
        δ = J-functor f ε

        observation : δ ≡ λ p → ∃-intro x (ε(λ a → p(∃-intro x a)))
        observation = reflexivity

-- This generalizes the dependent J-∧-shift (dependent product of selection functions):

J-blah : {R : Ω} {X : Set} {B : X → Ω} → 
------
              J R X ∧ (∀(x : X) → J R (B x)) → J R (∃ \(x : X) → B x)

J-blah (∧-intro ε f) = μJ(J-functor J-∃-shift (J-gfunctor f ε))


-- Unshifts:


J-∀-unshift : {R : Ω} {X : Set} {A : X → Ω} → 
-----------
              J R (∀(x : X) → A x) → ∀(x : X) → J R (A x)

J-∀-unshift ε x = J-functor (λ f → f x) ε


K-∀-unshift : {R : Ω} {X : Set} {A : X → Ω} → 
-----------
              K R (∀(x : X) → A x) → ∀(x : X) → K R (A x)

K-∀-unshift φ x = K-functor (λ f → f x) φ
