{-# OPTIONS --cubical --safe --postfix-projections #-}

module Uni where

open import Cubical.Core.Everything renaming (Σ to Sg)

open import Cubical.Foundations.Prelude renaming (Σ to Sg)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function

open import Cubical.HITs.Interval

data U : Type₀
T : U → Type₀

data U where
  Π Σ : (a : U) (b : T a → U) → U
  pp : (a : Interval → U) → T (a zero) → T (a one) → U
  un : (a b : U) → T a ≃ T b → a ≡ b

T (Π a b) = (x : T a) → T (b x)
T (Σ a b) = Σ[ x ∈ T a ] (T (b x))
T (pp a x y) = PathP (λ i → T (a (seg i))) x y
T (un a b e i) = Glue (T b) λ{ (i = i0) → T a , e ; (i = i1) → T b , idEquiv (T b) }
