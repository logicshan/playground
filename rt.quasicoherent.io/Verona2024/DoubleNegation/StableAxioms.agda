{-# OPTIONS --allow-unsolved-metas #-}
module Verona2024.DoubleNegation.StableAxioms where

open import Verona2024.Basics.Common hiding (ℕ; zero; succ)

-- Here we postulate the PA axioms as truths, and then use these below to establish
-- the truth of the translated statements.
--
-- More accurately, we should instead define an Agda datatype of PA and HA proofs:
-- With the setup in this file, we could cheat by employing advanced Agda features
-- in the proofs of the translated statements (like universes and universe polymorphism).
postulate
  ℕ : Set

  zero : ℕ
  succ : ℕ → ℕ
  _+_  : ℕ → ℕ → ℕ
  _·_  : ℕ → ℕ → ℕ

  add-zero       : (x   : ℕ)     → (x + zero) ≡ x
  add-succ       : (x y : ℕ)     → (x + succ y) ≡ succ (x + y)
  mult-zero      : (x   : ℕ)     → (x · zero) ≡ zero
  mult-succ      : (x y : ℕ)     → (x · succ y) ≡ ((x · y) + y)
  succ-not-zero  : (x   : ℕ)     → ¬ (succ x ≡ zero)
  succ-injective : (x y : ℕ)     → succ x ≡ succ y → x ≡ y
  zero-or-succ   : (x   : ℕ)     → x ≡ zero ∨ Σ[ y ∈ ℕ ] x ≡ succ y
  induction      : (P : ℕ → Set) → P zero → ((n : ℕ) → P n → P (succ n)) → ((n : ℕ) → P n)

return : {X : Set} → X → ¬ ¬ X
return x = {!!}

add-zero' : (x : ℕ) → ¬ ¬ ((x + zero) ≡ x)
add-zero' x = {!!}

-- Add more translations and their proofs here.
