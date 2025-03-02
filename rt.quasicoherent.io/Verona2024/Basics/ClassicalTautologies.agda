{-# OPTIONS --allow-unsolved-metas #-}

module Verona2024.Basics.ClassicalTautologies where

open import Verona2024.Basics.Common

module _ (A B : Set) where
  a : ¬ (A ∨ B) → ¬ A ∧ ¬ B
  a = λ z → (λ z₁ → z (left z₁)) , (λ z₁ → z (right z₁))

  b : ¬ (A ∧ B) → ¬ A ∨ ¬ B
  b = {!!}

  c : (A → B) → ¬ A ∨ B
  c = {!!}

  d : ((A ∨ B) ∧ ¬ A) → B
  d = {!!}

e : (n : ℕ) → n ≡ zero ∨ ¬ (n ≡ zero)
e zero = left refl
e (succ n) = right λ ()

j : (f : ℕ → Bool) → ¬ ¬ (Σ[ n ∈ ℕ ] f n ≡ false) → Σ[ n ∈ ℕ ] f n ≡ false
j = {!!}

k : (f : ℕ → Bool) → Σ[ n ∈ ℕ ] (f n ≡ true → ((m : ℕ) → f m ≡ true))
k = {!!}

l : (f : ℕ → Bool) → (Σ[ n ∈ ℕ ] f n ≡ false) ∨ ((n : ℕ) → f n ≡ true)
l = {!!}
