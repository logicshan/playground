{-# OPTIONS --allow-unsolved-metas #-}
module Verona2024.DoubleNegation.Drinker where

open import Verona2024.Basics.Common

drinker : (f : ℕ → Bool) → ¬ ¬ (Σ[ n ∈ ℕ ] (f n ≡ true → ((m : ℕ) → ¬ ¬ (f m ≡ true))))
drinker f = λ z → z (zero , (λ z₁ m z₂ → z (m , (λ z₃ m₁ z₄ → z₂ z₃))))
