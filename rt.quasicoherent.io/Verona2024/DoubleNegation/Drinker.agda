{-# OPTIONS --allow-unsolved-metas #-}
module Verona2024.DoubleNegation.Drinker where

open import Verona2024.Basics.Common

drinker : (f : ℕ → Bool) → ¬ ¬ (Σ[ n ∈ ℕ ] (f n ≡ true → ((m : ℕ) → ¬ ¬ (f m ≡ true))))
drinker f = {!!}
