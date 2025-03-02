{-# OPTIONS --allow-unsolved-metas #-}

module Verona2024.Basics.Negation where

open import Verona2024.Basics.Common

module _ (A : Set) where
  a : A → ¬ ¬ A
  a = λ z z₁ → z₁ z

  b₁ : ¬ ¬ ¬ A → ¬ A
  b₁ = λ z z₁ → z (λ z₂ → z₂ z₁)

  b₂ : ¬ A → ¬ ¬ ¬ A
  b₂ = λ z z₁ → z₁ z

  c : ¬ ¬ (A ∨ ¬ A)
  c = λ z → z (right (λ z₁ → z (left z₁)))

module _ (A B : Set) where
  d₁ : ¬ ¬ (A ∧ B) → ¬ ¬ A ∧ ¬ ¬ B
  d₁ ¬¬A∧B = {!!}

  d₂ : ¬ ¬ A ∧ ¬ ¬ B → ¬ ¬ (A ∧ B)
  d₂ (p , q) = {!!}
