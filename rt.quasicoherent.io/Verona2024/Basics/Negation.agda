{-# OPTIONS --allow-unsolved-metas #-}

module Verona2024.Basics.Negation where

open import Verona2024.Basics.Common

module _ (A : Set) where
  a : A → ¬ ¬ A
  a = {!!}

  b₁ : ¬ ¬ ¬ A → ¬ A
  b₁ = {!!}

  b₂ : ¬ A → ¬ ¬ ¬ A
  b₂ = {!!}

  c : ¬ ¬ (A ∨ ¬ A)
  c = {!!}

module _ (A B : Set) where
  d₁ : ¬ ¬ (A ∧ B) → ¬ ¬ A ∧ ¬ ¬ B
  d₁ = {!!}

  d₂ : ¬ ¬ A ∧ ¬ ¬ B → ¬ ¬ (A ∧ B)
  d₂ = {!!}
