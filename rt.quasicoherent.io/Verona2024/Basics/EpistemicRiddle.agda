{-# OPTIONS --allow-unsolved-metas #-}
module Verona2024.Basics.EpistemicRiddle where

open import Verona2024.Basics.Common

postulate
  ℝ : Set

  _+_ : ℝ → ℝ → ℝ
  _-_ : ℝ → ℝ → ℝ
  _*_ : ℝ → ℝ → ℝ

  Algebraic : ℝ → Set

  sum-algebraic     : {x y : ℝ} → Algebraic x → Algebraic y → Algebraic (x + y)
  product-algebraic : {x y : ℝ} → Algebraic x → Algebraic y → Algebraic (x * y)

  two     : ℝ
  onehalf : ℝ
  π       : ℝ
  e       : ℝ

  eq₁ : (x y : ℝ) → ((x + y) + (x - y)) ≡ (two * x)
  eq₂ : (x : ℝ) → (onehalf * (two * x)) ≡ x

Transcendental : ℝ → Set
Transcendental x = ¬ Algebraic x

postulate
  onehalf-algebraic : Algebraic onehalf
  pi-transcendental : Transcendental π
  e-transcendental  : Transcendental e

theorem₁ : ¬ (Algebraic (e + π) ∧ Algebraic (e - π))
theorem₁ (p , q) = e-transcendental e-algebraic
  where
  helper₁ : ((e + π) + (e - π)) ≡ (two * e)
  helper₁ = eq₁ e π
  helper₂ : (onehalf * (two * e)) ≡ e
  helper₂ = eq₂ e
  helper₃ : Algebraic (two * e)
  helper₃ = subst Algebraic helper₁ (sum-algebraic p q)
  helper₄ : Algebraic (onehalf * (two * e))
  helper₄ = product-algebraic onehalf-algebraic helper₃
  e-algebraic : Algebraic e
  e-algebraic = subst Algebraic helper₂ helper₄
  

-- Additional postulates are required for this; determine which ones!
theorem₂ : ¬ (Algebraic (e + π) ∧ Algebraic (e * π))
theorem₂ (p , q) = {!!}

-- The exercise specifically asked us to conclude with classical logic;
-- so we postulate the relevant law:
postulate
  de-morgan : {A B : Set} → ¬ (A ∧ B) → ¬ A ∨ ¬ B

theorem₁' : Transcendental (e + π) ∨ Transcendental (e - π)
theorem₁' = de-morgan theorem₁

theorem₂' : Transcendental (e + π) ∨ Transcendental (e * π)
theorem₂' = de-morgan theorem₂
