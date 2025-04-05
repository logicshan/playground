{-# OPTIONS --cubical --safe --postfix-projections #-}

module Glued where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Int
open import Cubical.HITs.Ints.BiInvInt

variable
  ℓ : Level
  A B : Type ℓ

Glued : {C : I → Type ℓ} → A ≃ C i0 → B ≃ C i1 → A ≡ B
Glued {A = A} {B = B} {C = C} eq₁ eq₂ i
  = Glue (C i) λ{ (i = i0) → A , eq₁ ; (i = i1) → B , eq₂ }

glued
  : {C : I → Type ℓ}
  → {eq₁ : A ≃ C i0} {eq₂ : B ≃ C i1}
  → (x : A) (y : B)
  → PathP C (eq₁ .fst x) (eq₂ .fst y)
  → PathP (λ i → Glued {C = C} eq₁ eq₂ i) x y
glued x y z i = glue (λ{ (i = i0) → x ; (i = i1) → y }) (z i)

unglued
  : {C : I → Type ℓ}
  → {eq₁ : A ≃ C i0} {eq₂ : B ≃ C i1}
  → {x : A} {y : B}
  → PathP (λ i → Glued {C = C} eq₁ eq₂ i) x y
  → PathP C (eq₁ .fst x) (eq₂ .fst y)
unglued p i = unglue (i ∨ ~ i) (p i)

Ints : Int ≃ BiInvInt
Ints = isoToEquiv (iso fwd bwd fwd-bwd bwd-fwd)

GInts : I → Type₀
GInts = λ i → Glue BiInvInt λ{ (i = i0) → Int , Ints ; (i = i1) → BiInvInt , idEquiv BiInvInt }

apInts : Int → BiInvInt
apInts = transp GInts i0

gInts : ∀ n → PathP GInts n (fwd n)
gInts n i = glue (λ{ (i = i0) → n ; (i = i1) → fwd n }) (fwd n)

