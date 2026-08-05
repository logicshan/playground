{-# OPTIONS --irrelevant-projections #-}

module Irrelevant where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Bool
open import Cubical.HITs.S1

open import Cubical.Relation.Nullary

variable
  ℓ : Level
  A X : Type ℓ
  Y : X → Type ℓ

record Sq (A : Type ℓ) : Type ℓ where
  constructor sq
  field
    .value : A

open Sq

sqsh : ∀(x y : Sq A) → x ≡ y
sqsh x y = refl

F : S¹ → Type
F base = Bool
F (loop i) = notEq i

no-sect : ¬ (∀ x → F x)
no-sect f with f base | cong f loop
... | false | fl = true≢false (fromPathP fl)
... | true | fl = false≢true (fromPathP fl)

.choice : (∀ x → Sq (Y x)) → Sq (∀ x → Y x)
choice e = sq λ x → value (e x)

sq-sect : (x : S¹) → Sq (F x)
sq-sect base = sq true
sq-sect (loop i)
  = hcomp (λ where
        k (i = i0) → y
        k (i = i1) → sqsh y (sq true) k)
      y
  where
  y : Sq (notEq i)
  y = sq (transport (λ j → notEq (i ∧ j)) true)

.bad : ⊥
bad = no-sect (value (choice sq-sect))
