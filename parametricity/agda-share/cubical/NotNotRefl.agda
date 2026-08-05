
module NotNotRefl where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Empty
open import Cubical.Data.Unit

data Bool : Type where
  false true : Bool

not : Bool → Bool
not false = true
not true  = false

not-not : ∀ b → not (not b) ≡ b
not-not false = refl
not-not true  = refl

twist : Bool ≡ Bool
twist = isoToPath λ where
    .fun → not
    .inv → not
    .rightInv → not-not
    .leftInv  → not-not
  where open Iso

false≢true : false ≡ true → ⊥
false≢true p = subst P p _
  where
  P : Bool → Type
  P false = Unit
  P true  = ⊥

lemma : refl ≡ twist → ⊥
lemma p = false≢true false≡true
  where
  -- `transport refl false` computes to `false`
  -- `transport twist false` computes to `true`
  -- So `transport refl false ≡ transport twist false`
  --   computes to `false ≡ true`
  false≡true : false ≡ true
  false≡true = cong (λ q → transport q false) p
