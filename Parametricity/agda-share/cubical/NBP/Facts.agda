
module NBP.Facts where

open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Relation.Nullary

variable
  ℓ₁ ℓ₂ ℓ₃ : Level

congS₂ : ∀{A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃}
       → {w x : A} {y z : B}
       → (f : A → B → C) (p : w ≡ x) (q : y ≡ z)
       → f w y ≡ f x z
congS₂ f p q = cong₂ f p q

record IdentityCode (A : Type ℓ₁) ℓ₂ : Type (ℓ-max ℓ₁ (ℓ-suc ℓ₂)) where
  field
    Code : A → A → Type
    isProp-Code : ∀ x y → isProp (Code x y)
    reflexive : ∀ x → Code x x
    decode : ∀ x y → Code x y → x ≡ y

open IdentityCode ⦃ ... ⦄ public

IdentityCode→isSet
  : ∀{A : Type ℓ₁} → ⦃ IdentityCode A ℓ₂ ⦄ → isSet A
IdentityCode→isSet = HSeparated→isSet λ x y →
  decode x y ∘ rec (isProp-Code x y) λ p →
    subst (Code x) p (reflexive x)
