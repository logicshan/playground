open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Data.Nat using (ℕ; zero; suc)
open import Function using (_∘_) renaming (id to id')
open import Data.Sum hiding ([_,_])
open import Relation.Binary.PropositionalEquality
open import Data.Fin using (Fin; zero; suc)

open import Categories.Category
open import Categories.Functor hiding (id)
open import Categories.Monad hiding (id)
open import Categories.Category.Construction.Kleisli
open import Categories.Category.Instance.Sets using (Sets)

module _ where

variable
  o ℓ e : Level

module _ where
  open Category

  FinSet : Category lzero lzero lzero
  Obj FinSet = ℕ
  _⇒_ FinSet n m = Fin n → Fin m
  _≈_ FinSet f g = ∀ x → f x ≡ g x
  id FinSet = λ z → z
  Category._∘_ FinSet = λ g f x → g (f x)
  assoc FinSet = λ x → refl
  sym-assoc FinSet = λ x → refl
  identityˡ FinSet = λ x → refl
  identityʳ FinSet = λ x → refl
  identity² FinSet = λ x → refl
  equiv FinSet = record
    { refl = λ {x} x₁ → refl
    ; sym = λ x x₁ → sym (x x₁)
    ; trans = λ x x₁ x₂ → trans (x x₂) (x₁ x₂) }
  ∘-resp-≈ FinSet {f = f} {h} {g} {i} = λ x x₁ x₂ → let open ≡-Reasoning in begin
    f (g x₂) ≡⟨ x (g x₂) ⟩ h (g x₂) ≡⟨ cong h (x₁ x₂) ⟩ h (i x₂) ∎

module _ where
  open Category
  open import FreeDeMorganAlgebra using (FreeDeMorgan; η; DM)

  K : Category _ lzero _
  K = Kleisli DM

  Kᵒᵖ : Category _ _ _
  Kᵒᵖ = op K

  DM⟦_⟧ : ∀ {o} → Obj (Sets o) → Obj (Sets o)
  DM⟦_⟧ = Functor.F₀ (Monad.F DM)
{-
  Hom[_,_] : ∀ {o} → Obj (Sets o) → Obj (Sets o) → Set o
  Hom[_,_] {o} = _⇒_ (Sets o)
-}
  Cube : Category lzero lzero lzero
  Obj Cube = ℕ
  _⇒_ Cube I J = Sets lzero [ Fin J , DM⟦ Fin I ⟧ ]
  _≈_ Cube f g = ∀ x → f x ≡ g x
  id Cube = η
  Category._∘_ Cube = Category._∘_ Kᵒᵖ
  assoc Cube {A} {B} {C} {D} {f} {g} {h} 
    = assoc Kᵒᵖ {A = Fin A} {B = Fin B} {C = Fin C} {D = Fin D} {f = f} {g = g} {h = h} 
  sym-assoc Cube {A} {B} {C} {D} {f} {g} {h} 
    = sym-assoc Kᵒᵖ {A = Fin A} {B = Fin B} {C = Fin C} {D = Fin D} {f = f} {g = g} {h = h} 
  identityˡ Cube = identityˡ Kᵒᵖ
  identityʳ Cube = identityʳ Kᵒᵖ
  identity² Cube = identity² Kᵒᵖ
  equiv Cube = equiv Kᵒᵖ
  ∘-resp-≈ Cube = ∘-resp-≈ Kᵒᵖ
