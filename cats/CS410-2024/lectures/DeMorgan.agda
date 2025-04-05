{-# OPTIONS --cubical #-}

module DeMorgan where

open import Cubical.Foundations.Prelude hiding (_∧_; _∨_; comp)
open import Agda.Primitive
open import Cubical.Data.Fin using (Fin)
open import Cubical.Data.Nat using (ℕ)
open import Function renaming (id to id')
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Foundations.HLevels using (isSet→)
open import Cubical.Data.Fin.Properties using (isSetFin)

variable
  ℓ ℓ' : Level
  A B C : Set ℓ

data FreeDM {ℓ} (A : Set ℓ) : Set ℓ where
  var   : A → FreeDM A
  𝟎     : FreeDM A
  𝟏     : FreeDM A
  _∧_   : FreeDM A → FreeDM A → FreeDM A
  _∨_   : FreeDM A → FreeDM A → FreeDM A
  ¬_    : FreeDM A → FreeDM A

  -- Lattice laws as paths
  ∧-comm    : ∀ x y → x ∧ y ≡ y ∧ x
  ∧-assoc   : ∀ x y z → x ∧ (y ∧ z) ≡ (x ∧ y) ∧ z
  ∨-comm    : ∀ x y → x ∨ y ≡ y ∨ x
  ∨-assoc   : ∀ x y z → x ∨ (y ∨ z) ≡ (x ∨ y) ∨ z
  ∧-absorb  : ∀ x y → x ∧ (x ∨ y) ≡ x
  ∨-absorb  : ∀ x y → x ∨ (x ∧ y) ≡ x

  -- Bounded lattice laws
  ∧-identity : ∀ x → (x ∧ 𝟏) ≡ x
  ∨-identity : ∀ x → (x ∨ 𝟎) ≡ x

  -- De Morgan laws
  involution : ∀ x → (¬ (¬ x)) ≡ x
  deMorgan-∧ : ∀ x y → ¬ (x ∧ y) ≡ (¬ x) ∨ (¬ y)
  deMorgan-∨ : ∀ x y → ¬ (x ∨ y) ≡ (¬ x) ∧ (¬ y)

  squash : (x y : FreeDM A) → (p q : x ≡ y) → p ≡ q

module _ where
  open Category

  FinSet : Category lzero lzero
  ob FinSet = ℕ
  Hom[_,_] FinSet n m = Fin n → Fin m
  id FinSet = id'
  _⋆_ FinSet f g = λ x → g (f x)
  ⋆IdL FinSet f = funExt λ x i → f x
  ⋆IdR FinSet f = funExt λ x i → f x
  ⋆Assoc FinSet f g h = λ i x → h (g (f x))
  isSetHom FinSet = isSet→ isSetFin

module _ where
  open Category

  SET : Category lzero lzero
  ob SET = {!Set!}
  Hom[_,_] SET = {!!}
  id SET = {!!}
  _⋆_ SET = {!!}
  ⋆IdL SET = {!!}
  ⋆IdR SET = {!!}
  ⋆Assoc SET = {!!}
  isSetHom SET = {!!}
