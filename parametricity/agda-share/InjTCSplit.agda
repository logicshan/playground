{-# OPTIONS --injective-type-constructors #-}

module InjTCSplit  where

open import Level
open import Function
open import Data.Empty
open import Data.Unit
open import Relation.Binary.PropositionalEquality

variable
  ℓ : Level

module _
  (split : ∀{ℓ}{A B : Set ℓ} → (f : A → B) → (∀ x y → f x ≡ f y → x ≡ y) → B → A)
  (split! : ∀{ℓ}{A B : Set ℓ} (f : A → B) inj x → split f inj (f x) ≡ x)
  where

  data Lam (F : Set → Set) : Set where

  inj-Lam : ∀ F G → Lam F ≡ Lam G → F ≡ G
  inj-Lam _ _ refl = refl

  Ap : Set → Set → Set
  Ap F X = split Lam inj-Lam F X

  Y : (Set → Set) → Set
  Y F = Ω (Lam Ω)
    module Y where
    Ω : Set → Set
    Ω X = F (Ap X X)

  YF≡FYF : ∀ F → Y F ≡ F (Y F)
  YF≡FYF F = cong (λ G → F (G (Lam (Y.Ω F)))) (split! Lam inj-Lam (Y.Ω F))

  Bad : Set
  Bad = Y (λ X → X → ⊥)

  Bad≡ : Bad ≡ (Bad → ⊥)
  Bad≡ = YF≡FYF (λ X → X → ⊥)

  bad : ⊥
  bad = out (subst id (sym Bad≡) out) where
    out : Bad → ⊥
    out b = subst id Bad≡ b b
