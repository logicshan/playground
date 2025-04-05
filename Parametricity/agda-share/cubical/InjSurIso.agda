{-# OPTIONS --postfix-projections #-}

module InjSurIso where

open import Cubical.Core.Everything

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation

variable
  ℓ : Level
  A B : Type ℓ

-- f is injective
Inj : (A → B) → Type _
Inj f = ∀ x y → f x ≡ f y → x ≡ y

-- f is surjective
Sur : (A → B) → Type _
Sur f = ∀ b → ∥ fiber f b ∥₁

-- f has a section
Sec : (A → B) → Type _
Sec f = ∀ b → fiber f b

module Isom (Aset : isSet A) (Bset : isSet B) (f : A → B) (inj : Inj f) (sur : Sur f) where
  propFiber : ∀{b} → isProp (fiber f b)
  propFiber (x , p) (y , q)
    = ΣPathP ((inj x y (p ∙ sym q)) , (isSet→isSet' Bset _ _ _ _))

  sec : Sec f
  sec = rec propFiber (idfun _) ∘ sur

  g : B → A
  g = fst ∘ sec

  fib : ∀ x → fiber f (f x)
  fib x = (x , refl)

  inv₁ : g ∘ f ≡ idfun _
  inv₁ i a = propFiber (sec (f a)) (fib a) i .fst

  inv₂ : f ∘ g ≡ idfun _
  inv₂ i b = sec b .snd i
