{-# OPTIONS --universe-polymorphism #-}

-- Propositional equality, with extensionality!

module Equality where

open import Basics

data _≡_ {i} {A : Set i} (x : A) : A → Set i where
  refl : x ≡ x

symm : ∀{i} {A : Set i} {x y : A} → x ≡ y → y ≡ x
symm refl = refl

trans : ∀{i} {A : Set i} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

postulate
  ext : ∀{i j} {A : Set i} {B : Set j} {f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g

subst : ∀{i j} {A : Set i} (P : A → Set j) {x y} → x ≡ y → P x → P y
subst P refl Px = Px

cong : ∀{i j} {A : Set i} {B : Set j} (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

K : ∀{i} {A : Set i} {x : A} (p : x ≡ x) → p ≡ refl
K refl = refl


-- Equational reasoning from the std-lib

module Reasoning {i} (A : Set i) where
  infix  40 _IsRelatedTo_
  infix  20 _∎
  infixr 20 _≡⟨_⟩_
  infix  10 begin_

  data _IsRelatedTo_ (x y : A) : Set i where
    relTo : (x≡y : x ≡ y) → x IsRelatedTo y

  begin_ : ∀{x y} → x IsRelatedTo y → x ≡ y
  begin relTo x≡y = x≡y

  _≡⟨_⟩_ : ∀ x {y z} → x ≡ y → y IsRelatedTo z → x IsRelatedTo z
  _ ≡⟨ x≡y ⟩ relTo y≡z = relTo (trans x≡y y≡z)

  _∎ : ∀ x → x IsRelatedTo x
  _ ∎ = relTo refl