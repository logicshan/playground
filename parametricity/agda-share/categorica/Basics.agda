{-# OPTIONS --universe-polymorphism #-}

module Basics where

data Level : Set where
  zero : Level
  suc  : Level → Level
{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO zero  #-}
{-# BUILTIN LEVELSUC  suc   #-}

infixl 60 _⊔_
_⊔_ : Level → Level → Level
zero  ⊔ n     = n
suc m ⊔ zero  = suc m
suc m ⊔ suc n = suc (m ⊔ n)
{-# BUILTIN LEVELMAX _⊔_ #-}

data _⊎_ {i j} (A  : Set i) (B : Set j) : Set (i ⊔ j) where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

infixr 40 _,_
data Σ {i j} (A : Set i) (P : A → Set j) : Set (i ⊔ j) where
  _,_ : (x : A) (w : P x) → Σ A P

