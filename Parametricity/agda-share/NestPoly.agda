{-# OPTIONS --universe-polymorphism #-}

module NestPoly where

data Level : Set where
  zero : Level
  suc  : Level → Level

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO zero  #-}
{-# BUILTIN LEVELSUC  suc   #-}

max : Level → Level → Level
max zero    n       = n
max (suc m) zero    = suc m
max (suc m) (suc n) = suc (max m n)
{-# BUILTIN LEVELMAX max #-}

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ    #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}

induction : ∀{i : Level} {P : ℕ → Set i}
          → (∀{m} → P m → P (suc m)) → P 0 → (n : ℕ) → P n
induction Ps Pz zero    = Pz
induction Ps Pz (suc n) = Ps {n} (induction (λ{m} → Ps {m}) Pz n)

nest : ∀{i : Level} {A : Set i} {F : Set i → Set i}
     → (n : ℕ) → (∀{A} → A → F A)
     → A → induction F A n
nest {i} {A} {F} n g x = induction {i} {induction F A} g x n
