
module Newtype where

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

foldℕ : ∀{r : Set} → ℕ → (r → r) → r → r
foldℕ zero    s z = z
foldℕ (suc n) s z = s (foldℕ n s z)

abstract
  Notℕ : Set
  Notℕ = ℕ

  toNotℕ : ℕ → Notℕ
  toNotℕ n = n

  fromNotℕ : Notℕ → ℕ
  fromNotℕ n = n

{-

-- Type mismatch
-- when checking that the pattern zero has type Notℕ

foldNotℕ : ∀{r : Set} → Notℕ → (r → r) → r → r
foldNotℕ zero    s z = z
foldNotℕ (suc n) s z = s (foldNotℕ n s z)
-}

{-

-- Notℕ !=< ℕ of type Set
-- when checking that the expression n has type ℕ

foldNotℕ : ∀{r : Set} → Notℕ → (r → r) → r → r
foldNotℕ n = foldℕ n

-}

foldNotℕ : ∀{r : Set} → Notℕ → (r → r) → r → r
foldNotℕ n = foldℕ (fromNotℕ n)