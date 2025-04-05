
module QuickSort where

open import Data.List
open import Data.List.Properties
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Induction
open import Induction.WellFounded

variable n : ℕ

before : ℕ -> List ℕ -> List ℕ
before p = filter (_≤? p)

after : ℕ -> List ℕ -> List ℕ
after p = filter (p <?_)

before< : ∀ p xs → length (before p xs) < length (p ∷ xs)
before< p xs = ≤-<-trans (length-filter (_≤? p) xs) ≤-refl

after< : ∀ p xs → length (after p xs) < length (p ∷ xs)
after< p xs = ≤-<-trans (length-filter (p <?_) xs) ≤-refl

quicksort₀ : (l : List ℕ) -> Acc _<_ (length l) -> List ℕ
quicksort₀ []       al        = []
quicksort₀ (p ∷ xs) (acc pre) = ls ++ p ∷ rs
  where
  ls = quicksort₀ (before p xs) (pre (before< p xs))
  rs = quicksort₀ (after  p xs) (pre (after<  p xs))

quicksort : List ℕ -> List ℕ
quicksort l = quicksort₀ l (<-wellFounded (length l))
