
module DiaFun where

open import Function
open import Data.Empty
open import Data.Nat
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

-- No number is its own successor
lemma : ∀ m → ¬ m ≡ 1 + m
lemma zero () -- absurd, 0 ≢ 1
lemma (suc m) eq = lemma m peq
  where
  peq : m ≡ 1 + m
  peq = cong pred eq

-- A binary function `enum` is a covering if
IsCovering : (ℕ → ℕ → ℕ) → _
IsCovering enum =
  ∀(f : ℕ → ℕ) →       -- for all functions `f`
  Σ[ n ∈ ℕ ]           -- there is a number `n`
  ∀ m → enum n m ≡ f m -- `enum n` is extensionally equal to `f`

-- No functions are coverings
diagonal : (enum : ℕ → ℕ → ℕ) → ¬ IsCovering enum
diagonal enum cover
  = case cover g of λ{
      -- ext n : enum n n ≡ g n
      -- ext n : enum n n ≡ 1 + enum n n
      (n , ext) → lemma (enum n n) (ext n)
    }
  where
  g : ℕ → ℕ
  g m = 1 + enum m m
