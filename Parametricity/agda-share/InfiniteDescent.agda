
module InfiniteDescent where

open import Data.Nat
open import Data.Nat.Induction
open import Data.Product
open import Function
open import Relation.Nullary

infinite-descent
  : (P : ℕ -> Set)
  → (∀ n → P n -> ∃[ m ] m < n × P m)
  → ∀ n → ¬ P n
infinite-descent P pre =
  -- Prove ¬ P n by well-founded induction along _<_
  <-rec (λ n → ¬ P n) λ n rec Pn →
    case pre n Pn of λ where
      (m , m<n , Pm) → rec m<n Pm
