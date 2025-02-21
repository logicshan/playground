module Verona2024.DoubleNegation.Maximum where

open import Data.Nat
open import Data.Product
open import Data.Sum

module _ (⊥ : Set) where
  ¬_ : Set → Set
  ¬ X = X → ⊥

  return : {X : Set} → X → ¬ ¬ X
  return x k = k x

  _⟫=_ : {X Y : Set} → ¬ ¬ X → (X → ¬ ¬ Y) → ¬ ¬ Y
  m ⟫= f = λ k → m (λ x → f x k)

  {-# TERMINATING #-}
  maximum : ¬ ¬ (Σ[ n ∈ ℕ ] ((m : ℕ) → ¬ ¬ (n ≥ m)))
  maximum = go 0
    where
    go : ℕ → ¬ ¬ (Σ[ n ∈ ℕ ] ((m : ℕ) → ¬ ¬ (n ≥ m)))
    go n k = k (n , h)
      where
      h : (m : ℕ) → ¬ ¬ (n ≥ m)
      h m with ≤-<-connex m n
      ... | inj₁ m≤n = return m≤n
      ... | inj₂ n<m = λ k' → go m k

  absurd : ¬ ¬ (Σ[ n ∈ ℕ ] n ≥ suc n)
  absurd = maximum ⟫= λ (n , h) → h (suc n) ⟫= λ n≥sucn → return (n , n≥sucn) 
