{-# OPTIONS --two-level #-}

open import Data.Nat

data ℕˢ : SSet where  
  zeroˢ : ℕˢ  
  sucˢ : ℕˢ → ℕˢ  
ℕˢ-to-ℕ : ℕˢ → ℕ  
ℕˢ-to-ℕ zeroˢ = zero  
ℕˢ-to-ℕ (sucˢ n) = suc (ℕˢ-to-ℕ n)  
