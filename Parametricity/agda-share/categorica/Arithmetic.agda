
module Arithmetic where

open import Equality

module Natural where
  data ℕ : Set where
    zero : ℕ
    suc  : ℕ → ℕ

  {-# BUILTIN NATURAL ℕ    #-}
  {-# BUILTIN ZERO    zero #-}
  {-# BUILTIN SUC     suc  #-}

  _+_ : ℕ → ℕ → ℕ
  0     + n = n
  suc m + n = suc (m + n)

module Finite where
  open Natural

  data Fin : ℕ → Set where
    zero : ∀{n} → Fin (1 + n)
    suc  : ∀{n} → Fin n → Fin (1 + n)

  data _≤_ : {n : ℕ} → Fin n → Fin n → Set where
    z≤ : ∀{n} {i : Fin (1 + n)} → _≤_ {1 + n} zero i
    s≤ : ∀{n} {i j : Fin n} → (i≤j : _≤_ {n} i j) → _≤_ {1 + n} (suc i) (suc j)

  ≤-refl : ∀{n} {i : Fin n} → i ≤ i
  ≤-refl {i = zero}  = z≤
  ≤-refl {i = suc i} = s≤ ≤-refl

  ≤-trans : ∀{n} {i j k : Fin n} → i ≤ j → j ≤ k → i ≤ k
  ≤-trans z≤       j≤k      = z≤
  ≤-trans (s≤ i≤j) (s≤ j≤k) = s≤ (≤-trans i≤j j≤k)

  ≤-unique : ∀{n} {i j : Fin n} (pf₁ pf₂ : i ≤ j) → pf₁ ≡ pf₂
  ≤-unique z≤         z≤  = refl
  ≤-unique (s≤ i≤j)   (s≤ i≤j') with ≤-unique i≤j i≤j'
  ≤-unique (s≤ .i≤j') (s≤ i≤j') | refl = refl
  


