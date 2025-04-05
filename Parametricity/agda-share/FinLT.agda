
module FinLT where

-- Representing finite set with sigma and inequality proofs

data Σ (A : Set) (P : A → Set) : Set where
  _,_ : (x : A) (w : P x) → Σ A P

data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ    #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}

data _≤_ : ℕ → ℕ → Set where
  zero : ∀{j}   → 0 ≤ j
  suc  : ∀{i j} → i ≤ j → suc i ≤ suc j

_<_ : ℕ → ℕ → Set
i < j = suc i ≤ j

<-dec : (i j : ℕ) → (i < j) ⊎ (j ≤ i)
<-dec i       zero    = inr zero
<-dec zero    (suc j) = inl (suc zero)
<-dec (suc i) (suc j) with <-dec i j
... | inl i<j = inl (suc i<j)
... | inr j≤i = inr (suc j≤i)

<-step : ∀{i j} → i < j → i < suc j
<-step (suc zero)      = suc zero
<-step (suc (suc i<j)) = suc (<-step (suc i<j))

Fin : ℕ → Set
Fin k = Σ ℕ λ i → i < k

fzero : ∀{k} → Fin (suc k)
fzero = (0 , suc zero)

fsuc : ∀{k} → Fin k → Fin (suc k)
fsuc (i , i<k) = (suc i , suc i<k)

-- modular arithmetic
msuc : ∀{k} → Fin k → Fin k
msuc {zero}  (_ , ())
msuc {suc k} (i , _) with <-dec (suc i) (suc k)
... | inl si<sk = (suc i , si<sk)
... | inr _     = fzero

_+_ : ∀{k} → Fin k → Fin k → Fin k
(zero  , _)       + j = j
(suc i , suc i<k) + j = msuc ((i , <-step i<k) + j)

_*_ : ∀{k} → Fin k → Fin k → Fin k
_*_ {zero}  (_ , ())          _
_*_ {suc k} (zero , _)        _ = fzero
_*_ {suc k} (suc i , suc i<k) j = j + ((i , <-step i<k) * j)

_^_ : ∀{k} → Fin k → ℕ → Fin k
_^_ {zero}  (_ , ()) _
_^_ {suc k} b        zero    = msuc (fzero)
_^_ {suc k} b        (suc e) = b * (b ^ e)
