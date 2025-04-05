
module AckInd0 where

open import Data.Nat

induction : (Q : ℕ -> Set) -> Q 0 -> (∀ n → Q n → Q (suc n)) -> (∀ n → Q n)
induction Q Qz Qs 0 = Qz
induction Q Qz Qs (suc n) = Qs n (induction Q Qz Qs n)

case : (Q : ℕ -> Set) -> Q 0 -> (∀ n → Q (suc n)) -> (∀ n → Q n)
case Q Qz Qs 0       = Qz
case Q Qz Qs (suc n) = Qs n

induction-01
  : (Q : ℕ -> Set)
  → Q 0
  → Q 1
  → (∀ n → Q (suc n) -> Q (suc (suc n)))
  → (∀ n → Q n)
induction-01 Q Q0 Q1 Qs =
  induction Q Q0 (case (λ n → Q n -> Q (suc n)) (λ _ → Q1) Qs)

ack-induction
  : (P : ℕ -> ℕ -> Set)
  → (∀ n → P 0 n)
  → (∀ m → P (suc m) 0)
  → (∀ m → P (suc m) 1)
  → (∀ m n → (∀ k → P m k)
           → P (suc m) (suc n)
           → P (suc m) (suc (suc n)))
  → ∀ m n → P m n
ack-induction P Pzn Psm0 Psm1 Pst =
  induction (λ m → ∀ n → P m n) Pzn Psub
  where
  Psub : ∀ m → (∀ n → P m n) → (∀ n → P (suc m) n)
  Psub m Pmn =
    induction-01 (λ n → P (suc m) n) (Psm0 m) (Psm1 m) (λ n → Pst m n Pmn)

A : ℕ -> ℕ -> ℕ
A = ack-induction (λ m n → ℕ)
  (λ n → 2 * n)               -- A 0 n = 2 * n
  (λ _ → 1)                   -- A (1 + m) 0 = 1
  (λ _ → 2)                   -- A (1 + m) 1 = 2
  (λ m n Am Asmsn → Am Asmsn) -- A (1 + m) (2 + n) = A m (A (1 + m) (1 + n))
