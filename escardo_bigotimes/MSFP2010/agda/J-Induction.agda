module J-Induction where

open import Logic
open import Induction
open import JK-Monads
open import JK-Shifts


J-induction' : {R : Ω} {A : ℕ → Ω} → 
-----------
            J R(A O) → (∀(k : ℕ) → A k → J R (A(succ k))) → ∀(n : ℕ) → J R (A n)

J-induction' base step = induction base (λ k → J-extend(step k))



J-induction : {R : Ω} {A : ℕ → Ω} → 
-----------
            A O → (∀(k : ℕ) → A k → J R (A(succ k))) → J R (∀(n : ℕ) → A n)

J-induction base step = J-∀-shift(induction (ηJ base) (λ k → J-extend(step k)))
