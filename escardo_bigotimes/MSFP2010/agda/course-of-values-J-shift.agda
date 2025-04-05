{-# OPTIONS --no-termination-check #-}

module course-of-values-J-shift where

open import Logic
open import LogicalFacts
open import Induction
open import JK-Monads

course-of-values-J-∧-shift : {R A₀ A₁ : Ω} → 
--------------------------
                              J R A₀ ∧ (A₀ → J R A₁) → J R (A₀ ∧ A₁)

course-of-values-J-∧-shift (∧-intro ε₀ f) = J-extend(λ a₀ → J-strength (∧-intro a₀ (f a₀))) ε₀


course-of-values-J-∧-shift' : {R : Ω} {A : ℕ → Ω} → 
--------------------------
                               J R (A O) ∧ (A O → J R (∀(n : ℕ) → A(succ n))) → 
                               J R (∀(n : ℕ) → A n)

course-of-values-J-∧-shift' = (J-functor cons) ∘ course-of-values-J-∧-shift


bounded-∀ : (n : ℕ) → (A : ℕ → Ω) → Ω
bounded-∀ O A = ⊤
bounded-∀ (succ n) A = (bounded-∀ n A) ∧ A n

push : {n : ℕ} → {A : ℕ → Ω} → A O → (bounded-∀ n (λ k → A(succ k))) → bounded-∀ (succ n) A
push {O} a * = ∧-intro * a
push {succ n} a (∧-intro b a') = ∧-intro (push a b) a'


course-of-values-J-∀-shift : {R : Ω} {A : ℕ → Ω} → 
--------------------------
                             (∀(n : ℕ) → (bounded-∀ n A) → J R (A n)) → J R (∀(n : ℕ) → A n)

course-of-values-J-∀-shift {R} {A} ε =
  course-of-values-J-∧-shift' (∧-intro ε₀ (λ a → course-of-values-J-∀-shift (ε' a)))

  where ε₀ : J R (A O)
        ε₀ = head ε *

        ε' : A O → ∀(n : ℕ) → (bounded-∀ n (λ k → A(succ k))) → J R (A(succ n))
        ε' a n b = ε(succ n)(push a b)  


