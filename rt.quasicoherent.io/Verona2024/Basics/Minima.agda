{-# OPTIONS --allow-unsolved-metas #-}
module Verona2024.Basics.Minima where

open import Verona2024.Basics.Common

HasMin : (ℕ → Set) → Set
HasMin X = Σ[ n ∈ ℕ ] X n ∧ ((m : ℕ) → X m → n ≤ m)

Detachable : (ℕ → Set) → Set
Detachable X = (n : ℕ) → X n ∨ ¬ (X n)

LEM : Set₁
LEM = (P : Set) → P ∨ (¬ P)

triv : (X : ℕ → Set) → X zero → HasMin X
triv X 0∈X = zero , 0∈X , (λ _ _ → ≤-base)

shift : (ℕ → Set) → (ℕ → Set)
shift X = λ n → X (succ n)

module _ {X : ℕ → Set} where
  lemma : ¬ (X zero) → HasMin (shift X) → HasMin X
  lemma p (n , n∈X' , n-min) = succ n , n∈X' , go
    where
    go : (m : ℕ) → X m → succ n ≤ m
    go zero     zero∈X  = ⊥-elim (p zero∈X)
    go (succ m) succm∈X = ≤-succ (n-min m succm∈X)

a : (X : ℕ → Set) (x₀ : ℕ) → X x₀ → Detachable X → HasMin X
a X zero x₀∈X dec = triv X x₀∈X
a X (succ x₀) succx₀∈X dec with dec zero
... | left 0∈X = triv X 0∈X
... | right ¬0∈X = lemma ¬0∈X (a (shift X) x₀ succx₀∈X λ n → dec (succ n))
--                                            ^^^^^^^^
--                                            x₀∈ShiftX

return : {A : Set} → A → ¬ ¬ A
return x = λ z → z x

oracle : {A : Set} → ¬ ¬ (A ∨ ¬ A)
oracle = λ z → z (right (λ z₁ → z (left z₁)))

_⟫=_ : {A B : Set} → ¬ ¬ A → (A → ¬ ¬ B) → ¬ ¬ B
h ⟫= f = λ z → h (λ z₁ → f z₁ z)

¬¬-map : {A B : Set} → (A → B) → (¬ ¬ A → ¬ ¬ B)
¬¬-map f h = λ z → h (λ z₁ → z (f z₁))

b : (X : ℕ → Set) (x₀ : ℕ) → X x₀ → ¬ ¬ HasMin X
b X zero      zero∈X   = λ z → z (zero , zero∈X , (λ m z₁ → ≤-base))
b X (succ x₀) succx₀∈X = oracle ⟫= go
  where
  go : X zero ∨ ¬ (X zero) → ¬ ¬ HasMin X
  go (left p)  = λ z → z (zero , p , (λ m z₁ → ≤-base))
  go (right p) = ¬¬-map (lemma p) (b (shift X) x₀ succx₀∈X)

data ⊤ : Set where
  tt : ⊤

¬succ≤zero : {n : ℕ} → ¬ (succ n ≤ zero)
¬succ≤zero ()

c : ((X : ℕ → Set) (x₀ : ℕ) → X x₀ → HasMin X) → LEM
c r P = go (r X (succ zero) tt)
  where
  X : ℕ → Set
  X zero     = P
  X (succ _) = ⊤

  go : HasMin X → P ∨ ¬ P
  go (zero   , n∈X , n-min) = left n∈X
  go (succ n , n∈X , n-min) = right (λ p → ¬succ≤zero ((n-min zero p)))
