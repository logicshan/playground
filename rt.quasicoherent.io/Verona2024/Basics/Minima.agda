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
triv X 0∈X = {!!}

shift : (ℕ → Set) → (ℕ → Set)
shift X = λ n → X (succ n)

module _ {X : ℕ → Set} where
  lemma : ¬ (X zero) → HasMin (shift X) → HasMin X
  lemma p (n , n∈X' , n-min) = {!!}
    where
    go : (m : ℕ) → X m → succ n ≤ m
    go zero     zero∈X  = {!!}
    go (succ m) succm∈X = {!!}

a : (X : ℕ → Set) (x₀ : ℕ) → X x₀ → Detachable X → HasMin X
a X zero      x₀∈X     dec = {!!}
a X (succ x₀) succx₀∈X dec with dec zero
... | left  p = {!!}
... | right p = {!!}

return : {A : Set} → A → ¬ ¬ A
return x = {!!}

oracle : {A : Set} → ¬ ¬ (A ∨ ¬ A)
oracle = {!!}

_⟫=_ : {A B : Set} → ¬ ¬ A → (A → ¬ ¬ B) → ¬ ¬ B
h ⟫= f = {!!}

¬¬-map : {A B : Set} → (A → B) → (¬ ¬ A → ¬ ¬ B)
¬¬-map f h = {!!}

b : (X : ℕ → Set) (x₀ : ℕ) → X x₀ → ¬ ¬ HasMin X
b X zero      zero∈X   = {!!}
b X (succ x₀) succx₀∈X = oracle ⟫= go
  where
  go : X zero ∨ ¬ (X zero) → ¬ ¬ HasMin X
  go (left p)  = {!!}
  go (right p) = {!!}

data ⊤ : Set where
  tt : ⊤

¬succ≤zero : {n : ℕ} → ¬ (succ n ≤ zero)
¬succ≤zero ()

c : ((X : ℕ → Set) (x₀ : ℕ) → X x₀ → HasMin X) → LEM
c r P = {!!}
  where
  X : ℕ → Set
  X zero     = P
  X (succ _) = ⊤

  go : HasMin X → P ∨ ¬ P
  go (zero   , n∈X , n-min) = {!!}
  go (succ n , n∈X , n-min) = {!!}
