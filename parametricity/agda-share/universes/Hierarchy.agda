
module Hierarchy where

open import Meta

module Form (U : Set) (T : U → Set) where
  mutual
    data Φ : Set where
      Π̂ : (s : Φ) (f : Θ s → Φ) → Φ
      Σ̂ : (s : Φ) (f : Θ s → Φ) → Φ
      Ŵ : (s : Φ) (f : Θ s → Φ) → Φ
      û : Φ
      t̂ : (s : U) → Φ

    Θ : Φ → Set
    Θ (Π̂ s f) = (S : Θ s) → Θ (f S)
    Θ (Σ̂ s f) = Σ (Θ s) (λ S → Θ (f S))
    Θ (Ŵ s f) = W (Θ s) (λ S → Θ (f S))
    Θ û       = U
    Θ (t̂ s)   = T s

open Form

module Base where
  mutual
    data U₀ : Set where
      0₀ : U₀
      1₀ : U₀
      2₀ : U₀
      L₀ : U₀
      Π₀ : (s : U₀) (f : T₀ s → U₀) → U₀
      Σ₀ : (s : U₀) (f : T₀ s → U₀) → U₀
      W₀ : (s : U₀) (f : T₀ s → U₀) → U₀

    T₀ : U₀ → Set
    T₀ 0₀       = ⊥
    T₀ 1₀       = ⊤
    T₀ 2₀       = Bool
    T₀ L₀       = ℕ
    T₀ (Π₀ s f) = (S : T₀ s) → T₀ (f S)
    T₀ (Σ₀ s f) = Σ (T₀ s) (λ S → T₀ (f S))
    T₀ (W₀ s f) = W (T₀ s) (λ S → T₀ (f S))

open Base

mutual
  U : ℕ → Set
  U 0       = U₀
  U (suc n) = Φ (U n) T

  T : {n : ℕ} → U n → Set
  T {0}     = T₀
  T {suc n} = Θ (U n) T

mutual
  data U∞ : Set where
    Π∞ : (s : U∞) (f : T∞ s → U∞) → U∞
    Σ∞ : (s : U∞) (f : T∞ s → U∞) → U∞
    W∞ : (s : U∞) (f : T∞ s → U∞) → U∞
    u∞ : (n : ℕ) → U∞
    t∞ : {n : ℕ} (s : U n) → U∞

  T∞ : U∞ → Set
  T∞ (Π∞ s f) = (S : T∞ s) → T∞ (f S)
  T∞ (Σ∞ s f) = Σ (T∞ s) (λ S → T∞ (f S))
  T∞ (W∞ s f) = W (T∞ s) (λ S → T∞ (f S))
  T∞ (u∞ n)   = U n
  T∞ (t∞ s)   = T s

Π₊ : ∀{m n} → (s : U m) (f : T s → U n) → U∞
Π₊ s f = Π∞ (t∞ s) (λ S → t∞ (f S))

Σ₊ : ∀{m n} → (s : U m) (f : T s → U n) → U∞
Σ₊ s f = Σ∞ (t∞ s) (λ S → t∞ (f S))

W₊ : ∀{m n} → (s : U m) (f : T s → U n) → U∞
W₊ s f = W∞ (t∞ s) (λ S → t∞ (f S))

poly : U∞
poly = Π∞ (t∞ L₀) \i → u∞ i
