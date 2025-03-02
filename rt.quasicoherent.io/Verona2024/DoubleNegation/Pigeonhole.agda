{-# OPTIONS --allow-unsolved-metas #-}
module Verona2024.DoubleNegation.Pigeonhole where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Bool using (Bool; false; true)
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality

module Classical where
  data ⊥ : Set where

  ⊥-elim : {X : Set} → ⊥ → X
  ⊥-elim ()

  ¬_ : Set → Set
  ¬ X = X → ⊥
  
  not-true-is-false : {x : Bool} → ¬ (true ≡ x) → false ≡ x
  not-true-is-false {false} p = refl
  not-true-is-false {true}  p = ⊥-elim (p refl)

  -- "Boundedly α P" expresses that the predicate P is satisfied by the values
  -- of α only finitely often.
  Boundedly : {X : Set} → (ℕ → X) → (X → Set) → Set
  Boundedly α P = Σ[ a ∈ ℕ ] ((b : ℕ) → b ≥ a → ¬ P (α b))

  -- "Infinitely α P" expresses, in a positive way, that the values of α
  -- satisfy P infinitely often.
  Infinitely : {X : Set} → (ℕ → X) → (X → Set) → Set
  Infinitely α P = (a : ℕ) → Σ[ b ∈ ℕ ] b ≥ a × P (α b)

  postulate
    oracle : {A : Set} → A ⊎ (¬ A)

  lemma : {X : Set} → {α : ℕ → X} {P : X → Set} → ¬ Boundedly α P → Infinitely α P
  lemma {α = α} {P = P} p a with oracle {Σ[ b ∈ ℕ ] b ≥ a × P (α b)}
  ... | inj₁ q = q
  ... | inj₂ q = ⊥-elim (p (a , (λ b b≥a → λ pαb → q (b , b≥a , pαb))))

  module _ (α : ℕ → Bool) where

    theorem : Infinitely α (false ≡_) ⊎ Infinitely α (true ≡_)
    theorem with oracle {Boundedly α (true ≡_)}
    ... | inj₁ (a , p) = inj₁ λ a' → (a' ⊔ a) , m≤m⊔n a' a , not-true-is-false (p (a' ⊔ a) (m≤n⊔m a' a))
    ... | inj₂ p       = inj₂ (lemma {P = true ≡_} p)

    go : {x : Bool} → Infinitely α (x ≡_) → ∃[ i ] ∃[ j ] i < j × α i ≡ α j
    go p =
      let
        (b , b≥zero , x≡αb) = p zero
        (c , c≥sucb , x≡αc) = p (suc b)
      in
        b , c , c≥sucb , trans (sym x≡αb) x≡αc

    corollary : ∃[ i ] ∃[ j ] i < j × α i ≡ α j
    corollary with theorem
    ... | inj₁ p = go p
    ... | inj₂ p = go p

module ConstructiveButUninformative (⊥ : Set) where
  ¬_ : Set → Set
  ¬ X = X → ⊥
  
  ⊥-elim : {X : Set} → ⊥ → ¬ ¬ X
  ⊥-elim a = λ _ → a

  return : {X : Set} → X → ¬ ¬ X
  return x = λ k → k x

  _⟫=_ : {X Y : Set} → ¬ ¬ X → (X → ¬ ¬ Y) → ¬ ¬ Y
  m ⟫= f = λ k → m (λ x → f x k)

  escape : ¬ ¬ ⊥ → ⊥
  escape m = m (λ a → a)

  not-true-is-false : {x : Bool} → ¬ (true ≡ x) → ¬ ¬ (false ≡ x)
  not-true-is-false {false} p = λ z → z refl
  not-true-is-false {true}  p = λ z → p refl

  Boundedly : {X : Set} → (ℕ → X) → (X → Set) → Set
  Boundedly f P = Σ[ a ∈ ℕ ] ((b : ℕ) → b ≥ a → ¬ P (f b))

  Infinitely : {X : Set} → (ℕ → X) → (X → Set) → Set
  Infinitely f P = (a : ℕ) → ¬ ¬ (Σ[ b ∈ ℕ ] b ≥ a × P (f b))

  oracle : {A : Set} → ¬ ¬ (A ⊎ (¬ A))
  oracle = λ k → k (inj₂ (λ x → k (inj₁ x)))

  lemma : {X : Set} → {α : ℕ → X} {P : X → Set} → ¬ Boundedly α P → Infinitely α P
  lemma {α = α} {P = P} p a = λ z → p (a , (λ b z₁ z₂ → z (b , z₁ , z₂)))

  module _ (α : ℕ → Bool) where

    theorem : ¬ ¬ (Infinitely α (false ≡_) ⊎ Infinitely α (true ≡_))
    theorem = oracle {Boundedly α (true ≡_)} ⟫= λ
      { (inj₁ (a , p)) → λ k → k (inj₁ (λ a' → not-true-is-false (p (a' ⊔ a) (m≤n⊔m a' a)) ⟫= λ eq → return ((a' ⊔ a) , m≤m⊔n a' a , eq)))
      ; (inj₂ p) → λ k → k (inj₂ (lemma {P = true ≡_} p))
      }

    go : {x : Bool} → Infinitely α (x ≡_) → ¬ ¬ (∃[ i ] ∃[ j ] i < j × α i ≡ α j)
    go {x} p = p zero ⟫= λ
      (b , b≥zero , x≡αb) → p (suc b) ⟫= λ
      (c , c≥sucb , x≡αc) → return (b , c , c≥sucb , trans (sym x≡αb) x≡αc)

    corollary : ¬ ¬ (∃[ i ] ∃[ j ] i < j × α i ≡ α j)
    corollary = theorem ⟫= λ { (inj₁ p) → go p; (inj₂ p) → go p }

module Constructive where
  module _ (α : ℕ → Bool) where
    Claim : Set
    Claim = ∃[ i ] ∃[ j ] i < j × α i ≡ α j

    open ConstructiveButUninformative (Claim)

    result : Claim
    result = escape (corollary α) 
    -- Run "C-c C-n Constructive.result" (in the Agdapad, "C-c C-v Constructive.result")
    -- to inspect the unrolled proof term. It references α 3 and hence definitely does NOT
    -- coincide with the straightforward proof which just inspects α 0, α 1 and α 2
    -- and looks for two equal values among these three values.
