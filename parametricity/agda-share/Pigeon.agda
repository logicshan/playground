
module Pigeon where

open import Function

open import Data.Empty
open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat as Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality


lift : ∀{m : ℕ} {ms}
    → Σ[ n ∈ ℕ ] (n ∈ ms) × (1 < n)
    → Σ[ n ∈ ℕ ] (n ∈ m ∷ ms) × (1 < n)
lift (n , n∈ms , 1<n) = (n , there n∈ms , 1<n)

test : (n : ℕ) → (n ≤ 1) ⊎ (1 < n)
test 0 = inj₁ z≤n
test 1 = inj₁ ≤-refl
test (suc (suc n)) = inj₂ (m≤m+n 2 n)

module Negative where
    down : ∀{m ms}
         → (∀ n → n ∈ (m ∷ ms) → n ≤ 1)
         → ∀ n → n ∈ ms → n ≤ 1
    down all n n∈ms = all n (there n∈ms)

    negative : (l : List ℕ)
             → (∀ n → n ∈ l → n ≤ 1)
             → sum l ≤ length l
    negative [] all = ≤-refl
    negative (n ∷ ns) all with test n
    ... | inj₁ n≤1 = +-mono-≤ n≤1 (negative ns (down all))
    ... | inj₂ 1<n = ⊥-elim (<⇒≱ 1<n (all n (here refl)))

    up : ∀{m ms}
       → m ≤ 1
       → (∀ n → n ∈ ms → n ≤ 1)
       → ∀ n → n ∈ m ∷ ms → n ≤ 1
    up m≤1 all n (here refl) = m≤1
    up m≤1 all n (there n∈ms) = all n n∈ms

    search : (l : List ℕ)
           → ¬ (∀ n → n ∈ l → n ≤ 1)
           → Σ[ n ∈ ℕ ] (n ∈ l) × (1 < n)
    search [] ¬all = ⊥-elim (¬all λ _ ())
    search (n ∷ ns) ¬all with test n
    ... | inj₁ n≤1 = lift (search ns (¬all ∘ up n≤1))
    ... | inj₂ 1<n = n , here refl , 1<n

    positive : (l : List ℕ)
             → length l < sum l
             → Σ[ n ∈ ℕ ] (n ∈ l) × (1 < n)
    positive l l<s = search l λ all → <⇒≱ l<s (negative l all)


module Positive where
    cancel : ∀{i j k l} → k ≤ i → i + j < k + l → j < l
    cancel {i} k≤i i+j<k+l = +-cancelˡ-< i (<-transˡ i+j<k+l (+-monoˡ-≤ _ k≤i))

    positive : (l : List ℕ)
             → length l < sum l
             → Σ[ n ∈ ℕ ] (n ∈ l) × 1 < n
    positive (n ∷ ns) l<s with test n
    ... | inj₂ 1<n = (n , here refl , 1<n)
    ... | inj₁ n≤1 = lift (positive ns (cancel n≤1 l<s))
