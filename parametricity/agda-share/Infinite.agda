
module Infinite where

open import Data.Empty
open import Data.Nat as Nat
open import Data.Product

open import Data.List
open import Data.List.Any as Any
open import Data.List.All as All
open Any.Membership (setoid) using (_∈_ ; _∉_)

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

maximum : List ℕ → ℕ
maximum []        = 0
maximum (n ∷ ns) = n ⊔ maximum ns

lemma₁ : ∀{x P l} → x ∈ l → All P l → P x
lemma₁ (here refl) (Px ∷ _)  = Px
lemma₁ (there x∈l) (_  ∷ AP) = lemma₁ x∈l AP

lemma₂ : ∀{m n} → m ≤ m ⊔ n
lemma₂ {zero}          = z≤n
lemma₂ {suc m} {zero}  = DecTotalOrder.reflexive decTotalOrder refl
lemma₂ {suc m} {suc n} = s≤s lemma₂

lemma₃ : ∀{o m n} → m ≤ n → m ≤ o ⊔ n
lemma₃             z≤n       = z≤n
lemma₃ {o = 0}     m≤n       = m≤n
lemma₃ {o = suc o} (s≤s m≤n) = s≤s (lemma₃ {o = o} m≤n)

lemma₄ : ∀{A l} {P Q : A → Set} → (∀{x} → P x → Q x) → All P l → All Q l
lemma₄ pq []           = []
lemma₄ pq (Px ∷ APxs) = pq Px ∷ lemma₄ pq APxs

lemma₅ : ∀{l} → All (λ x → x < suc (maximum l)) l
lemma₅ {[]}      = []
lemma₅ {x ∷ xs} =
   s≤s lemma₂ ∷ lemma₄ (λ pf → s≤s (lemma₃ {x} (aux pf))) lemma₅
 where
 aux : ∀{m n} → suc m ≤ suc n → m ≤ n
 aux (s≤s m≤n) = m≤n

lemma₆ : ∀{n} → ¬ n < n
lemma₆ {zero} ()
lemma₆ {suc n} (s≤s n<n) = lemma₆ n<n

infinite-ℕ : ∀ l → Σ ℕ λ x → x ∉ l
infinite-ℕ l = suc max , λ sm∈l → lemma₆ (lemma₁ sm∈l lemma₅)
 where
 max = maximum l
