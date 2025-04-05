module course-of-values where

open import Logic
open import LogicalFacts
open import finite-sets
open import Induction
open import Equality

course-of-values : {A : ℕ → Ω} → 
    (∀(n : ℕ) → (∀(i : Fin n) → A(nat i)) → A n) → ∀(n : ℕ) → A n

course-of-values {A} f n = lemma₁ n (lemma₀(succ n))
 where lemma₀ : ∀(n : ℕ) → ∀(i : Fin n) → A(nat i)
       lemma₀ = induction base step
         where base : ∀(i : Fin O) → A(nat i)
               base =  λ ()

               step : ∀(n : ℕ) → (∀(i : Fin n) → A(nat i)) → ∀(i : Fin(succ n)) → A(nat i)
               step n s = append {A} s (f n s)

       lemma₁ : ∀(n : ℕ) → (∀(i : Fin(succ n)) → A(nat i)) → A n
       lemma₁ n s = predicate-compositionality A (nat∘tan-is-identity n) (s (tan n))
