
module FiniteChoice where

open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Nat
open import Cubical.Data.Fin.Recursive
open import Cubical.HITs.PropositionalTruncation as PT

variable
  ℓ : Level
  n : ℕ

choose₀
  : (P : Lift {j = ℓ} (Fin n) → Type ℓ) → (∀ x → ∥ P x ∥) → ∥ (∀ x → P x) ∥
choose₀ {ℓ} {zero} P f = ∣ Empty.elim {ℓ} {P ∘ lift} ∘ lower ∣
choose₀ {n = suc n} P f
  = map2 merge (f (lift zero)) (choose₀ (P ∘ suc') (f ∘ suc'))
  where
  suc' = lift ∘ suc ∘ lower
  merge : P (lift zero) → (∀ x → P (lift (suc (lower x)))) → ∀ x → P x
  merge Pz Ps (lift zero) = Pz
  merge Pz Ps (lift (suc x)) = Ps (lift x)

mediate
  : (F : Type ℓ) (P : F → Type ℓ)
  → Σ[ n ∈ ℕ ] Fin n ≃ F
  → (∀ x → ∥ P x ∥)
  → ∥ (∀ x → P x) ∥
mediate F P (n , e) = transport (λ i → C (ua e' i)) choose₀ P
  where
  e' : Lift (Fin _) ≃ F
  e' = compEquiv (invEquiv LiftEquiv) e
  C : Type _ → Type _
  C A = (P : A → Type _) → (∀ x → ∥ P x ∥) → ∥ (∀ x → P x) ∥

isFinite : Type ℓ → Type ℓ
isFinite F = ∥ Σ[ n ∈ ℕ ] Fin n ≃ F ∥

Finite : ∀ ℓ → Type (ℓ-suc ℓ)
Finite ℓ = Σ[ F ∈ Type ℓ ] isFinite F

choose
  : ∀{F : Finite ℓ} {P : F .fst → Type ℓ}
  → (∀ x → ∥ P x ∥) → ∥ (∀ x → P x) ∥
choose {F = F , fin} {P} = PT.rec (isPropΠ λ _ → squash) (mediate F P) fin

