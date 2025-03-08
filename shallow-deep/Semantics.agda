module Semantics where

-- The set-theoretic model of λ-calculus

open import Data.Nat
open import Data.Unit
open import Data.Product

open import Deep

-- Types are interpreted as sets
⟦_⟧ᵗ : type → Set
⟦ nat ⟧ᵗ = ℕ
⟦ A ⇒ B ⟧ᵗ = ⟦ A ⟧ᵗ → ⟦ B ⟧ᵗ

-- Contexts are interpreted as sets
⟦_⟧ᶜ : context → Set
⟦ ∙ ⟧ᶜ = ⊤
⟦ Γ ⨟ A ⟧ᶜ =  ⟦ Γ ⟧ᶜ × ⟦ A ⟧ᵗ

-- Auxiliary map, for looking up values of variables
lookup : ∀ {Γ A} → A ∈ Γ → ⟦ Γ ⟧ᶜ → ⟦ A ⟧ᵗ
lookup z (_ , a) = a
lookup (s x) (η , _) = lookup x η

-- A typing judgement Γ ⊢ e : A is interpreted as a map ⟦ e ⟧ : ⟦ Γ ⟧ᶜ → ⟦ A ⟧ᵗ
⟦_⟧ : ∀ {Γ A} → term Γ A → ⟦ Γ ⟧ᶜ → ⟦ A ⟧ᵗ
⟦ zero ⟧ η = 0
⟦ succ e ⟧ η = suc (⟦ e ⟧ η)
⟦ var x ⟧ η = lookup x η
⟦ lam A e ⟧ η = λ a → ⟦ e ⟧ (η , a)
⟦ app e₁ e₂ ⟧ η = ⟦ e₁ ⟧ η (⟦ e₂ ⟧ η)

-- The interpretation of ∙ ⊢ (λ (x : nat) . succ (succ x)) (succ zero) : nat
cow : ⟦ ∙ ⟧ᶜ → ⟦ nat ⟧ᵗ
cow tt = ⟦ app (lam nat (succ (succ (var z)))) (succ zero) ⟧ tt
-- Agda normalizes cow tt to the numeral 3
