{-# OPTIONS --allow-unsolved-metas #-}
module Verona2024.Realizability.Soundness where
-- NOTE: I'm not yet content with this development; a cleanup is planned.

open import Verona2024.Realizability.Common

open import Data.Nat
open import Data.Fin hiding (raise)
open import Data.List
open import Data.Vec hiding (length; toList)
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any
open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Data.Product

data _⊢_ : {Γ : Cxt} → Form Γ → Form Γ → Set where
  identity     : {Γ : Cxt} {φ : Form Γ} → φ ⊢ φ
  conj-elimₗ   : {Γ : Cxt} {α β : Form Γ} → (α ∧ β) ⊢ α
  conj-intr    : {Γ : Cxt} {α β χ : Form Γ} → χ ⊢ α → χ ⊢ β → χ ⊢ (α ∧ β)
  reflexivity  : {τ : Ty} → ⊤ ⊢ (var {τ ∷ []} (here refl) ≈ var (here refl))
  substitution : {Γ Δ : Cxt} {α β : Form Γ} (f : {σ : Ty} → σ ∈ Γ → Term Δ σ) → α ⊢ β → subs α f ⊢ subs β f
  -- add more proof rules here

module _ (P… : PCA) where
  open PCA P…
  open Church P…
  open Semantics P…

  Valid : {Γ : Cxt} → Env Γ → Set
  Valid {Γ} env = {τ : Ty} → (i : τ ∈ Γ) → ⟦ τ ⟧ (env i) 

  sound : {Γ : Cxt} {α β : Form Γ} → α ⊢ β → Σ[ r ∈ Expr (suc (length Γ)) ] ((env : Env Γ) (s : Code) → Valid env → s ⊩⟨ env ⟩ α → multi r (s ∷ toList env) (λ k → k ⊩⟨ env ⟩ β))
  sound identity = var zero , λ env s v x → x
  sound conj-elimₗ = var zero · lit zer , λ env s v x → implies s zer _ _ (λ y → implies' s one _ _ λ y → proj₁) x
  sound _ = {!!}
  -- more cases go here

  theorem : {α : Form []} → ⊤ ⊢ α → Σ[ r ∈ Code ] r ⊩⟨ ∅ ⟩ (⊤ ⇒ α)
  theorem p = lambda (proj₁ (sound p)) , λ s _ → multi→app _ _ _ (proj₂ (sound p) ∅ s (λ ()) tt)
