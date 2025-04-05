
module NBP.Prod.Terms where

open import Cubical.Foundations.Function hiding (_$_)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
import Cubical.Data.Empty as Empty
open import Cubical.Data.Fin.Recursive as Fin
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Relation.Nullary

open import NBP.Prod.Types
open import NBP.Prod.Terms.Core as Terms
import NBP.Prod.Terms.Levels as Levels

module Rn-Stx where
  open Stx

  rn-tm : Rn Γ Δ → Tm Δ A → Tm Γ A
  rn-tm ρ (va v) = va (rn-∈ ρ v)
  rn-tm ρ tt = tt
  rn-tm ρ (l , r) = rn-tm ρ l , rn-tm ρ r
  rn-tm ρ (π₁ p) = π₁ (rn-tm ρ p)
  rn-tm ρ (π₂ p) = π₂ (rn-tm ρ p)
  rn-tm ρ (la e) = la (rn-tm (sh ρ) e)
  rn-tm ρ (f $ e) = rn-tm ρ f $ rn-tm ρ e

  rn-tm-id : ∀(e : Tm Γ A) → rn-tm rn-id e ≡ e
  rn-tm-id (va v) = refl
  rn-tm-id tt = refl
  rn-tm-id (l , r) = cong₂ _,_ (rn-tm-id l) (rn-tm-id r)
  rn-tm-id (π₁ p) = cong π₁ (rn-tm-id p)
  rn-tm-id (π₂ p) = cong π₂ (rn-tm-id p)
  rn-tm-id (la e) =
    cong la (subst F sh-id (rn-tm-id e))
    where F = λ γ → rn-tm γ e ≡ e
  rn-tm-id (f $ e) = cong₂ _$_ (rn-tm-id f) (rn-tm-id e)

  rn-tm-∘ : ∀(e : Tm Γ A) → rn-tm (ρ rn∘ σ) e ≡ rn-tm ρ (rn-tm σ e)
  rn-tm-∘ {σ = σ} (va v) = refl
  rn-tm-∘ tt = refl
  rn-tm-∘ (l , r) = cong₂ _,_ (rn-tm-∘ l) (rn-tm-∘ r)
  rn-tm-∘ (π₁ p) = cong π₁ (rn-tm-∘ p)
  rn-tm-∘ (π₂ p) = cong π₂ (rn-tm-∘ p)
  rn-tm-∘ {ρ = ρ} {σ} (la e) =
    cong la (subst F (sh-∘ ρ σ) (rn-tm-∘ e))
    where F = λ γ → rn-tm γ e ≡ rn-tm (sh ρ) (rn-tm (sh σ) e)
  rn-tm-∘ (f $ e) = cong₂ _$_ (rn-tm-∘ f) (rn-tm-∘ e)


module Rn-Sem where
  open Sem
  open Levels using (isSet-No; isSet-Ne)

  rn-no : Rn Γ Δ → No Δ A → No Γ A
  rn-ne : Rn Γ Δ → Ne Δ A → Ne Γ A

  rn-no ρ tt = tt
  rn-no ρ (l , r) = rn-no ρ l , rn-no ρ r
  rn-no ρ (la e) = la (rn-no (sh ρ) e)
  rn-no ρ (ne e) = ne (rn-ne ρ e)

  rn-ne ρ (va v) = va (rn-∈ ρ v)
  rn-ne ρ (π₁ p) = π₁ (rn-ne ρ p)
  rn-ne ρ (π₂ p) = π₂ (rn-ne ρ p)
  rn-ne ρ (f $ e) = rn-ne ρ f $ rn-no ρ e

  rn-no-id : ∀(e : No Γ A) → rn-no rn-id e ≡ e
  rn-ne-id : ∀(e : Ne Γ A) → rn-ne rn-id e ≡ e

  rn-no-id tt = refl
  rn-no-id (l , r) = cong₂ _,_ (rn-no-id l) (rn-no-id r)
  rn-no-id (la e) =
    cong la (subst F sh-id (rn-no-id e))
    where F = λ γ → rn-no γ e ≡ e
  rn-no-id (ne e) = cong ne (rn-ne-id e)

  rn-ne-id (va v) = refl
  rn-ne-id (π₁ e) = cong π₁ (rn-ne-id e)
  rn-ne-id (π₂ e) = cong π₂ (rn-ne-id e)
  rn-ne-id (f $ e) = cong₂ _$_ (rn-ne-id f) (rn-no-id e)

  rn-no-∘ : ∀(ρ : Rn Θ Δ) (σ : Rn Δ Γ) (e : No Γ A)
          → rn-no (ρ rn∘ σ) e ≡ rn-no ρ (rn-no σ e)
  rn-ne-∘ : ∀(ρ : Rn Θ Δ) (σ : Rn Δ Γ) (e : Ne Γ A)
          → rn-ne (ρ rn∘ σ) e ≡ rn-ne ρ (rn-ne σ e)

  rn-no-∘ ρ σ tt = refl
  rn-no-∘ ρ σ (l , r) = cong₂ _,_ (rn-no-∘ ρ σ l) (rn-no-∘ ρ σ r)
  rn-no-∘ ρ σ (la e) =
    cong la (cong f (sym (sh-∘ ρ σ)) ∙ rn-no-∘ (sh ρ) (sh σ) e)
    where f = λ γ → rn-no γ e
  rn-no-∘ ρ σ (ne e) = cong ne (rn-ne-∘ ρ σ e)

  rn-ne-∘ ρ σ (va v) = refl
  rn-ne-∘ ρ σ (π₁ e) = cong π₁ (rn-ne-∘ ρ σ e)
  rn-ne-∘ ρ σ (π₂ e) = cong π₂ (rn-ne-∘ ρ σ e)
  rn-ne-∘ ρ σ (f $ e) = cong₂ _$_ (rn-ne-∘ ρ σ f) (rn-no-∘ ρ σ e)

  rn-ne-∘∘ : ∀(ρ : Rn Φ Θ) (σ : Rn Θ Δ) (τ : Rn Δ Γ) (e : Ne Γ A)
           → PathP (λ i → rn-ne-∘ (ρ rn∘ σ) τ e i ≡ rn-ne ρ (rn-ne-∘ σ τ e i))
               (rn-ne-∘ ρ (σ rn∘ τ) e)
               (rn-ne-∘ ρ σ (rn-ne τ e))
  rn-no-∘∘ : ∀(ρ : Rn Φ Θ) (σ : Rn Θ Δ) (τ : Rn Δ Γ) (e : No Γ A)
           → PathP (λ i → rn-no-∘ (ρ rn∘ σ) τ e i ≡ rn-no ρ (rn-no-∘ σ τ e i))
               (rn-no-∘ ρ (σ rn∘ τ) e)
               (rn-no-∘ ρ σ (rn-no τ e))

  rn-ne-∘∘ {Φ = Φ} {A = A} ρ σ τ e =
    isSet→isSet' (isSet-Ne Φ A)
      (rn-ne-∘ ρ (σ rn∘ τ) e)
      (rn-ne-∘ ρ σ (rn-ne τ e))
      (rn-ne-∘ (ρ rn∘ σ) τ e)
      (cong (rn-ne ρ) (rn-ne-∘ σ τ e))

  rn-no-∘∘ {Φ = Φ} {A = A} ρ σ τ e =
    isSet→isSet' (isSet-No Φ A)
      (rn-no-∘ ρ (σ rn∘ τ) e)
      (rn-no-∘ ρ σ (rn-no τ e))
      (rn-no-∘ (ρ rn∘ σ) τ e)
      (cong (rn-no ρ) (rn-no-∘ σ τ e))


module Env where
  open Sem
  open Rn-Sem

  En : Cx → Cx → Type
  En Γ [] = Unit
  En Γ (Δ ∷ A) = En Γ Δ × Ne Γ A

  en-id : ∀ Γ → En Γ Γ
  en-id Γ = build Γ (idfun _) where
    build : ∀ Δ → (∀{A} → A ∈ Δ → A ∈ Γ) → En Γ Δ
    build []      _  = _
    build (Δ ∷ B) up = build Δ (up ∘ po) , va (up to)

  rn-en : Rn Γ Δ → En Δ Θ → En Γ Θ
  rn-en {Θ = []}    ρ e = _
  rn-en {Θ = Θ ∷ A} ρ (e , x) = rn-en ρ e , rn-ne ρ x

  rn-en-id : ∀(e : En Δ Θ) → rn-en rn-id e ≡ e
  rn-en-id {Θ = []}    _ = refl
  rn-en-id {Θ = Θ ∷ A} (e , x) =
    ≡-× (rn-en-id e) (rn-ne-id x)

  rn-en-∘ : ∀(ρ : Rn Φ Γ) (σ : Rn Γ Δ) (e : En Δ Θ)
          → rn-en (ρ rn∘ σ) e ≡ rn-en ρ (rn-en σ e)
  rn-en-∘ {Θ = []} _ _ _ = refl
  rn-en-∘ {Θ = Θ ∷ A} ρ σ (e , x) =
    ≡-× (rn-en-∘ ρ σ e) (rn-ne-∘ ρ σ x)
  
  isSet-En : ∀ Γ Δ → isSet (En Γ Δ)
  isSet-En Γ [] = isSetUnit
  isSet-En Γ (Δ ∷ A) = isSet× (isSet-En Γ Δ) (Levels.isSet-Ne Γ A)
