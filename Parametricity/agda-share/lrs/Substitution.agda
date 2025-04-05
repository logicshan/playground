
module Substitution where

-- This module implements substitution and renaming. It proves many
-- lemmas and installs them as rewrite rules to avoid having to
-- explicitly substitute elsewhere, allowing the reduction lemmas to
-- look a lot more like the source paper.

open import Syntax

open import Function

open import Relation.Binary.PropositionalEquality
open import Agda.Builtin.Equality.Rewrite

-- Function extensionality is a must for renamings/substitutions as
-- functions.
postulate
  funExt : ∀{A : Set} {B : A -> Set} {f g : (x : A) -> B x}
        -> (∀ x -> f x ≡ g x) -> f ≡ g
  funExtI : ∀{A : Set} {B : A -> Set} {f g : {x : A} -> B x}
        -> (∀ x -> f {x} ≡ g {x}) -> (λ{x} → f {x}) ≡ (λ{x} → g {x})

-- Variable renamings
record Rn (Γ : Cx) (Δ : Cx) : Set where
  constructor pack
  field lookup : Vr Δ t -> Vr Γ t
open Rn public

-- Augments a renaming by adding a variable to both input and output.
tk : Rn Γ Δ -> Rn (Γ ∷ s) (Δ ∷ s)
tk r .lookup to     = to
tk r .lookup (po v) = po (r .lookup v)

-- Composes two renamings.
_∙_ : Rn Γ Θ -> Rn Θ Δ -> Rn Γ Δ
(rn₀ ∙ rn₁) .lookup = lookup rn₀ ∘ lookup rn₁

-- tk commutes with composition
∙-tk : ∀{rn : Rn Γ Θ} {sn : Rn Θ Δ}
    -> tk {s = s} rn ∙ tk sn ≡ tk (rn ∙ sn)
∙-tk {s = s} {rn = rn} {sn} =
  cong pack (funExtI λ t → funExt λ{ to → refl ; (po v) → refl })
{-# REWRITE ∙-tk #-}

-- The reflexive renaming
reflᵣₙ : Rn Γ Γ
reflᵣₙ .lookup v = v

-- The weakening renaming
wk : Rn (Γ ∷ s) Γ
wk .lookup = po

step : Rn Γ Δ -> Rn (Γ ∷ s) Δ
step r .lookup = po ∘ lookup r

-- Overloading for renaming.
record Renameable (T : Cx -> Set) : Set where
  field rename : Rn Γ Δ -> T Δ -> T Γ
open Renameable {{...}} public

-- Variables can be renamed
instance
  renameᵥ : Renameable (λ Γ -> Vr Γ t)
  renameᵥ .rename r = lookup r

module Renaming where
  go : Rn Γ Δ -> Tm Δ t -> Tm Γ t
  go rn (vr x)     = vr (lookup rn x)
  go rn tt         = tt
  go rn (la e)     = la (go (tk rn) e)
  go rn (ap f e)   = ap (go rn f) (go rn e)
  go rn (il e)     = il (go rn e)
  go rn (ir e)     = ir (go rn e)
  go rn (ca e l r) = ca (go rn e) (go (tk rn) l) (go (tk rn) r)

  go-go : ∀(rn : Rn Γ Θ) (sn : Rn Θ Δ) (e : Tm Δ t)
       -> go rn (go sn e) ≡ go (rn ∙ sn) e
  go-go rn sn (vr x) = refl
  go-go rn sn tt = refl
  go-go rn sn (la e) = cong la (go-go (tk rn) (tk sn) e)
  go-go rn sn (ap f e) = cong₂ ap (go-go rn sn f) (go-go rn sn e)
  go-go rn sn (il e) = cong il (go-go rn sn e)
  go-go rn sn (ir e) = cong ir (go-go rn sn e)
  go-go rn sn (ca e l r) rewrite go-go rn sn e
    = cong₂ (ca _)
        (go-go (tk rn) (tk sn) l)
        (go-go (tk rn) (tk sn) r)
  {-# REWRITE go-go #-}

-- Terms can be renamed
instance
  renameₜₘ : Renameable (λ Γ -> Tm Γ t)
  renameₜₘ .rename = Renaming.go

-- Substitutions from a variables to terms
record Su (Γ : Cx) (Δ : Cx) : Set where
  constructor pack
  field lookup : Vr Δ t -> Tm Γ t
open Su public

bu : Su Δ Γ -> Su (Δ ∷ s) (Γ ∷ s)
bu su .lookup to     = vr to
bu su .lookup (po v) = rename wk (su .lookup v)

reflₛᵤ : Su Γ Γ
reflₛᵤ .lookup = vr

_⟩_ : Su Γ Δ -> Tm Γ t -> Su Γ (Δ ∷ t)
(su ⟩ t) .lookup to     = t
(su ⟩ t) .lookup (po v) = su .lookup v

suExt : {φ ψ : Su Γ Δ} -> (∀{t} v → lookup φ {t} v ≡ lookup ψ v) → φ ≡ ψ
suExt f = cong pack (funExtI λ t → funExt f)

bu-refl : bu reflₛᵤ ≡ reflₛᵤ {Γ ∷ s}
bu-refl = suExt λ{ to → refl ; (po v) → refl }
{-# REWRITE bu-refl #-}

-- Overloading for simultaneous substitution.
record Substitutable (T : Cx -> Set) : Set where
  constructor pack
  field ssub : Su Γ Δ -> T Δ -> T Γ
open Substitutable {{...}} public

-- Single substitution
sub : ∀{T} {{_ : Substitutable T}} -> Tm Γ s -> T (Γ ∷ s) -> T Γ
sub m e = ssub (reflₛᵤ ⟩ m) e

module Substitution where
  go : Su Γ Δ -> Tm Δ t -> Tm Γ t
  go su (vr v)     = lookup su v
  go su tt         = tt
  go su (la e)     = la (go (bu su) e)
  go su (ap f e)   = ap (go su f) (go su e)
  go su (il e)     = il (go su e)
  go su (ir e)     = ir (go su e)
  go su (ca e l r) =
    ca (go su e) (go (bu su) l) (go (bu su) r)

  _«_ : Su Γ Θ -> Rn Θ Δ -> Su Γ Δ
  (φ « σ) .lookup = lookup φ ∘ lookup σ

  _»_ : Rn Γ Θ -> Su Θ Δ -> Su Γ Δ
  (σ » φ) .lookup = rename σ ∘ lookup φ

  wk-shift : (φ : Su Γ Δ) -> bu {s = s} φ « wk ≡ wk » φ
  wk-shift φ = suExt λ{ to → refl ; (po v) → refl }

  ⟩-«-wk : (φ : Su Γ Δ) -> (e : Tm Γ t) -> (φ ⟩ e) « wk ≡ φ
  ⟩-«-wk φ e = suExt λ{ to → refl ; (po v) → refl }
  {-# REWRITE ⟩-«-wk #-}

  bu-« : (φ : Su Γ Θ) (σ : Rn Θ Δ) -> bu {s = s} φ « tk σ ≡ bu (φ « σ)
  bu-« φ σ = suExt λ{ to → refl ; (po v) → refl }
  {-# REWRITE bu-« #-}

  bu-» : (σ : Rn Γ Θ) (φ : Su Θ Δ) -> tk σ » bu {s = s} φ ≡ bu (σ » φ)
  bu-» σ φ = suExt λ{ to → refl ; (po v) → refl }
  {-# REWRITE bu-» #-}

  go-rn : (φ : Su Γ Θ)
       -> (σ : Rn Θ Δ)
       -> (e : Tm Δ t)
       -> go φ (rename σ e) ≡ go (φ « σ) e
  go-rn φ σ (vr v)   = refl
  go-rn φ σ tt       = refl
  go-rn φ σ (la e)   = cong la (go-rn (bu φ) (tk σ) e)
  go-rn φ σ (ap f e) = cong₂ ap (go-rn φ σ f) (go-rn φ σ e)
  go-rn φ σ (il e)   = cong il (go-rn φ σ e)
  go-rn φ σ (ir e)   = cong ir (go-rn φ σ e)
  go-rn φ σ (ca e l r) rewrite go-rn φ σ e
    = cong₂ (ca _)
        (go-rn (bu φ) (tk σ) l)
        (go-rn (bu φ) (tk σ) r)
  {-# REWRITE go-rn #-}

  rn-go : (σ : Rn Γ Θ)
       -> (φ : Su Θ Δ)
       -> (e : Tm Δ t)
       -> Renaming.go σ (go φ e) ≡ go (σ » φ) e
  rn-go σ φ (vr v)   = refl
  rn-go σ φ tt       = refl
  rn-go σ φ (la e)   = cong la (rn-go (tk σ) (bu φ) e)
  rn-go σ φ (ap f e) = cong₂ ap (rn-go σ φ f) (rn-go σ φ e)
  rn-go σ φ (il e)   = cong il (rn-go σ φ e)
  rn-go σ φ (ir e)   = cong ir (rn-go σ φ e)
  rn-go σ φ (ca e l r) rewrite rn-go σ φ e
    = cong₂ (ca _)
        (rn-go (tk σ) (bu φ) l)
        (rn-go (tk σ) (bu φ) r)
  {-# REWRITE rn-go #-}

  go-refl : (e : Tm Γ t) -> go reflₛᵤ e ≡ e
  go-refl (vr _) = refl
  go-refl tt = refl
  go-refl (la e) = cong la (go-refl e)
  go-refl (ap f e) = cong₂ ap (go-refl f) (go-refl e)
  go-refl (il e) = cong il (go-refl e)
  go-refl (ir e) = cong ir (go-refl e)
  go-refl (ca e r l) rewrite go-refl e
    = cong₂ (ca _) (go-refl r) (go-refl l)
  {-# REWRITE go-refl #-}

  _«»_ : Su Γ Θ -> Su Θ Δ -> Su Γ Δ
  (φ «» ψ) .lookup = go φ ∘ lookup ψ

  bu-«» : (φ : Su Γ Θ) -> (ψ : Su Θ Δ)
       -> bu {s = s} φ «» bu ψ ≡ bu (φ «» ψ)
  bu-«» φ ψ = suExt λ where
    to → refl
    (po v) → cong (λ ξ → go ξ (lookup ψ v)) (wk-shift φ)
  {-# REWRITE bu-«» #-}

  ⟩-«»-bu : (φ : Su Γ Δ) -> (e : Tm Γ t)
         -> (reflₛᵤ ⟩ e) «» bu φ ≡ φ ⟩ e
  ⟩-«»-bu φ e = suExt λ{ to → refl ; (po v) → refl }
  {-# REWRITE ⟩-«»-bu #-}

  go-go : (φ : Su Γ Θ)
       -> (ψ : Su Θ Δ)
       -> (e : Tm Δ t)
       -> go φ (go ψ e) ≡ go (φ «» ψ) e
  go-go φ ψ (vr _)   = refl
  go-go φ ψ tt       = refl
  go-go φ ψ (la e)   = cong la (go-go (bu φ) (bu ψ) e)
  go-go φ ψ (ap f e) = cong₂ ap (go-go φ ψ f) (go-go φ ψ e)
  go-go φ ψ (il e)   = cong il (go-go φ ψ e)
  go-go φ ψ (ir e)   = cong ir (go-go φ ψ e)
  go-go φ ψ (ca e l r) rewrite go-go φ ψ e
    = cong₂ (ca _)
        (go-go (bu φ) (bu ψ) l)
        (go-go (bu φ) (bu ψ) r)
  {-# REWRITE go-go #-}

instance
  substₜₘ : Substitutable (λ Γ → Tm Γ t)
  substₜₘ .ssub = Substitution.go
