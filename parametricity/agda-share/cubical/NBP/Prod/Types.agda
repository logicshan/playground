
module NBP.Prod.Types where

open import Cubical.Foundations.Function hiding (_$_)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
import Cubical.Data.Empty as Empty
open import Cubical.Data.Fin.Recursive as Fin
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Relation.Nullary

open import NBP.Facts

-- Simple types with unit, product and function
data Ty : Type where
  ⊤ β : Ty
  _*_ _⇒_ : Ty → Ty → Ty

infixr 30 _⇒_
infixr 35 _*_

instance
  Ty-IdentityCode : IdentityCode Ty ℓ-zero
  Ty-IdentityCode .Code = Co where
    Co : Ty → Ty → Type
    Co ⊤ ⊤ = Unit
    Co β β = Unit
    Co (A * B) (A' * B') = Co A A' × Co B B'
    Co (A ⇒ B) (A' ⇒ B') = Co A A' × Co B B'
    Co _ _ = Empty.⊥

  Ty-IdentityCode .isProp-Code = iP where
    iP : ∀ T U → isProp _
    iP ⊤ ⊤ = isPropUnit
    iP β β = isPropUnit
    iP (A * B) (A' * B') =
      isProp× (iP A A') (iP B B')
    iP (A ⇒ B) (A' ⇒ B') =
      isProp× (iP A A') (iP B B')
    iP ⊤ (_ * _) = Empty.isProp⊥
    iP ⊤ (_ ⇒ _) = Empty.isProp⊥
    iP β (_ * _) = Empty.isProp⊥
    iP β (_ ⇒ _) = Empty.isProp⊥
    iP (_ * _) ⊤ = Empty.isProp⊥
    iP (_ ⇒ _) ⊤ = Empty.isProp⊥
    iP (_ * _) β = Empty.isProp⊥
    iP (_ ⇒ _) β = Empty.isProp⊥
    iP (_ * _) (_ ⇒ _) = Empty.isProp⊥
    iP (_ ⇒ _) (_ * _) = Empty.isProp⊥

  Ty-IdentityCode .reflexive = rf where
    rf : _
    rf ⊤ = _
    rf β = _
    rf (A * B) = rf A , rf B
    rf (A ⇒ B) = rf A , rf B

  Ty-IdentityCode .decode = de where
    de : _
    de ⊤ ⊤ _ = refl
    de β β _ = refl
    de (A * C) (B * D) (c , d) =
      cong₂ _*_ (de A B c) (de C D d)
    de (A ⇒ C) (B ⇒ D) (c , d) =
      cong₂ _⇒_ (de A B c) (de C D d)

isSet-Ty : isSet Ty
isSet-Ty = IdentityCode→isSet

-- Simple type contexts
data Cx : Type where
  [] : Cx
  _∷_ : Cx → Ty → Cx

instance
  IdentityCode-Cx : IdentityCode Cx ℓ-zero
  IdentityCode-Cx .Code = Co where
    Co : _
    Co []      []      = Unit
    Co (Γ ∷ A) (Δ ∷ B) = Co Γ Δ × Code A B
    Co _       _       = Empty.⊥

  IdentityCode-Cx .isProp-Code = PC where
    PC : _
    PC [] [] = isPropUnit
    PC [] (Δ ∷ x) = Empty.isProp⊥
    PC (Γ ∷ A) [] = Empty.isProp⊥
    PC (Γ ∷ A) (Δ ∷ B) =
      isProp× (PC Γ Δ) (isProp-Code A B)

  IdentityCode-Cx .reflexive = rf where
    rf : _
    rf [] = _
    rf (Γ ∷ A) = rf Γ , reflexive A

  IdentityCode-Cx .decode = de where
    de : _
    de [] [] _ = refl
    de (Γ ∷ A) (Δ ∷ B) (c , d) =
      cong₂ _∷_ (de Γ Δ c) (decode A B d)

isSet-Cx : isSet Cx
isSet-Cx = IdentityCode→isSet

infixl 20 _∷_

length : Cx → ℕ
length [] = 0
length (Γ ∷ _) = suc (length Γ)

_!_ : (Γ : Cx) → Fin (length Γ) → Ty
(_ ∷ A) ! zero = A
(Γ ∷ _) ! suc n = Γ ! n

variable
  A B C D : Ty
  Γ Δ Θ Φ : Cx

infix 10 _∈_
data _∈_ : Ty → Cx → Type where
  to :         A ∈ Γ ∷ A
  po : A ∈ Γ → A ∈ Γ ∷ B

module isSet-∈ where
  _∈'_ : Ty → Cx → Type
  A ∈' Γ = Σ[ n ∈ _ ] A ≡ Γ ! n

  ∈→∈' : A ∈ Γ → A ∈' Γ
  ∈→∈' v = fs v , sn v module ∈→∈' where
    fs : A ∈ Γ → Fin (length Γ)
    fs to = zero
    fs (po v) = suc (fs v)

    sn : (v : A ∈ Γ) → A ≡ Γ ! fs v
    sn to = refl
    sn (po v) = sn v

  ∈'→∈ : A ∈' Γ → A ∈ Γ
  ∈'→∈ = uncurry go module ∈'→∈ where
    go : (n : Fin (length Γ)) → A ≡ Γ ! n → A ∈ Γ
    go {Γ ∷ A} zero    p = subst (_∈ Γ ∷ A) (sym p) to
    go {Γ ∷ A} (suc n) p = po (go n p)

  ∈→∈'→∈ : ∀(v : A ∈ Γ) → ∈'→∈ (∈→∈' v) ≡ v
  ∈→∈'→∈ v = go v where
    go : ∀(u : A ∈ Γ) → ∈'→∈.go {A} {Γ} (∈→∈'.fs v u) (∈→∈'.sn v u) ≡ u
    go {Γ = Γ ∷ A} to = substRefl {B = _∈ Γ ∷ A} to
    go (po u) = cong po (go u)

isSet-∈ : ∀ A Γ → isSet (A ∈ Γ)
isSet-∈ A Γ =
  isSetRetract ∈→∈' ∈'→∈ ∈→∈'→∈
    (isSetΣ isSetFin (λ n → isProp→isSet (isSet-Ty A (Γ ! n))))
  where open isSet-∈

-- Simple type renamings. Represented as functions
-- gives judgmental identity and associativity of
-- composition.
record Rn (Γ Δ : Cx) : Type where
  field rn-∈ : A ∈ Δ → A ∈ Γ

open Rn public

variable ρ σ τ : Rn Γ Δ

-- Empty renaming.
⟨⟩ : Rn Γ []
⟨⟩ .rn-∈ ()

-- Shift a renaming under a binder.
sh : Rn Γ Δ → Rn (Γ ∷ A) (Δ ∷ A)
sh ρ .rn-∈ to = to
sh ρ .rn-∈ (po v) = po (ρ .rn-∈ v)

-- Add a variable to a renaming.
_,,_ : Rn Γ Δ → A ∈ Γ → Rn Γ (Δ ∷ A)
(_ ,, v) .rn-∈ to = v
(ρ ,, _) .rn-∈ (po u) = ρ .rn-∈ u
infixl 20 _,,_

rn-π : Rn (Γ ∷ A) Γ
rn-π .rn-∈ v = po v

isSet-Rn : ∀ Γ Δ → isSet (Rn Γ Δ)
isSet-Rn Γ Δ ρ σ p q i j .rn-∈ =
  isSet→ (isSet-∈ _ Γ) (rn-∈ ρ) (rn-∈ σ)
    (λ k → rn-∈ (p k)) (λ k → rn-∈ (q k))
    i j

infixl 15 _rn∘_
_rn∘_ : Rn Γ Δ → Rn Δ Θ → Rn Γ Θ
(ρ rn∘ σ) .rn-∈ = rn-∈ ρ ∘ rn-∈ σ

rn-id : Rn Γ Γ
rn-id .rn-∈ v = v

sh-id : rn-id ≡ sh {Γ} {Γ} {A} rn-id
sh-id i .rn-∈ to = to
sh-id i .rn-∈ (po v) = po v

sh-∘ : (ρ : Rn Γ Δ) (σ : Rn Δ Θ) → sh ρ rn∘ sh σ ≡ sh {A = A} (ρ rn∘ σ)
sh-∘ ρ σ i .rn-∈ to = to
sh-∘ ρ σ i .rn-∈ (po v) = po (rn-∈ ρ (rn-∈ σ v))

sh-∘∘ : (ρ : Rn Γ Δ) (σ : Rn Δ Θ) (τ : Rn Θ Φ)
      → PathP (λ i → sh-∘ {A = A} ρ σ i rn∘ sh τ ≡ sh-∘ ρ (σ rn∘ τ) i)
          (cong (sh ρ rn∘_) (sh-∘ σ τ))
          (sh-∘ (ρ rn∘ σ) τ)
sh-∘∘ ρ σ τ i j .rn-∈ to = to
sh-∘∘ ρ σ τ i j .rn-∈ (po v) =
  po (ρ .rn-∈ (σ .rn-∈ (τ .rn-∈ v)))

