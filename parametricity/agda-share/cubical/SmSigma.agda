{-# OPTIONS --cubical --postfix-projections #-}

module SmSigma where

open import Cubical.Core.Everything
open import Cubical.Functions.Embedding
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence

import Cubical.Foundations.Univalence.Universe as Uni

open import Cubical.Data.Nat
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation

import Cubical.Data.Empty as Empty
import Cubical.Data.Unit as Unit

open import Cubical.Relation.Nullary

variable
  ℓ ℓ' : Level
  A B C D : Type ℓ
  x : A


module IAlg where
  data Q : Type₀
  Tv : Q → Type₀

  data Q where
    ⊥ ⊤ : Q
    ⋁ : (ℕ → Q) → Q
    un : ∀(x y : Q) → Tv x ≃ Tv y → x ≡ y

  syntax ⋁ (λ n → P) = ⋁[ n ] P

  Tv ⊥ = Empty.⊥
  Tv ⊤ = Unit.Unit
  Tv (⋁ x) = ∃ ℕ (Tv ∘ x)
  Tv (un _ _ e i) = ua e i

  TvProp : ∀ x → isProp (Tv x)
  TvProp ⊥ = Empty.isProp⊥
  TvProp ⊤ = Unit.isPropUnit
  TvProp (⋁ _) p q = squash p q
  TvProp (un x y e i)
    = isOfHLevel→isOfHLevelDep 1 {A = Type₀} {B = isProp}
        (λ _ → isPropIsProp) (TvProp x) (TvProp y) (ua e) i

  open Uni Q Tv un (λ _ → refl) renaming (isEmbeddingEl to isEmbeddingTv)

  rf : ∀ x y → Tv x ≡ Tv y → x ≡ y
  rf x y = pathIso x y .Iso.inv

  Qset : isSet Q
  Qset x y = isOfHLevelRespectEquiv 1 (invEquiv path-reflection) sub
    where
    sub : isProp (Tv x ≡ Tv y)
    sub = isOfHLevel≡ 1 (TvProp x) (TvProp y)

  _⊢_ : Q → Q → Type₀
  x ⊢ y = Tv x → Tv y

  infix 3 _≅_
  _≅_ : Type₀ → Type₀ → Type₀
  A ≅ B = (A → B) × (B → A)

  open Iso

  exIso : ∀ x y → x ⊢ y → y ⊢ x → Iso (Tv x) (Tv y)
  exIso x y f g .fun = f
  exIso x y f g .inv = g
  exIso x y f g .rightInv z = TvProp y (f (g z)) z
  exIso x y f g .leftInv z = TvProp x (g (f z)) z

  ex : ∀ x y → x ⊢ y → y ⊢ x → x ≡ y
  ex x y f g = un x y (isoToEquiv (exIso x y f g))

  Q-elim₁
    : ∀{F : Q → Type ℓ}
    → (Fprp : ∀ q → isProp (F q))
    → F ⊥
    → F ⊤
    → (∀ p → (∀ n → F (p n)) → F (⋁ p))
    → ∀ q → F q
  Q-elim₁ Fprp b t j ⊥ = b
  Q-elim₁ Fprp b t j ⊤ = t
  Q-elim₁ Fprp b t j (⋁ x) = j x (Q-elim₁ Fprp b t j ∘ x)
  Q-elim₁ Fprp b t j (un q r e i)
    = isOfHLevel→isOfHLevelDep 1 Fprp eq er (un q r e) i
    where
    eq = Q-elim₁ Fprp b t j q
    er = Q-elim₁ Fprp b t j r

  Q-elim₂
    : ∀{F : Type₀ → Type ℓ}
    → (Fprp : ∀ T → isProp (F T))
    → F (Empty.⊥)
    → F (Unit.Unit)
    → (∀(T : ℕ → Type₀) → (∀ n → F (T n)) → F (∃[ n ∈ ℕ ] T n))
    → ∀ q → F (Tv q)
  Q-elim₂ {F = F} Fprp F⊥ F⊤ F∨
    = Q-elim₁ {F = F ∘ Tv} (Fprp ∘ Tv) F⊥ F⊤ (λ p → F∨ (Tv ∘ p))

  lemma : ∀ q r → isProp (Σ[ q∧r ∈ Q ] Tv q∧r ≡ Tv q × Tv r)
  lemma q r = isEmbedding→hasPropFibers isEmbeddingTv (Tv q × Tv r)

  meet : ∀ q r → Σ[ q∧r ∈ Q ] Tv q∧r ≡ Tv q × Tv r
  meet q r
    = Q-elim₁
        (λ q → lemma q r)
        (⊥ , isoToPath sublemma₀)
        (r , isoToPath sublemma₁)
        (λ p fp → λ where
            .fst → (⋁ (fst ∘ fp))
            .snd → isoToPath (sublemma₂ p (fst ∘ fp) (snd ∘ fp)))
        q
    where
    sublemma₀ : Iso Empty.⊥ (Empty.⊥ × A)
    sublemma₀ .fun ()
    sublemma₀ .inv ()
    sublemma₀ .rightInv () 
    sublemma₀ .leftInv ()

    sublemma₁ : Iso A (Unit.Unit × A)
    sublemma₁ .fun = _ ,_
    sublemma₁ .inv = snd
    sublemma₁ .rightInv _ = refl
    sublemma₁ .leftInv _ = refl

    split : isProp B → ∥ A × B ∥ → ∥ A ∥ × B
    split Bprp = rec (isProp× squash Bprp) (map-fst ∣_∣)

    merge : ∥ A ∥ × B → ∥ A × B ∥
    merge (l , r) = map (_, r) l

    assocl : ∀{P : A → Type₀} → (Σ[ x ∈ A ] P x × B) → Σ A P × B
    assocl (n , p , b) = (n , p) , b

    assocr : ∀{P : A → Type₀} → Σ A P × B → Σ[ x ∈ A ] P x × B
    assocr ((n , p) , b) = n , p , b

    sublemma₂
      : (p : ℕ → Q) 
      → (p∧r : ℕ → Q)
      → (∀ n → Tv (p∧r n) ≡ Tv (p n) × Tv r)
      → Iso (Tv (⋁ p∧r)) (Tv (⋁ p) × Tv r)
    sublemma₂ p p∧r s .fun
      = split (TvProp r) ∘ map (assocl ∘ map-snd (λ{n} → transport (s n)))
    sublemma₂ p p∧r s .inv = map (map-snd (transport⁻ (s _)) ∘ assocr) ∘ merge
    sublemma₂ p p∧r s .rightInv b = isProp× (TvProp (⋁ p)) (TvProp r) _ b
    sublemma₂ p p∧r s .leftInv a = TvProp (⋁ p∧r) _ a

  _∧Q_ : Q → Q → Q
  q ∧Q r = meet q r .fst
