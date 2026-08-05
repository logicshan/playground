{-# OPTIONS --cubical --postfix-projections #-}

module GroupoidProduct where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport

open import Cubical.Data.Nat as Nat
open import Cubical.Data.Fin as Fin

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetTruncation as ST

variable
  ℓ ℓ' : Level
  A X Y : Type ℓ
  w x y z : A
  n : ℕ

LFin : ℕ → Type ℓ
LFin n = Lift (Fin n)

Finite : ∀ ℓ → Type _
Finite ℓ = Σ[ X ∈ Type ℓ ] Σ[ n ∈ ℕ ] ∥ LFin n ≡ X ∥

FSet : ((X , _) : Finite ℓ) → isSet X
FSet (X , n , tp)
  = PT.rec isPropIsSet (λ p → transport (cong isSet p) (isOfHLevelLift 2 isSetFin)) tp

K : Type ℓ → Type ℓ → Type _
K C A = (A → C) → C

module Utils where
  tie : (p : x ≡ y) → PathP (λ k → x ≡ p k) refl p
  tie p k j = p (j ∧ k)

  raw-square : (p : x ≡ y) (q : x ≡ z) (r : y ≡ z) → (i j : I) → _
  raw-square p q r j i
    = hcomp (λ k → λ where
          (j = i1) → r i
          (i = i0) → p (~ k ∨ j)
          (i = i1) → q (~ k ∨ j))
        (r i)

  line : (p : x ≡ y) (q : x ≡ z) (r : y ≡ z) → x ≡ x
  line p q r i = raw-square p q r i0 i

  square : (p : x ≡ y) (q : x ≡ z) (r : y ≡ z) → Square (line p q r) r p q
  square p q r i j = raw-square p q r i j

  line-lemma : ∀(p : x ≡ y) → line p p refl ≡ refl
  line-lemma p k i
    = hcomp (λ j → λ where
          (i = i0) → p (~ j)
          (i = i1) → p (~ j)
          (k = i1) → p (~ j))
        (p i1)

  raw-square-lemma : (r : x ≡ x) → (k i j : I) → _
  raw-square-lemma r k j i
    = hcomp (λ _ → λ where
          (j = i1) → r i
          (i = i0) → r i0
          (i = i1) → r i1
          (k = i1) → r i)
        (r i)

  -- actual type of raw-square-lemma
  square-lemma
    : (r : x ≡ x)
    → Cube
        (square refl refl r) (λ i j → r j)
        (square refl refl r) (λ i j → r j)
        refl refl
  square-lemma r k i j = raw-square-lemma r k i j

  cube : (p q r : x ≡ y) → (i j k : I) → _
  cube {y = y} p q r i j k
    = hcomp (λ τ → λ where
          (k = i1) → y
          (j = i0) → p (k ∨ ~ τ)
          (i = i0) (j = i1) → q (k ∨ ~ τ)
          (i = i1) (j = i1) → r (k ∨ ~ τ))
        y

  tranPath : (P : I → Type ℓ) {x : P i0} → PathP P x (transp P i0 x)
  tranPath P {x} i = transp (λ k → P (i ∧ k)) (~ i) x

module SetProd
    (C : Type ℓ)
    (Cgpd : isGroupoid C)
    (F : Type ℓ)
    (FSet : isSet F)
    (Π : (F → C) → C)
    (comm : ∀(R : F ≡ F) → PathP (λ i → K C (R i)) Π Π)
    (ccoh : ∀(P Q R : F ≡ F)
          → (S : Square P R refl Q)
          → SquareP (λ i j → K C (S i j))
              (comm P) (comm R) refl (comm Q))
  where
  open 3-Constant
  open Utils

  -- action
  π : (F ≡ X) → K C X
  π P = transport (λ i → K C (P i)) Π

  π-lemma : Π ≡ π refl
  π-lemma j = transp (λ i → K C F) (~ j) Π

  -- constancy
  MT₀ : (A : I → Type ℓ) → K C (A i0) → K C (A i1) → Type _
  MT₀ A x y = PathP (λ i → K C (A i)) x y

  MT : (A : I → Type ℓ) (P : F ≡ A i0) (Q : F ≡ A i1)  → Type _
  MT A P Q = MT₀ A (π P) (π Q)

  MTr : (R : F ≡ F) → MT (λ i → R i) refl refl
  MTr R = transport (λ k → MT₀ (λ i → R i) (π-lemma k) (π-lemma k)) (comm R)

  c-π : ∀(P : F ≡ X) (Q : F ≡ Y) (R : X ≡ Y) → PathP (λ i → K C (R i)) (π P) (π Q)
  c-π P Q R
    = transport
        (λ k → MT (raw-square P Q R k) (tie P k) (tie Q k))
        (MTr (line P Q R))

  LM : ∀(R : F ≡ F) → PathP (λ j → K C (R j)) (π refl) (π refl) → Type _
  LM R z = SquareP (λ i j → K C (R j)) (comm R) z π-lemma π-lemma

  c-π-lemma₀ : ∀(R : F ≡ F) → LM R (MTr R)
  c-π-lemma₀ R = tranPath (λ k → MT₀ (λ i → R i) (π-lemma k) (π-lemma k))

  c-π-lemma₁
    : ∀ R
    → PathP (λ k → MT (raw-square refl refl R k) (tie refl k) (tie refl k))
        (MTr (line refl refl R)) (c-π refl refl R)
  c-π-lemma₁ R
    = tranPath (λ k → MT (raw-square refl refl R k) (tie refl k) (tie refl k))

  c-π-lemma₂
    : ∀(R : F ≡ F)
    → PathP (λ i → MT (raw-square refl refl R (~ i)) refl refl)
        (MTr R) (MTr (line refl refl R))
  c-π-lemma₂ R i = MTr (λ j → raw-square refl refl R (~ i) j)

  c-π-lemma₃ : ∀(R : F ≡ F) → LM R (c-π refl refl R)
  c-π-lemma₃ R i j
    = comp (λ k → K C (raw-square-lemma R k (~ i) j)) (λ k → λ where
           (j = i0) → π-lemma (~ k ∨ i)
           (i = i0) → c-π-lemma₀ R (~ k) j
           (i = i1) → c-π-lemma₁ R k j
           (j = i1) → π-lemma (~ k ∨ i))
        (med (i) j)
    where
    med = c-π-lemma₂ R

  -- coherence
  OT₀
    : {X Y Z : Type ℓ}
    → {P : X ≡ Y} {Q : Y ≡ Z} {R : X ≡ Z}
    → (S : Square P R refl Q)
    → {x : K C X} {y : K C Y} {z : K C Z}
    → (p : PathP (λ i → K C (P i)) x y)
    → (q : PathP (λ i → K C (Q i)) y z)
    → (r : PathP (λ i → K C (R i)) x z)
    → Type _
  OT₀ S p q r = SquareP (λ i j → K C (S i j)) p r refl q

  OT
    : {X Y Z : Type ℓ}
    → {P : X ≡ Y} {Q : Y ≡ Z} {R : X ≡ Z}
    → Square P R refl Q
    → (FX : F ≡ X) (FY : F ≡ Y) (FZ : F ≡ Z)
    → Type _
  OT {P = P} {Q} {R} S FX FY FZ
    = OT₀ S (c-π FX FY P) (c-π FY FZ Q) (c-π FX FZ R)

  OTr
    : {P Q R : F ≡ F}
    → (S : Square P R refl Q)
    → OT (λ i j → S i j) refl refl refl
  OTr {P} {Q} {R} S
    = transport (λ k →
          OT₀ S (c-π-lemma₃ P k) (c-π-lemma₃ Q k) (c-π-lemma₃ R k))
        (ccoh P Q R S)

  co-π : ∀(P Q R : F ≡ X) → Square (c-π P Q refl) (c-π P R refl) refl (c-π Q R refl)
  co-π P Q R
    = transport (λ k →
          OT (λ i j → cube P Q R i j k) (tie P k) (tie Q k) (tie R k))
        (OTr (λ i j → cube P Q R i j i0))

  π-3-constant : 3-Constant (π {X = X})
  π-3-constant .link P Q = c-π P Q refl
  π-3-constant .coh₁ = co-π

  module Promote (X : Type ℓ) (te : ∥ F ≡ X ∥) where
    Π̂ : (X → C) → C
    Π̂ = rec→Gpd (isOfHLevelΠ 3 (λ _ → Cgpd)) π π-3-constant te
