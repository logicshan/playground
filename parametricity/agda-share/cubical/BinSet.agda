{-# OPTIONS --cubical --postfix-projections #-}

module BinSet where

open import Cubical.Core.Everything
open import Cubical.Functions.Embedding
open import Cubical.Functions.Involution
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence

open import Cubical.Data.Bool hiding (isSetBool)
open import Cubical.Data.Sigma

import Cubical.Data.Empty as Empty
import Cubical.Data.Unit as Unit

open import Cubical.HITs.PropositionalTruncation

BIN : Type₁
BIN = Σ[ B ∈ Type₀ ] ∥ B ≡ Bool ∥

incl : BIN → hSet _
incl (B , _) .fst = B
incl (_ , tp) .snd
  = rec isPropIsSet (λ p → transport (λ i → isSet (p (~ i))) Bset) tp
  where
  open import BoolSet

isSetIsPropDep : isOfHLevelDep 1 (isSet {ℓ = ℓ-zero})
isSetIsPropDep = isOfHLevel→isOfHLevelDep 1 (λ A → isPropIsSet {A = A})

dsquash : isOfHLevelDep 1 λ A → ∥ A ≡ Bool ∥ 
dsquash = isOfHLevel→isOfHLevelDep 1 (λ _ → squash)

Σ≡Prop²
  : ∀{ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
  → {w x : Σ A B}
  → isOfHLevelDep 1 B
  → (p q : w ≡ x)
  → cong fst p ≡ cong fst q
  → p ≡ q
Σ≡Prop² Bprp p q r i j .fst = r i j
Σ≡Prop² {B = B} {w} {x} Bprp p q r i j .snd
  = isPropDep→isSetDep Bprp (w .snd) (x .snd) (cong snd p) (cong snd q) r i j

inclIsEmbedding : isEmbedding incl
inclIsEmbedding w x = isoToIsEquiv theIso
  where
  open Iso
  theIso : Iso (w ≡ x) (incl w ≡ incl x)
  theIso .fun = cong incl
  theIso .inv p i
    = p i .fst , dsquash (w .snd) (x .snd) (λ i → p i .fst) i
  theIso .rightInv p = Σ≡Prop² isSetIsPropDep _ p refl
  theIso .leftInv p = Σ≡Prop² dsquash _ p refl

isGroupoidBIN : isGroupoid BIN
isGroupoidBIN
  = Embedding-into-hLevel→hLevel 2
      (incl , isEmbedding→hasPropFibers inclIsEmbedding)
      (isOfHLevelTypeOfHLevel 2)

data 𝔹 : Type₀
El : 𝔹 → Type₀

data 𝔹 where
  ℕ₂ : 𝔹
  un : ∀ x y → El x ≃ El y → x ≡ y

El ℕ₂ = Bool
El (un x y e i) = ua e i

open import Cubical.Foundations.Univalence.Universe 𝔹 El un (λ _ → refl)

module Binary where
  isBinary : ∀ b → ∥ El b ≡ Bool ∥
  isBinary ℕ₂ = ∣ refl ∣
  isBinary (un b c e i)
    = squash
        (transp (λ j → ∥ ua e (i ∧ j) ≡ Bool ∥) (~ i) (isBinary b))
        (transp (λ j → ∥ ua e (i ∨ ~ j) ≡ Bool ∥) i (isBinary c))
        i

  big : 𝔹 → BIN
  big b = El b , isBinary b

  lemma : ∀ B → ∥ B ≡ Bool ∥ → Σ[ b ∈ 𝔹 ] El b ≡ B
  lemma B = rec (isEmbedding→hasPropFibers isEmbeddingEl B) (_,_ ℕ₂ ∘ sym)

  small : BIN → 𝔹
  small (B , tp) = lemma B tp .fst

  big-small : ∀ p → big (small p) ≡ p
  big-small (B , tp) = ΣPathP (b≡B , dsquash (isBinary b) tp b≡B)
    where
    b = small (B , tp)
    b≡B = lemma B tp .snd

  small-big : ∀ b → small (big b) ≡ b
  small-big b = pathIso _ _ .Iso.inv (lemma (El b) (isBinary b) .snd)

  open Iso
  reflectIso : Iso 𝔹 BIN
  reflectIso .fun = big
  reflectIso .inv = small
  reflectIso .rightInv = big-small
  reflectIso .leftInv = small-big

  loop : ℕ₂ ≡ ℕ₂
  loop = un ℕ₂ ℕ₂ notEquiv

  -- loop² : Square loop refl refl loop
  -- loop² i j = un ℕ₂ (loop j) {!!} {!i!}

  -- 𝔹gpd : isGroupoid 𝔹
  -- 𝔹gpd = {!!}

data ℍ : Type₀ where
  base : ℍ
  loop : base ≡ base
  loop² : Square loop refl refl loop
  trunc : isGroupoid ℍ

module Hinary where
  variable
    ℓ : Level
    A B : Type ℓ
    x y z : A

  rec-ℍ
    : (x : A)
    → (p : x ≡ x)
    → (sq : Square p refl refl p)
    → isGroupoid A
    → ℍ → A
  rec-ℍ x p sq Agpd = go
    where
    go : ℍ → _
    go base = x
    go (loop i) = p i
    go (loop² i j) = sq i j
    go (trunc x y p q r s i j k)
      = Agpd
          (go x) (go y)
          (cong go p) (cong go q)
          (cong (cong go) r) (cong (cong go) s)
          i j k

  open import BoolSet

  nEq : Bool ≡ Bool
  nEq = involPath {f = not} notnot

  notPathSet : PathP (λ i → isSet (nEq i)) Bset Bset
  notPathSet = isSetIsPropDep Bset Bset nEq

  notNotPath : Square nEq refl refl nEq
  notNotPath = involPath² notnot

  notNotPathSet
    : SquareP (λ i j → isSet (notNotPath i j)) notPathSet refl refl notPathSet
  notNotPathSet
    = isPropDep→isSetDep' isSetIsPropDep notNotPath
        notPathSet refl refl notPathSet

  hSet₀ : Type₁
  hSet₀ = hSet ℓ-zero

  Code : ℍ → hSet₀
  Code =
    rec-ℍ
      (Bool , Bset)
      (λ i → nEq i , notPathSet i)
      (λ i j → notNotPath i j , notNotPathSet i j)
      (isOfHLevelTypeOfHLevel 2)

  nEqCoh : PathP (λ i → ∥ nEq i ≡ Bool ∥) ∣ refl ∣ ∣ refl ∣
  nEqCoh i = dsquash ∣ refl ∣ ∣ refl ∣ nEq i

  nEqCoh² : SquareP (λ i j → ∥ notNotPath i j ≡ Bool ∥) nEqCoh refl refl nEqCoh
  nEqCoh²
    = isPropDep→isSetDep' dsquash notNotPath nEqCoh refl refl nEqCoh

  large : ℍ → BIN
  large =
    rec-ℍ
      (Bool , ∣ refl ∣)
      (λ i → nEq i , nEqCoh i)
      (λ i j → notNotPath i j , nEqCoh² i j)
      isGroupoidBIN

  HEl : ℍ → Type₀
  HEl h = Code h .fst

  Hair : Type₀ → Type₀
  Hair A = Σ[ h ∈ ℍ ] (HEl h → A)

  -- bin : ℍ → 𝔹
  -- bin base = ℕ₂
  -- bin (loop i) = Binary.loop i
  -- bin (loop² i j) = Binary.loop² i j
  -- bin (trunc x y p q r s i j k)
  --   = Binary.𝔹gpd (bin x) (bin y)
  --       (λ i → bin (p i)) (λ i → bin (q i))
  --       (λ i j → bin (r i j)) (λ i j → bin (s i j))
  --       i j k
