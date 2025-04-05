{-# OPTIONS --cubical --postfix-projections #-}

module UU where

open import Cubical.Core.Everything
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence

import Cubical.Foundations.Univalence.Universe as Uni

open import Cubical.Data.Nat
open import Cubical.HITs.PropositionalTruncation

import Cubical.Data.Empty as Empty
import Cubical.Data.Unit as Unit

variable
  ℓ : Level
  A : Type ℓ
  x : A

reg : transport (λ _ → A) ≡ idfun A
reg {A = A} i x = transp (λ _ → A) i x


module UU where
  data U : Type₀
  El : U → Type₀

  data U where
    un : ∀ x y → El x ≃ El y → x ≡ y

  El (un _ _ e i) = ua e i

  nu : ∀ x y → x ≡ y → El x ≃ El y
  nu x y p .fst = transport (cong El p)
  nu x y p .snd = isEquivTransport (cong El p)

  nu-un : ∀ x y (e : El x ≃ El y) → nu x y (un x y e) ≡ e
  nu-un x y e = equivEq (nu x y (un x y e)) e λ i z → uaβ e z i

  ua-equiv : ∀ x i → ua (idEquiv (El x)) i ≃ El x
  ua-equiv x i = λ where
      .fst → transp (λ j → p j) (i ∨ ~ i)
      .snd → transp (λ j → isEquiv (transp (λ k → p (j ∧ k)) (~ j ∨ i ∨ ~ i)))
               (i ∨ ~ i) (idIsEquiv T)
    where
    T = ua (idEquiv (El x)) i
    p : T ≡ El x
    p j = uaIdEquiv {A = El x} j i

  un-refl : ∀ x → un x x (idEquiv (El x)) ≡ refl
  un-refl x i j
    = hcomp (λ k → λ where
          (i = i0) → un x x (idEquiv (El x)) j
          (i = i1) → un x x (idEquiv (El x)) (j ∨ k)
          (j = i0) → un x x (idEquiv (El x)) (~ i ∨ k)
          (j = i1) → x)
        (un (un x x (idEquiv (El x)) (~ i)) x (ua-equiv x (~ i)) j)

  nu-refl : ∀ x → nu x x refl ≡ idEquiv (El x)
  nu-refl x = equivEq (nu x x refl) (idEquiv (El x)) reg

  un-nu : ∀ x y (p : x ≡ y) → un x y (nu x y p) ≡ p
  un-nu x y p
    = J (λ z q → un x z (nu x z q) ≡ q) (cong (un x x) (nu-refl x) ∙ un-refl x) p

  minivalence : ∀ x y → (x ≡ y) ≃ (El x ≃ El y)
  minivalence x y = isoToEquiv mini
    where
    open Iso
    mini : Iso (x ≡ y) (El x ≃ El y)
    mini .fun = nu x y
    mini .inv = un x y
    mini .rightInv = nu-un x y
    mini .leftInv = un-nu x y
