{-# OPTIONS --cubical --postfix-projections #-}

module BoolSet where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Cubical.Data.Bool

open import Cubical.Data.Empty as Empty
open import Cubical.Data.Unit as Unit

private
  variable
    ℓ : Level
    A B C : Type ℓ
    w x y z : A
    p q : x ≡ y

  code : (x y : Bool) → Type₀
  code false false = Unit
  code true  true  = Unit
  code _     _     = ⊥

  code-refl : code x x
  code-refl {false} = _
  code-refl {true}  = _

  decode : ∀ x y → code x y → x ≡ y
  decode false false _ = refl
  decode true  true  _ = refl

  encode : ∀ x y → x ≡ y → code x y
  encode _ _ p = transport (λ i → code (p i0) (p i)) code-refl

  tie : (p : x ≡ y) → PathP (λ i → x ≡ p i) refl p
  tie p i j = p (i ∧ j)

  de-en-refl : ∀ x → decode x x (encode x x refl) ≡ refl
  de-en-refl false = refl
  de-en-refl true  = refl

  de-en : ∀ x y p → decode x y (encode x y p) ≡ p
  de-en x y p
    = transport (λ j → decode x (p j) (encode x (p j) (tie p j)) ≡ tie p j) (de-en-refl x)

  code-prop : ∀ x y → isProp (code x y)
  code-prop false false = isPropUnit
  code-prop true true = isPropUnit

Bset : isSet Bool
Bset x y p q i
  = hcomp (λ k → λ where
        (i = i0) → de-en x y p k
        (i = i1) → de-en x y q k)
      (decode x y (code-prop x y (encode x y p) (encode x y q) i))

