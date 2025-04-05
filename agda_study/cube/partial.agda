{-# OPTIONS --cubical #-}

open import Cubical.Core.Primitives hiding (empty; hfill)

data Bool : Set where
  true  : Bool
  false : Bool

partialBool : ∀ i → Partial (i ∨ ~ i) Bool
partialBool i (i = i0) = false
partialBool i (i = i1) = false

φ : ∀ (i : I) → I
φ i = i ∨ ~ i

rawTerm : (i : I) → Bool
rawTerm i = false

u : (i : I) → Partial i Bool
u i = λ { (i = i1) → true }

subBool : ∀ i → Bool [ (i ∨ ~ i) ↦ partialBool i ]
subBool i = inS false
--                ∙          ∙
--                ^          ^
--               true      false

partialBool' : ∀ i → Partial (i ∨ ~ i) Bool
partialBool' i = λ where
  (i = i0) → true
  (i = i1) → false

partialBool'' : ∀ i j → Partial (~ i ∨ i ∨ (i ∧ j)) Bool
partialBool'' i j = λ where
  (i = i1)          → true
  (i = i1) (j = i1) → true
  (i = i0)          → false

--               ∙
--    |          |
--    |          |
--    |          |
--    |          |
--              
--    ^          ^
--  false       true

empty : {A : Set} → Partial i0 A
empty = λ ()

compPath : ∀ {ℓ} {A : Set ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
compPath {x = x} p q i = hcomp {φ = i ∨ ~ i} (λ{ j (i = i0) → x
                                 ; j (i = i1) → q j })
                               (p i)
{-
hfill : ∀ {ℓ} {A : Set ℓ} {φ : I}
        (u : ∀ i → Partial φ A) (u0 : A [ φ ↦ u i0 ])
        (i : I) → A
hfill {φ = φ} u u0 i = {!!}
-}

hfill : ∀ {ℓ} {A : Set ℓ} {φ : I}
        (u : ∀ i → Partial φ A) (u0 : A [ φ ↦ u i0 ])
        (i : I) → A
hfill {φ = φ} u u0 i = hcomp {φ = φ ∨ ~ i}
                             (λ{ j (φ = i1) → u (i ∧ j) 1=1
                               ; j (i = i0) → outS u0 })
                             (outS u0)

p_refl : ∀ {ℓ} {A : Set ℓ} {x y : A} (p : x ≡ y) → x ≡ y
p_refl {x = x} {y = y} p i = hcomp {φ = i ∨ ~ i}
                   (λ _ → λ { (i = i0) → x
                            ; (i = i1) → y })
                   (p i)

--  x --------- y
--  |           |
--  |           |
--  |           |
--  |           |
--  |           |
--  x --------- y
--        p

p_refl≡p : ∀ {ℓ} {A : Set ℓ} {x y : A} (p : x ≡ y) → p ≡ p_refl p
p_refl≡p {x = x} {y = y} p j i =
  hfill {φ = i ∨ ~ i}
        (λ _ → λ { (i = i0) → x
                 ; (i = i1) → y })
        (inS (p i))
        j
