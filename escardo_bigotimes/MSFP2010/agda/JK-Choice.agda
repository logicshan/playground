module JK-Choice where

open import Logic
open import LogicalFacts
open import Induction
open import JK-Monads
open import Choice
open import Equality
open import JK-Shifts

------------------------------------------------------------------------
-- Proof of the J translation of the axiom of choice                  --
-- from the proof of the axiom of choice using J-∀-shift as a lemma.  --
------------------------------------------------------------------------

JR-AC-ℕ : {R : Ω} {X : ℕ → Set} {P : (n : ℕ) → X n → Ω} →
-------
           (∀(n : ℕ) → J R (∃(\(x : X n) → P n x)))
        → J R (∃(\(f : ((n : ℕ) → X n)) → ∀(n : ℕ) → P n (f n)))

JR-AC-ℕ g = (J-functor AC) (J-∀-shift g)


-----------------------------------------------------------------------
-- The K-translation of AC can be proved only for certain formulas,  --
-- including those that are in the image of the K-translation.       --
--                                                                   --
-- Hence most theorems in this part have restrictions.               --
--                                       ------------                --
--                                                                   --
-- This is because there is no general K-∀-shift.                    --
-----------------------------------------------------------------------

-- This goes in direction opposite to J-K, but is not a morphism.
-- (Preservation of the unit fails.)


K-J : {R A : Ω} → 
---
               (R → A) →            -- restriction.
               K R A → J R A        -- morphism.

K-J restriction φ = restriction ∘ φ


K-∀-shift : {R : Ω} {A : ℕ → Ω} → 
---------
            (∀(n : ℕ) → R → A n) →                         -- restriction,
            (∀(n : ℕ) → K R (A n)) → K R (∀(n : ℕ) → A n)  -- shift.

K-∀-shift restriction φs = J-K(J-∀-shift(λ n → K-J (restriction n) (φs n)))


KR-AC-ℕ : {R : Ω} {X : ℕ → Set} {P : (n : ℕ) → X n → Ω} →
-------
        (∀(n : ℕ) → R → ∃(\(m : X n) → P n m))                   -- restriction.
      → (∀(n : ℕ) → K R (∃(\(m : X n) → P n m)))                 -- premise,
      → K R (∃(\(f : ((n : ℕ) → X n)) → ∀(n : ℕ) → P n (f n)))   -- conclusion.

KR-AC-ℕ restriction g = (K-functor AC) (K-∀-shift restriction g)


----------------------------------------------
--                                          --
-- Now the translations of dependent choice --
--                                          --
----------------------------------------------


J-∀-double-shift : {R : Ω} {P : ℕ → ℕ → ℕ → Ω} →
---------------
     (∀(n : ℕ) → ∀(x : ℕ) → J R (∃(\(y : ℕ) → P n x y))) →
     J R (∀(n : ℕ) → ∀(x : ℕ) → ∃(\(y : ℕ) → P n x y))

J-∀-double-shift f = J-∀-shift(λ n → J-∀-shift (f n))


JR-DC-ℕ : {R : Ω} {P : ℕ → ℕ → ℕ → Ω} →
-------
     ∀(x₀ : ℕ) → 
     (∀(n : ℕ) → ∀(x : ℕ) → J R (∃(\(y : ℕ) → P n x y))) → 
     J R (∃(\(α : ℕ → ℕ) → α O ≡ x₀ ∧ (∀(n : ℕ) → P n (α n) (α(succ n)))))

JR-DC-ℕ x₀ f = (J-functor (DC x₀)) (J-∀-double-shift f)


K-∀-double-shift : {R : Ω} {P : ℕ → ℕ → ℕ → Ω} →
---------------
     (∀(n : ℕ) → ∀(x : ℕ) → R → ∃(\(y : ℕ) → P n x y)) →
     (∀(n : ℕ) → ∀(x : ℕ) → K R (∃(\(y : ℕ) → P n x y))) →
     K R (∀(n : ℕ) → ∀(x : ℕ) → ∃(\(y : ℕ) → P n x y))

K-∀-double-shift restriction f = 
  J-K(J-∀-double-shift(λ n x → K-J (restriction n x) (f n x)))
 

KR-DC-ℕ : {R : Ω} {P : ℕ → ℕ → ℕ → Ω} →
-------
    (∀(n : ℕ) → ∀(x : ℕ) → R → ∃(\(y : ℕ) → P n x y))
 → ∀(x₀ : ℕ) 
 → (∀(n : ℕ) → ∀(x : ℕ) → K R (∃(\(y : ℕ) → P n x y)))
 → K R (∃(\(α : ℕ → ℕ) → α O ≡ x₀ ∧ (∀(n : ℕ) → P n (α n) (α(succ n)))))

KR-DC-ℕ restriction x₀ f = (K-functor (DC x₀)) (K-∀-double-shift restriction f)
