module MinimalSetoid where

open import Relation.Binary using (Setoid; IsEquivalence)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)

-- A simple 2-element type
data Two : Set where
  a b : Two

-- Custom equivalence: "a ≈ a" and "b ≈ b" are true; others false
_≈_ : Two → Two → Set
a ≈ a = ⊤  -- "True" (trivial)
a ≈ b = ⊥  -- "False"
b ≈ a = ⊥
b ≈ b = ⊤

-- Prove equivalence properties
≈-refl : ∀ {x} → x ≈ x
≈-refl {a} = _  -- Fills ⊤
≈-refl {b} = _

≈-sym : ∀ {x y} → x ≈ y → y ≈ x
≈-sym {a} {a} _ = _  -- Symmetry for a ≈ a
≈-sym {b} {b} _ = _  -- Symmetry for b ≈ b

≈-trans : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z
≈-trans {a} {a} {a} _ _ = _  -- Transitivity for a ≈ a ≈ a
≈-trans {b} {b} {b} _ _ = _  -- Transitivity for b ≈ b ≈ b

-- Bundle into a Setoid
TwoSetoid : Setoid _ _
TwoSetoid = record
  { Carrier = Two
  ; _≈_ = _≈_
  ; isEquivalence = record
    { refl  = ≈-refl
    ; sym   = ≈-sym
    ; trans = ≈-trans
    }
  }
