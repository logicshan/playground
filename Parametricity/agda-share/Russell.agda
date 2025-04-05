
open import Data.Product
open import Data.Empty

open import Relation.Nullary

-- Class is the collection of classes.
-- _∈_ is the class membership relation.
module Russell (Class : Set) (_∈_ : Class → Class → Set) where

-- A set is a class that is the element of another class.
IsSet : Class → Set
IsSet x = Σ[ X ∶ Class ] (x ∈ X)

_∉_ : Class → Class → Set
X ∉ Y = ¬ (X ∈ Y)

-- R is the class of all non-self-inclusive sets
module Hyp (R : Class)
           -- Any member of R is not a member of itself
           (def₁ : ∀ z → z ∈ R → z ∉ z)
           -- If z is a set, and z is not self-inclusive, then it is a member of R
           (def₂ : ∀ z → IsSet z → z ∉ z → z ∈ R)
  where

  lemma₁ : IsSet R → R ∉ R
  lemma₁ hyp R∈R = def₁ R R∈R R∈R

  -- R is not a set
  lemma₂ : IsSet R → ⊥
  lemma₂ hyp = lemma₁ hyp (def₂ R hyp (lemma₁ hyp))
