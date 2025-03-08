open import Level
open import Data.Empty
open import Data.Product
open Σ

module SetTheory (ℓ : Level) where

-- The type of well-founded trees with branching type from universe level ℓ
data V : Set (suc ℓ) where
  set : ∀ {I : Set ℓ} → (I → V) → V

mutual
  -- Membership relation
  infix 5 _∈_
  data _∈_ : V → V → Set (suc ℓ) where
    ∈-set : ∀ {I} {t} {u : I → V} → (Σ[ i ∈ I ] t ≈ u i) → t ∈ set u

  -- Subset relation
  infix 5 _⊆_
  _⊆_ : V → V → Set (suc ℓ)
  set x ⊆ t = ∀ i → x i ∈ t

  -- Equality of well-founded trees as sets
  infix 5 _≈_
  data _≈_ : V → V → Set (suc ℓ) where
    ≈-set : ∀ {t u : V} → t ⊆ u → u ⊆ t  → u ≈ t

-- We check that (V, ∈, ≈) satisfies the set-theoretic axioms.
-- For illustration we only provide extensionality and empty set.
-- (Note that we cannot validate the powerset axiom, Agda is too predicative.)

data empty-type : Set ℓ where

∅ : V
∅ = set {I = empty-type} λ {()}

axiom-empty-set : Σ[ x ∈ V ] ∀ (y : V) → y ∈ x → ⊥
axiom-empty-set = ∅ , λ {y (∈-set ())}

axiom-extensionality : ∀ {x y : V} → x ⊆ y → y ⊆ x → x ≈ y
axiom-extensionality x⊆y y⊆x = ≈-set y⊆x x⊆y

-- and so on
