module FreeLatticeFunctor where

open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary using (Rel; Setoid; IsEquivalence)
open import Algebra.Lattice using (Lattice)
open import Function using (id; _∘_)
open import Data.Product using (_,_)
open import Category.Category

private
  variable
    ℓ : Level

-- Free lattice term algebra
data FreeLattice (X : Set ℓ) : Set ℓ where
  η   : X → FreeLattice X
  _∧_ : FreeLattice X → FreeLattice X → FreeLattice X
  _∨_ : FreeLattice X → FreeLattice X → FreeLattice X

-- Equivalence relation encoding lattice axioms
data _≈_ {X : Set ℓ} : Rel (FreeLattice X) ℓ where
  refl        : ∀ {x} → x ≈ x
  sym         : ∀ {x y} → x ≈ y → y ≈ x
  trans       : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z
  cong-∧      : ∀ {x x′ y y′} → x ≈ x′ → y ≈ y′ → (x ∧ y) ≈ (x′ ∧ y′)
  cong-∨      : ∀ {x x′ y y′} → x ≈ x′ → y ≈ y′ → (x ∨ y) ≈ (x′ ∨ y′)
  ∧-assoc     : ∀ x y z → (x ∧ (y ∧ z)) ≈ ((x ∧ y) ∧ z)
  ∨-assoc     : ∀ x y z → (x ∨ (y ∨ z)) ≈ ((x ∨ y) ∨ z)
  ∧-comm      : ∀ x y → (x ∧ y) ≈ (y ∧ x)
  ∨-comm      : ∀ x y → (x ∨ y) ≈ (y ∨ x)
  ∧-idem      : ∀ x → (x ∧ x) ≈ x
  ∨-idem      : ∀ x → (x ∨ x) ≈ x
  absorb-∧∨   : ∀ x y → (x ∧ (x ∨ y)) ≈ x
  absorb-∨∧   : ∀ x y → (x ∨ (x ∧ y)) ≈ x

≈-isEquivalence : ∀ {X} → IsEquivalence (_≈_ {ℓ} {X})  -- IsEquivalence (_≈_ {X})
≈-isEquivalence = record
  { refl  = refl
  ; sym   = sym
  ; trans = trans
  }

-- Free lattice as a setoid with lattice structure
freeLatticeSetoid : (X : Set ℓ) → Setoid ℓ ℓ
freeLatticeSetoid X = record
  { Carrier       = FreeLattice X
  ; _≈_           = _≈_
  ; isEquivalence = ≈-isEquivalence
  }

freeLattice : (X : Set ℓ) → Lattice ℓ ℓ
freeLattice X = record
  { Carrier = FreeLattice X
  ; _≈_     = _≈_
  ; _∨_     = _∨_
  ; _∧_     = _∧_
  ; isLattice = record
    { isEquivalence = ≈-isEquivalence
    ; ∨-comm        = ∨-comm
    ; ∨-assoc       = λ x y z → sym (∨-assoc x y z)
    ; ∨-cong        = cong-∨
    ; ∧-comm        = ∧-comm
    ; ∧-assoc       = λ x y z → sym (∧-assoc x y z)
    ; ∧-cong        = cong-∧
    ; absorptive    = (absorb-∨∧ , absorb-∧∨)
    }
  }
{-
module _ where
  open Category
  open Functor

  FreeLatticeF : Functor 
  act FreeLatticeF X = {!!}
  fmap FreeLatticeF = {!!}
  identity FreeLatticeF = {!!}
  homomorphism FreeLatticeF = {!!}
-}
-- Lifting functions to lattice homomorphisms
lift : {X Y : Set ℓ} → (X → Y) → FreeLattice X → FreeLattice Y
lift f (η x)    = η (f x)
lift f (a ∧ b)  = lift f a ∧ lift f b
lift f (a ∨ b)  = lift f a ∨ lift f b

-- Lift respects equivalence
lift-cong : {X Y : Set ℓ} (f : X → Y) → ∀ {a b} → a ≈ b → lift f a ≈ lift f b
lift-cong f refl                 = refl
lift-cong f (sym eq)             = sym (lift-cong f eq)
lift-cong f (trans eq₁ eq₂)      = trans (lift-cong f eq₁) (lift-cong f eq₂)
lift-cong f (cong-∧ eq₁ eq₂)     = cong-∧ (lift-cong f eq₁) (lift-cong f eq₂)
lift-cong f (cong-∨ eq₁ eq₂)     = cong-∨ (lift-cong f eq₁) (lift-cong f eq₂)
lift-cong f (∧-assoc x y z)      = ∧-assoc (lift f x) (lift f y) (lift f z)
lift-cong f (∨-assoc x y z)      = ∨-assoc (lift f x) (lift f y) (lift f z)
lift-cong f (∧-comm x y)         = ∧-comm (lift f x) (lift f y)
lift-cong f (∨-comm x y)         = ∨-comm (lift f x) (lift f y)
lift-cong f (∧-idem x)           = ∧-idem (lift f x)
lift-cong f (∨-idem x)           = ∨-idem (lift f x)
lift-cong f (absorb-∧∨ x y)      = absorb-∧∨ (lift f x) (lift f y)
lift-cong f (absorb-∨∧ x y)      = absorb-∨∧ (lift f x) (lift f y)

-- Functorial properties
lift-id : ∀ {X} (a : FreeLattice {ℓ} X) → lift id a ≈ a
lift-id (η x)    = refl
lift-id (a ∧ b)  = cong-∧ (lift-id a) (lift-id b)
lift-id (a ∨ b)  = cong-∨ (lift-id a) (lift-id b)

lift-comp : ∀ {X Y Z} (f : X → Y) (g : Y → Z) (a : FreeLattice {ℓ} X) →
            lift (g ∘ f) a ≈ lift g (lift f a)
lift-comp f g (η x)    = refl
lift-comp f g (a ∧ b)  = cong-∧ (lift-comp f g a) (lift-comp f g b)
lift-comp f g (a ∨ b)  = cong-∨ (lift-comp f g a) (lift-comp f g b)
