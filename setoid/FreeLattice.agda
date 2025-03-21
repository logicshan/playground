module FreeLattice where

open import Agda.Primitive
open import Data.Product hiding (map)
open import Relation.Binary hiding (Setoid)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Level renaming (suc to lsuc; zero to lzero)
open import Data.Sum hiding (map)
open import Function
open import Relation.Nullary
open import Relation.Binary.Structures

-- Define setoid for working with equivalence classes
record Setoid c ℓ : Set (lsuc (c ⊔ ℓ)) where
  infix 4 _≈_
  field
    Carrier : Set c
    _≈_ : Rel Carrier ℓ
    isEquivalence : IsEquivalence _≈_

  reflexive : ∀ {x y} → x ≡ y → x ≈ y
  reflexive refl = IsEquivalence.refl isEquivalence

-- Basic lattice definition with setoid carrier
record Lattice c ℓ : Set (lsuc (c ⊔ ℓ)) where
  field
    setoid : Setoid c ℓ
    _∨_ : Setoid.Carrier setoid → Setoid.Carrier setoid → Setoid.Carrier setoid
    _∧_ : Setoid.Carrier setoid → Setoid.Carrier setoid → Setoid.Carrier setoid
    
  open Setoid setoid public
  
  field
    -- Congruence properties
    ∨-cong : ∀ {x y u v} → x ≈ y → u ≈ v → (x ∨ u) ≈ (y ∨ v)
    ∧-cong : ∀ {x y u v} → x ≈ y → u ≈ v → (x ∧ u) ≈ (y ∧ v)
    
    -- Lattice laws
    ∨-comm : ∀ x y → (x ∨ y) ≈ (y ∨ x)
    ∨-assoc : ∀ x y z → (x ∨ (y ∨ z)) ≈ ((x ∨ y) ∨ z)
    ∧-comm : ∀ x y → (x ∧ y) ≈ (y ∧ x)
    ∧-assoc : ∀ x y z → (x ∧ (y ∧ z)) ≈ ((x ∧ y) ∧ z)
    
    -- Absorption laws
    absorb1 : ∀ x y → (x ∨ (x ∧ y)) ≈ x
    absorb2 : ∀ x y → (x ∧ (x ∨ y)) ≈ x

-- Lattice homomorphism
record LatticeHom {c₁ ℓ₁ c₂ ℓ₂} (L₁ : Lattice c₁ ℓ₁) (L₂ : Lattice c₂ ℓ₂) : 
                  Set (c₁ ⊔ ℓ₁ ⊔ c₂ ⊔ ℓ₂) where
  private
    module L₁ = Lattice L₁
    module L₂ = Lattice L₂
    
  field
    map : L₁.Carrier → L₂.Carrier
    map-cong : ∀ {x y} → L₁._≈_ x y → L₂._≈_ (map x) (map y)
    map-∨ : ∀ x y → L₂._≈_ (map (L₁._∨_ x y)) (L₂._∨_ (map x) (map y))
    map-∧ : ∀ x y → L₂._≈_ (map (L₁._∧_ x y)) (L₂._∧_ (map x) (map y))

-- Free lattice expressions
data LatticeExpr {c} (A : Set c) : Set c where
  var : A → LatticeExpr A
  _∨E_ : LatticeExpr A → LatticeExpr A → LatticeExpr A
  _∧E_ : LatticeExpr A → LatticeExpr A → LatticeExpr A

-- Define propositional equality for expressions (structural equality)
data _≡E_ {c} {A : Set c} : LatticeExpr A → LatticeExpr A → Set c where
  ≡var : ∀ {a} → var a ≡E var a
  ≡∨ : ∀ {e₁ e₂ e₃ e₄} → e₁ ≡E e₃ → e₂ ≡E e₄ → (e₁ ∨E e₂) ≡E (e₃ ∨E e₄)
  ≡∧ : ∀ {e₁ e₂ e₃ e₄} → e₁ ≡E e₃ → e₂ ≡E e₄ → (e₁ ∧E e₂) ≡E (e₃ ∧E e₄)

-- Reflexivity, symmetry, and transitivity of ≡E
reflE : ∀ {c} {A : Set c} {e : LatticeExpr A} → e ≡E e
reflE {e = var _} = ≡var
reflE {e = e₁ ∨E e₂} = ≡∨ reflE reflE
reflE {e = e₁ ∧E e₂} = ≡∧ reflE reflE

symE : ∀ {c} {A : Set c} {e₁ e₂ : LatticeExpr A} → e₁ ≡E e₂ → e₂ ≡E e₁
symE ≡var = ≡var
symE (≡∨ p q) = ≡∨ (symE p) (symE q)
symE (≡∧ p q) = ≡∧ (symE p) (symE q)

transE : ∀ {c} {A : Set c} {e₁ e₂ e₃ : LatticeExpr A} → e₁ ≡E e₂ → e₂ ≡E e₃ → e₁ ≡E e₃
transE ≡var ≡var = ≡var
transE (≡∨ p₁ q₁) (≡∨ p₂ q₂) = ≡∨ (transE p₁ p₂) (transE q₁ q₂)
transE (≡∧ p₁ q₁) (≡∧ p₂ q₂) = ≡∧ (transE p₁ p₂) (transE q₁ q₂)

-- Lattice equivalence relation for expressions
data _≈E_ {c} {A : Set c} : LatticeExpr A → LatticeExpr A → Set c where
  -- Basic structural equality
  ≈base : ∀ {e₁ e₂} → e₁ ≡E e₂ → e₁ ≈E e₂
  
  -- Reflexivity, symmetry, transitivity
  ≈refl : ∀ {e} → e ≈E e
  ≈sym : ∀ {e₁ e₂} → e₁ ≈E e₂ → e₂ ≈E e₁
  ≈trans : ∀ {e₁ e₂ e₃} → e₁ ≈E e₂ → e₂ ≈E e₃ → e₁ ≈E e₃
  
  -- Congruence
  ≈∨-cong : ∀ {e₁ e₂ e₃ e₄} → e₁ ≈E e₃ → e₂ ≈E e₄ → (e₁ ∨E e₂) ≈E (e₃ ∨E e₄)
  ≈∧-cong : ∀ {e₁ e₂ e₃ e₄} → e₁ ≈E e₃ → e₂ ≈E e₄ → (e₁ ∧E e₂) ≈E (e₃ ∧E e₄)
  
  -- Lattice laws
  ≈∨-comm : ∀ e₁ e₂ → (e₁ ∨E e₂) ≈E (e₂ ∨E e₁)
  ≈∨-assoc : ∀ e₁ e₂ e₃ → (e₁ ∨E (e₂ ∨E e₃)) ≈E ((e₁ ∨E e₂) ∨E e₃)
  ≈∧-comm : ∀ e₁ e₂ → (e₁ ∧E e₂) ≈E (e₂ ∧E e₁)
  ≈∧-assoc : ∀ e₁ e₂ e₃ → (e₁ ∧E (e₂ ∧E e₃)) ≈E ((e₁ ∧E e₂) ∧E e₃)
  
  -- Absorption laws
  ≈absorb1 : ∀ e₁ e₂ → (e₁ ∨E (e₁ ∧E e₂)) ≈E e₁
  ≈absorb2 : ∀ e₁ e₂ → (e₁ ∧E (e₁ ∨E e₂)) ≈E e₁

-- Proof that ≈E is an equivalence relation
≈E-isEquivalence : ∀ {c} {A : Set c} → IsEquivalence (_≈E_ {c} {A})
≈E-isEquivalence = record {
  refl = ≈refl ;
  sym = ≈sym ;
  trans = ≈trans
  }

-- Free lattice as a setoid
FreeLatticeSetoid : ∀ {c} → Set c → Setoid c c
FreeLatticeSetoid A = record {
  Carrier = LatticeExpr A ;
  _≈_ = _≈E_ ;
  isEquivalence = ≈E-isEquivalence
  }

-- Free lattice as a lattice structure
FreeLattice : ∀ {c} → Set c → Lattice c c
FreeLattice A = record {
  setoid = FreeLatticeSetoid A ;
  _∨_ = _∨E_ ;
  _∧_ = _∧E_ ;
  ∨-cong = ≈∨-cong ;
  ∧-cong = ≈∧-cong ;
  ∨-comm = ≈∨-comm ;
  ∨-assoc = ≈∨-assoc ;
  ∧-comm = ≈∧-comm ;
  ∧-assoc = ≈∧-assoc ;
  absorb1 = ≈absorb1 ;
  absorb2 = ≈absorb2
  }

-- Functor map for free lattice
mapFreeLattice : ∀ {c₁ c₂} {A : Set c₁} {B : Set c₂} → 
                (A → B) → LatticeExpr A → LatticeExpr B
mapFreeLattice f (var x) = var (f x)
mapFreeLattice f (e₁ ∨E e₂) = mapFreeLattice f e₁ ∨E mapFreeLattice f e₂
mapFreeLattice f (e₁ ∧E e₂) = mapFreeLattice f e₁ ∧E mapFreeLattice f e₂

-- Prove that mapFreeLattice preserves the equivalence relation
mapFreeLattice-cong : ∀ {c₁ c₂} {A : Set c₁} {B : Set c₂} {e₁ e₂ : LatticeExpr A} →
                     (f : A → B) → e₁ ≈E e₂ → mapFreeLattice f e₁ ≈E mapFreeLattice f e₂
mapFreeLattice-cong f (≈base (≡var {a})) = ≈base ≡var
mapFreeLattice-cong f (≈base (≡∨ p q)) = 
  ≈base (≡∨ (≡E-helper f p) (≡E-helper f q))
  where
    ≡E-helper : ∀ {c₁ c₂} {A : Set c₁} {B : Set c₂} {e₁ e₂ : LatticeExpr A} →
               (f : A → B) → e₁ ≡E e₂ → mapFreeLattice f e₁ ≡E mapFreeLattice f e₂
    ≡E-helper f ≡var = ≡var
    ≡E-helper f (≡∨ p q) = ≡∨ (≡E-helper f p) (≡E-helper f q)
    ≡E-helper f (≡∧ p q) = ≡∧ (≡E-helper f p) (≡E-helper f q)
mapFreeLattice-cong f (≈base (≡∧ p q)) = 
  ≈base (≡∧ (≡E-helper f p) (≡E-helper f q))
  where
    ≡E-helper : ∀ {c₁ c₂} {A : Set c₁} {B : Set c₂} {e₁ e₂ : LatticeExpr A} →
               (f : A → B) → e₁ ≡E e₂ → mapFreeLattice f e₁ ≡E mapFreeLattice f e₂
    ≡E-helper f ≡var = ≡var
    ≡E-helper f (≡∨ p q) = ≡∨ (≡E-helper f p) (≡E-helper f q)
    ≡E-helper f (≡∧ p q) = ≡∧ (≡E-helper f p) (≡E-helper f q)
mapFreeLattice-cong f ≈refl = ≈refl
mapFreeLattice-cong f (≈sym p) = ≈sym (mapFreeLattice-cong f p)
mapFreeLattice-cong f (≈trans p q) = ≈trans (mapFreeLattice-cong f p) (mapFreeLattice-cong f q)
mapFreeLattice-cong f (≈∨-cong p q) = ≈∨-cong (mapFreeLattice-cong f p) (mapFreeLattice-cong f q)
mapFreeLattice-cong f (≈∧-cong p q) = ≈∧-cong (mapFreeLattice-cong f p) (mapFreeLattice-cong f q)
mapFreeLattice-cong f (≈∨-comm e₁ e₂) = ≈∨-comm (mapFreeLattice f e₁) (mapFreeLattice f e₂)
mapFreeLattice-cong f (≈∨-assoc e₁ e₂ e₃) = 
  ≈∨-assoc (mapFreeLattice f e₁) (mapFreeLattice f e₂) (mapFreeLattice f e₃)
mapFreeLattice-cong f (≈∧-comm e₁ e₂) = ≈∧-comm (mapFreeLattice f e₁) (mapFreeLattice f e₂)
mapFreeLattice-cong f (≈∧-assoc e₁ e₂ e₃) = 
  ≈∧-assoc (mapFreeLattice f e₁) (mapFreeLattice f e₂) (mapFreeLattice f e₃)
mapFreeLattice-cong f (≈absorb1 e₁ e₂) = ≈absorb1 (mapFreeLattice f e₁) (mapFreeLattice f e₂)
mapFreeLattice-cong f (≈absorb2 e₁ e₂) = ≈absorb2 (mapFreeLattice f e₁) (mapFreeLattice f e₂)

-- Create free lattice functor by bundling together mapFreeLattice and its properties
FreeLatticeHom : ∀ {c₁ c₂} {A : Set c₁} {B : Set c₂} →
                (A → B) → LatticeHom (FreeLattice A) (FreeLattice B)
FreeLatticeHom f = record {
  map = mapFreeLattice f ;
  map-cong = mapFreeLattice-cong f ;
  map-∨ = λ _ _ → ≈refl ;
  map-∧ = λ _ _ → ≈refl
  }

-- Functor laws for mapFreeLattice
map-id : ∀ {c} {A : Set c} → (x : LatticeExpr A) → mapFreeLattice id x ≡E x
map-id (var x) = ≡var
map-id (e₁ ∨E e₂) = ≡∨ (map-id e₁) (map-id e₂)
map-id (e₁ ∧E e₂) = ≡∧ (map-id e₁) (map-id e₂)

map-comp : ∀ {c₁ c₂ c₃} {A : Set c₁} {B : Set c₂} {C : Set c₃} 
         → (f : A → B) → (g : B → C) → (x : LatticeExpr A) 
         → mapFreeLattice (g ∘ f) x ≡E mapFreeLattice g (mapFreeLattice f x)
map-comp f g (var x) = ≡var
map-comp f g (e₁ ∨E e₂) = ≡∨ (map-comp f g e₁) (map-comp f g e₂)
map-comp f g (e₁ ∧E e₂) = ≡∧ (map-comp f g e₁) (map-comp f g e₂)

-- Unit of the adjunction (embedding)
η : ∀ {c} {A : Set c} → A → LatticeExpr A
η = var

-- Extend a function to a lattice homomorphism
extend : ∀ {c₁ c₂ ℓ₂} {A : Set c₁} {B : Set c₂} → 
        (L : Lattice c₂ ℓ₂) → (A → Lattice.Carrier L) → LatticeExpr A → Lattice.Carrier L
extend L f (var x) = f x
extend L f (e₁ ∨E e₂) = Lattice._∨_ L (extend L f e₁) (extend L f e₂)
extend L f (e₁ ∧E e₂) = Lattice._∧_ L (extend L f e₁) (extend L f e₂)

-- Prove that extend preserves the equivalence relation
extend-cong : ∀ {c₁ c₂ ℓ₂} {A : Set c₁} {B : Set c₂} → 
             (L : Lattice c₂ ℓ₂) → (f : A → Lattice.Carrier L) → 
             {e₁ e₂ : LatticeExpr A} → e₁ ≈E e₂ → 
             Lattice._≈_ L (extend L f e₁) (extend L f e₂)
extend-cong L f (≈base ≡var) = Lattice.isEquivalence.refl (Lattice.setoid L)
extend-cong L f (≈base (≡∨ p q)) = 
  Lattice.∨-cong L (extend-cong L f (≈base p)) (extend-cong L f (≈base q))
extend-cong L f (≈base (≡∧ p q)) = 
  Lattice.∧-cong L (extend-cong L f (≈base p)) (extend-cong L f (≈base q))
extend-cong L f ≈refl = Lattice.isEquivalence.refl (Lattice.setoid L)
extend-cong L f (≈sym p) = Lattice.isEquivalence.sym (Lattice.setoid L) (extend-cong L f p)
extend-cong L f (≈trans p q) = 
  Lattice.isEquivalence.trans (Lattice.setoid L) (extend-cong L f p) (extend-cong L f q)
extend-cong L f (≈∨-cong p q) = 
  Lattice.∨-cong L (extend-cong L f p) (extend-cong L f q)
extend-cong L f (≈∧-cong p q) = 
  Lattice.∧-cong L (extend-cong L f p) (extend-cong L f q)
extend-cong L f (≈∨-comm e₁ e₂) = Lattice.∨-comm L (extend L f e₁) (extend L f e₂)
extend-cong L f (≈∨-assoc e₁ e₂ e₃) = 
  Lattice.∨-assoc L (extend L f e₁) (extend L f e₂) (extend L f e₃)
extend-cong L f (≈∧-comm e₁ e₂) = Lattice.∧-comm L (extend L f e₁) (extend L f e₂)
extend-cong L f (≈∧-assoc e₁ e₂ e₃) = 
  Lattice.∧-assoc L (extend L f e₁) (extend L f e₂) (extend L f e₃)
extend-cong L f (≈absorb1 e₁ e₂) = Lattice.absorb1 L (extend L f e₁) (extend L f e₂)
extend-cong L f (≈absorb2 e₁ e₂) = Lattice.absorb2 L (extend L f e₁) (extend L f e₂)

-- Create a proper lattice homomorphism from extend
extendHom : ∀ {c₁ c₂ ℓ₂} {A : Set c₁} {B : Set c₂} → 
           (L : Lattice c₂ ℓ₂) → (f : A → Lattice.Carrier L) → 
           LatticeHom (FreeLattice A) L
extendHom L f = record {
  map = extend L f ;
  map-cong = extend-cong L f ;
  map-∨ = λ _ _ → Lattice.isEquivalence.refl (Lattice.setoid L) ;
  map-∧ = λ _ _ → Lattice.isEquivalence.refl (Lattice.setoid L)
  }

-- Universal property: (η ∘ f) = (extendHom L f) ∘ η
universal-η : ∀ {c₁ c₂ ℓ₂} {A : Set c₁} {B : Set c₂} → 
             (L : Lattice c₂ ℓ₂) → (f : A → Lattice.Carrier L) → 
             (a : A) → 
             Lattice._≈_ L (extend L f (η a)) (f a)
universal-η L f a = Lattice.isEquivalence.refl (Lattice.setoid L)

-- Universal property: uniqueness of extend
universal-unique : ∀ {c₁ c₂ ℓ₂} {A : Set c₁} {B : Set c₂} → 
                  (L : Lattice c₂ ℓ₂) → (f : A → Lattice.Carrier L) → 
                  (h : LatticeHom (FreeLattice A) L) → 
                  (∀ a → Lattice._≈_ L (LatticeHom.map h (η a)) (f a)) → 
                  ∀ e → Lattice._≈_ L (LatticeHom.map h e) (extend L f e)
universal-unique L f h h-unit (var a) = h-unit a
universal-unique L f h h-unit (e₁ ∨E e₂) = 
  let 
    rec₁ = universal-unique L f h h-unit e₁
    rec₂ = universal-unique L f h h-unit e₂
  in 
    Lattice.isEquivalence.trans (Lattice.setoid L)
      (LatticeHom.map-∨ h e₁ e₂)
      (Lattice.∨-cong L rec₁ rec₂)
universal-unique L f h h-unit (e₁ ∧E e₂) = 
  let 
    rec₁ = universal-unique L f h h-unit e₁
    rec₂ = universal-unique L f h h-unit e₂
  in 
    Lattice.isEquivalence.trans (Lattice.setoid L)
      (LatticeHom.map-∧ h e₁ e₂)
      (Lattice.∧-cong L rec₁ rec₂)
