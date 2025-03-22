module FreeDeMorganAlgebra where

open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary using (Rel; Setoid; IsEquivalence)
open import Algebra.Lattice using (Lattice; DeMorganAlgebra; IsLattice; IsDistributiveLattice; IsDeMorganAlgebra)
open import Function using (id; _∘_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst)
open import Data.Nat

open import Categories.Category
open import Categories.Functor
open import Categories.NaturalTransformation
open import Categories.Monad
open import Categories.Category.Instance.Sets using (Sets)

open import DeMorganCategory
open import Relation.Binary.Morphism.Structures using (IsRelHomomorphism)
open import Relation.Binary.Morphism.Definitions using (Homomorphic₂)

private
  variable
    ℓ : Level

infix  8 ¬_
infixr 7 _∧_
infixr 6 _∨_
infix  4 _≈_

-- 自由德摩根代数的项定义
data FreeDeMorgan (X : Set ℓ) : Set ℓ where
  η     : X → FreeDeMorgan X                               -- 生成元
  ⊤     : FreeDeMorgan X                                   -- 顶元素
  ⊥     : FreeDeMorgan X                                   -- 底元素
  _∨_   : FreeDeMorgan X → FreeDeMorgan X → FreeDeMorgan X -- 并运算
  _∧_   : FreeDeMorgan X → FreeDeMorgan X → FreeDeMorgan X -- 交运算
  ¬_    : FreeDeMorgan X → FreeDeMorgan X                  -- 否定运算


-- Equivalence relation encoding lattice axioms
data _≈_ {X : Set ℓ} : Rel (FreeDeMorgan X) ℓ where
  refl        : ∀ {x} → x ≈ x
  sym         : ∀ {x y} → x ≈ y → y ≈ x
  trans       : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z
  ∧-cong      : ∀ {x x′ y y′} → x ≈ x′ → y ≈ y′ → (x ∧ y) ≈ (x′ ∧ y′)
  ∨-cong      : ∀ {x x′ y y′} → x ≈ x′ → y ≈ y′ → (x ∨ y) ≈ (x′ ∨ y′)
  ¬-cong      : ∀ {x y} → x ≈ y → (¬ x) ≈ (¬ y)
  ∧-assoc     : ∀ {x y z} → ((x ∧ y) ∧ z) ≈ (x ∧ (y ∧ z))
  ∨-assoc     : ∀ {x y z} → ((x ∨ y) ∨ z) ≈ (x ∨ (y ∨ z)) 
  ∧-comm      : ∀ {x y} → (x ∧ y) ≈ (y ∧ x)
  ∨-comm      : ∀ {x y} → (x ∨ y) ≈ (y ∨ x)
  ∧-idem      : ∀ {x} → (x ∧ x) ≈ x
  ∨-idem      : ∀ {x} → (x ∨ x) ≈ x
  absorb-∧∨   : ∀ {x y} → (x ∧ (x ∨ y)) ≈ x
  absorb-∨∧   : ∀ {x y} → (x ∨ (x ∧ y)) ≈ x
  de-morgan₁  : ∀ {t s} → ¬ (t ∨ s) ≈ (¬ t ∧ ¬ s)
  de-morgan₂  : ∀ {t s} → ¬ (t ∧ s) ≈ (¬ t ∨ ¬ s)
  ¬-involution : ∀ {t} → ¬ (¬ t) ≈ t
--  ∧-∨-distrib : ∀ {t s r} → (t ∧ (s ∨ r)) ≈ ((t ∧ s) ∨ (t ∧ r))
--  ∨-∧-distrib : ∀ {t s r} → (t ∨ (s ∧ r)) ≈ ((t ∨ s) ∧ (t ∨ r))
  ∨-distrib-∧ˡ : ∀ {t s r} → (t ∨ (s ∧ r)) ≈ ((t ∨ s) ∧ (t ∨ r))
  ∨-distrib-∧ʳ : ∀ {t s r} → (s ∧ r) ∨ t ≈ (s ∨ t) ∧ (r ∨ t)
  ∧-distrib-∨ˡ : ∀ {t s r} → t ∧ (s ∨ r) ≈ ((t ∧ s) ∨ (t ∧ r))
  ∧-distrib-∨ʳ : ∀ {t s r} → (s ∨ r) ∧ t ≈ (s ∧ t) ∨ (r ∧ t)
  ⊤-∧-identity : ∀ {t} → (t ∧ ⊤) ≈ t
  ⊥-∨-identity : ∀ {t} → (t ∨ ⊥) ≈ t

≈-isEquivalence : ∀ {X} → IsEquivalence (_≈_ {ℓ} {X})
≈-isEquivalence = record
  { refl  = refl
  ; sym   = sym
  ; trans = trans
  }

FreeDeMorganSetoid : (X : Set ℓ) → Setoid ℓ ℓ
FreeDeMorganSetoid X = record
  { Carrier       = FreeDeMorgan X
  ; _≈_           = _≈_
  ; isEquivalence = ≈-isEquivalence
  }

freeDeMorgan : (X : Set ℓ) → DeMorganAlgebra ℓ ℓ
DeMorganAlgebra.Carrier (freeDeMorgan X) = FreeDeMorgan X
DeMorganAlgebra._≈_ (freeDeMorgan X) = _≈_
DeMorganAlgebra._∨_ (freeDeMorgan X) = _∨_
DeMorganAlgebra._∧_ (freeDeMorgan X) = _∧_
DeMorganAlgebra.¬ freeDeMorgan X = ¬_
DeMorganAlgebra.⊤ (freeDeMorgan X) = ⊤
DeMorganAlgebra.⊥ (freeDeMorgan X) = ⊥
IsLattice.isEquivalence (IsDistributiveLattice.isLattice (IsDeMorganAlgebra.isDistributiveLattice (DeMorganAlgebra.isDeMorganAlgebra (freeDeMorgan X)))) = ≈-isEquivalence
IsLattice.∨-comm (IsDistributiveLattice.isLattice (IsDeMorganAlgebra.isDistributiveLattice (DeMorganAlgebra.isDeMorganAlgebra (freeDeMorgan X)))) x y = ∨-comm
IsLattice.∨-assoc (IsDistributiveLattice.isLattice (IsDeMorganAlgebra.isDistributiveLattice (DeMorganAlgebra.isDeMorganAlgebra (freeDeMorgan X)))) x y z = ∨-assoc
IsLattice.∨-cong (IsDistributiveLattice.isLattice (IsDeMorganAlgebra.isDistributiveLattice (DeMorganAlgebra.isDeMorganAlgebra (freeDeMorgan X)))) = ∨-cong
IsLattice.∧-comm (IsDistributiveLattice.isLattice (IsDeMorganAlgebra.isDistributiveLattice (DeMorganAlgebra.isDeMorganAlgebra (freeDeMorgan X)))) x y = ∧-comm
IsLattice.∧-assoc (IsDistributiveLattice.isLattice (IsDeMorganAlgebra.isDistributiveLattice (DeMorganAlgebra.isDeMorganAlgebra (freeDeMorgan X)))) x y z = ∧-assoc
IsLattice.∧-cong (IsDistributiveLattice.isLattice (IsDeMorganAlgebra.isDistributiveLattice (DeMorganAlgebra.isDeMorganAlgebra (freeDeMorgan X)))) = ∧-cong
IsLattice.absorptive (IsDistributiveLattice.isLattice (IsDeMorganAlgebra.isDistributiveLattice (DeMorganAlgebra.isDeMorganAlgebra (freeDeMorgan X)))) = (λ x y → absorb-∨∧) , (λ x y → absorb-∧∨)
IsDistributiveLattice.∨-distrib-∧ (IsDeMorganAlgebra.isDistributiveLattice (DeMorganAlgebra.isDeMorganAlgebra (freeDeMorgan X))) = (λ x y z → ∨-distrib-∧ˡ) , (λ x y z → ∨-distrib-∧ʳ)
IsDistributiveLattice.∧-distrib-∨ (IsDeMorganAlgebra.isDistributiveLattice (DeMorganAlgebra.isDeMorganAlgebra (freeDeMorgan X))) = (λ x y z → ∧-distrib-∨ˡ) , λ x y z → ∧-distrib-∨ʳ
IsDeMorganAlgebra.¬-involution (DeMorganAlgebra.isDeMorganAlgebra (freeDeMorgan X)) = λ x → ¬-involution
IsDeMorganAlgebra.¬-cong (DeMorganAlgebra.isDeMorganAlgebra (freeDeMorgan X)) = ¬-cong
IsDeMorganAlgebra.de-morgan₁ (DeMorganAlgebra.isDeMorganAlgebra (freeDeMorgan X)) = de-morgan₁
IsDeMorganAlgebra.de-morgan₂ (DeMorganAlgebra.isDeMorganAlgebra (freeDeMorgan X)) = de-morgan₂
IsDeMorganAlgebra.⊤-∧-identity (DeMorganAlgebra.isDeMorganAlgebra (freeDeMorgan X)) = λ x → ⊤-∧-identity
IsDeMorganAlgebra.⊥-∨-identity (DeMorganAlgebra.isDeMorganAlgebra (freeDeMorgan X)) = λ x → ⊥-∨-identity

module _ where

  open Functor

  FreeDeMorganFunctor : ∀ {o} → Functor (Sets o) (DeMorganCategory o o)
  F₀ FreeDeMorganFunctor = freeDeMorgan
  F₁ FreeDeMorganFunctor f = record
    { ⟦_⟧ = mapTerm f
    ; isRelHomomorphism = record { cong = cong-f }
    ; pres-∨ = λ x y → refl
    ; pres-∧ = λ x y → refl
    ; pres-¬ = λ x → refl
    ; pres-⊤ = refl
    ; pres-⊥ = refl
    }
    where
      mapTerm : ∀ {X Y} → (X → Y) → FreeDeMorgan X → FreeDeMorgan Y
      mapTerm g (η x) = η (g x)
      mapTerm g ⊤ = ⊤
      mapTerm g ⊥ = ⊥
      mapTerm g (x ∨ y) = mapTerm g x ∨ mapTerm g y
      mapTerm g (x ∧ y) = mapTerm g x ∧ mapTerm g y
      mapTerm g (¬ x) = ¬ (mapTerm g x)

      cong-f : ∀ {x y} → x ≈ y → mapTerm f x ≈ mapTerm f y
      cong-f refl = refl
      cong-f (sym p) = sym (cong-f p)
      cong-f (trans p q) = trans (cong-f p) (cong-f q)
      cong-f (∧-cong p q) = ∧-cong (cong-f p) (cong-f q)
      cong-f (∨-cong p q) = ∨-cong (cong-f p) (cong-f q)
      cong-f (¬-cong p) = ¬-cong (cong-f p)
      cong-f ∧-assoc = ∧-assoc
      cong-f ∨-assoc = ∨-assoc
      cong-f ∧-comm = ∧-comm
      cong-f ∨-comm = ∨-comm
      cong-f ∧-idem = ∧-idem
      cong-f ∨-idem = ∨-idem
      cong-f absorb-∧∨ = absorb-∧∨
      cong-f absorb-∨∧ = absorb-∨∧
      cong-f de-morgan₁ = de-morgan₁
      cong-f de-morgan₂ = de-morgan₂
      cong-f ¬-involution = ¬-involution
      cong-f ∨-distrib-∧ˡ = ∨-distrib-∧ˡ
      cong-f ∨-distrib-∧ʳ = ∨-distrib-∧ʳ
      cong-f ∧-distrib-∨ˡ = ∧-distrib-∨ˡ
      cong-f ∧-distrib-∨ʳ = ∧-distrib-∨ʳ
      cong-f ⊤-∧-identity = ⊤-∧-identity
      cong-f ⊥-∨-identity = ⊥-∨-identity

  identity FreeDeMorganFunctor {X} = functor-id X
    where
      functor-id : ∀ X → ∀ (x : FreeDeMorgan X) → DeMorganHom.⟦ F₁ FreeDeMorganFunctor (Category.id (Sets _)) ⟧ x ≈ x
      functor-id X (η x) = refl
      functor-id X ⊤ = refl
      functor-id X ⊥ = refl
      functor-id X (x ∨ y) = ∨-cong (functor-id X x) (functor-id X y)
      functor-id X (x ∧ y) = ∧-cong (functor-id X x) (functor-id X y) 
      functor-id X (¬ x) = ¬-cong (functor-id X x)

  homomorphism FreeDeMorganFunctor {X} {Y} {Z} {f} {g} = functor-hom X Y Z f g
    where
      functor-hom : ∀ X Y Z (f : X → Y) (g : Y → Z) → 
                   ∀ (x : FreeDeMorgan X) → 
                   DeMorganHom.⟦ F₁ FreeDeMorganFunctor (g ∘ f) ⟧ x ≈ 
                   DeMorganHom.⟦ F₁ FreeDeMorganFunctor g ⟧ (DeMorganHom.⟦ F₁ FreeDeMorganFunctor f ⟧ x)
      functor-hom X Y Z f g (η x) = refl
      functor-hom X Y Z f g ⊤ = refl
      functor-hom X Y Z f g ⊥ = refl
      functor-hom X Y Z f g (x ∨ y) = ∨-cong (functor-hom X Y Z f g x) (functor-hom X Y Z f g y)
      functor-hom X Y Z f g (x ∧ y) = ∧-cong (functor-hom X Y Z f g x) (functor-hom X Y Z f g y)
      functor-hom X Y Z f g (¬ x) = ¬-cong (functor-hom X Y Z f g x)

  F-resp-≈ FreeDeMorganFunctor {X} {Y} {f} {g} p = functor-resp X Y f g p
    where
      functor-resp : ∀ X Y (f g : X → Y) → 
                    (∀ x → f x ≡ g x) → 
                    ∀ (x : FreeDeMorgan X) → 
                    DeMorganHom.⟦ F₁ FreeDeMorganFunctor f ⟧ x ≈ DeMorganHom.⟦ F₁ FreeDeMorganFunctor g ⟧ x
      functor-resp X Y f g p (η x) rewrite p x = refl
      functor-resp X Y f g p ⊤ = refl
      functor-resp X Y f g p ⊥ = refl
      functor-resp X Y f g p (x ∨ y) = ∨-cong (functor-resp X Y f g p x) (functor-resp X Y f g p y)
      functor-resp X Y f g p (x ∧ y) = ∧-cong (functor-resp X Y f g p x) (functor-resp X Y f g p y)
      functor-resp X Y f g p (¬ x) = ¬-cong (functor-resp X Y f g p x)

  open DeMorganAlgebra

  Forgetful : ∀ {o} → Functor (DeMorganCategory o o) (Sets o)
  F₀ Forgetful DM = DM .Carrier
  F₁ Forgetful = DeMorganHom.⟦_⟧
  identity Forgetful = λ _ → _≡_.refl
  homomorphism Forgetful = λ _ → _≡_.refl
  F-resp-≈ Forgetful {DM} {DM′} {f} {g} p x = {!!}
