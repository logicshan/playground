module FreeDeMorganAlgebra where

open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary using (Rel; Setoid; IsEquivalence)
open import Algebra.Lattice using (Lattice; DeMorganAlgebra; IsLattice; IsDistributiveLattice; IsDeMorganAlgebra)
open import Function using (id; _∘_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst)

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

  FreeDeMorganFunctor : ∀ {o} →  Functor (Sets o) (DeMorganCategory o o)
  F₀ FreeDeMorganFunctor = freeDeMorgan
  DeMorganHom.⟦ F₁ FreeDeMorganFunctor f ⟧ (η x) = η (f x)
  DeMorganHom.⟦ F₁ FreeDeMorganFunctor f ⟧ ⊤ = ⊤
  DeMorganHom.⟦ F₁ FreeDeMorganFunctor f ⟧ ⊥ = ⊥
  DeMorganHom.⟦ F₁ FreeDeMorganFunctor f ⟧ (x ∨ x₁)
    = DeMorganHom.⟦ F₁ FreeDeMorganFunctor f ⟧ x ∨ DeMorganHom.⟦ F₁ FreeDeMorganFunctor f ⟧ x₁
  DeMorganHom.⟦ F₁ FreeDeMorganFunctor f ⟧ (x ∧ x₁)
    = DeMorganHom.⟦ F₁ FreeDeMorganFunctor f ⟧ x ∧ DeMorganHom.⟦ F₁ FreeDeMorganFunctor f ⟧ x₁
  DeMorganHom.⟦ F₁ FreeDeMorganFunctor f ⟧ (¬ x) = ¬ (DeMorganHom.⟦ F₁ FreeDeMorganFunctor f ⟧ x)
  IsRelHomomorphism.cong (DeMorganHom.isRelHomomorphism (F₁ FreeDeMorganFunctor f)) {x} {y} x₁ = lemma x₁
    where
    𝕗 : (DeMorganCategory _ _ Category.⇒ F₀ FreeDeMorganFunctor _)
         (F₀ FreeDeMorganFunctor _)
    𝕗 = F₁ FreeDeMorganFunctor f
    module 𝕗 = DeMorganHom 𝕗
    f⟦⟧ : DeMorganAlgebra.Carrier (F₀ FreeDeMorganFunctor _) →
         DeMorganAlgebra.Carrier (F₀ FreeDeMorganFunctor _)
    f⟦⟧ = 𝕗.⟦_⟧
    cong⟦⟧ : Homomorphic₂
              (DeMorganAlgebra.Carrier (F₀ FreeDeMorganFunctor _))
              (DeMorganAlgebra.Carrier (F₀ FreeDeMorganFunctor _))
              (DeMorganAlgebra._≈_ (F₀ FreeDeMorganFunctor _))
              (DeMorganAlgebra._≈_ (F₀ FreeDeMorganFunctor _)) DeMorganHom.⟦ F₁ FreeDeMorganFunctor f ⟧
    cong⟦⟧ = IsRelHomomorphism.cong 𝕗.isRelHomomorphism
    lemma : (x ≈ y) → DeMorganHom.⟦ F₁ FreeDeMorganFunctor f ⟧ x ≈ DeMorganHom.⟦ F₁ FreeDeMorganFunctor f ⟧ y
    lemma refl = refl
    lemma (sym p) = sym (cong⟦⟧ p)
    lemma (trans p p₁) = trans (cong⟦⟧ p) (cong⟦⟧ p₁) -- cong⟦⟧ (trans p p₁)
    lemma (∧-cong p p₁) = ∧-cong (cong⟦⟧ p) (cong⟦⟧ p₁)
    lemma (∨-cong p p₁) = ∨-cong (cong⟦⟧ p) (cong⟦⟧ p₁)
    lemma (¬-cong p) = ¬-cong (cong⟦⟧ p)
    lemma ∧-assoc = ∧-assoc
    lemma ∨-assoc = ∨-assoc
    lemma ∧-comm = ∧-comm
    lemma ∨-comm = ∨-comm
    lemma ∧-idem = ∧-idem
    lemma ∨-idem = ∨-idem
    lemma absorb-∧∨ = absorb-∧∨
    lemma absorb-∨∧ = absorb-∨∧
    lemma de-morgan₁ = de-morgan₁
    lemma de-morgan₂ = de-morgan₂
    lemma ¬-involution = ¬-involution
    lemma ∨-distrib-∧ˡ = ∨-distrib-∧ˡ
    lemma ∨-distrib-∧ʳ = ∨-distrib-∧ʳ
    lemma ∧-distrib-∨ˡ = ∧-distrib-∨ˡ
    lemma ∧-distrib-∨ʳ = ∧-distrib-∨ʳ
    lemma ⊤-∧-identity = ⊤-∧-identity
    lemma ⊥-∨-identity = ⊥-∨-identity

  DeMorganHom.pres-∨ (F₁ FreeDeMorganFunctor f) = λ x y → refl
  DeMorganHom.pres-∧ (F₁ FreeDeMorganFunctor f) = λ x y → refl
  DeMorganHom.pres-¬ (F₁ FreeDeMorganFunctor f) = λ x → refl
  DeMorganHom.pres-⊤ (F₁ FreeDeMorganFunctor f) = refl
  DeMorganHom.pres-⊥ (F₁ FreeDeMorganFunctor f) = refl
  identity FreeDeMorganFunctor (η x) = refl
  identity FreeDeMorganFunctor ⊤ = refl
  identity FreeDeMorganFunctor ⊥ = refl
  identity FreeDeMorganFunctor (x ∨ x₁) 
    = ∨-cong (identity FreeDeMorganFunctor x) (identity FreeDeMorganFunctor x₁)
  identity FreeDeMorganFunctor (x ∧ x₁) 
    = ∧-cong (identity FreeDeMorganFunctor x) (identity FreeDeMorganFunctor x₁)
  identity FreeDeMorganFunctor (¬ x) = ¬-cong (identity FreeDeMorganFunctor x)
  homomorphism FreeDeMorganFunctor (η x) = refl
  homomorphism FreeDeMorganFunctor ⊤ = refl
  homomorphism FreeDeMorganFunctor ⊥ = refl
  homomorphism FreeDeMorganFunctor (x ∨ x₁)
    = ∨-cong (homomorphism FreeDeMorganFunctor x) (homomorphism FreeDeMorganFunctor x₁)
  homomorphism FreeDeMorganFunctor (x ∧ x₁) 
    = ∧-cong (homomorphism FreeDeMorganFunctor x) (homomorphism FreeDeMorganFunctor x₁)
  homomorphism FreeDeMorganFunctor (¬ x) = ¬-cong (homomorphism FreeDeMorganFunctor x)
  F-resp-≈ FreeDeMorganFunctor p (η x) rewrite p x = refl
  F-resp-≈ FreeDeMorganFunctor p ⊤ = refl
  F-resp-≈ FreeDeMorganFunctor p ⊥ = refl
  F-resp-≈ FreeDeMorganFunctor p (x ∨ x₁)
    = ∨-cong (F-resp-≈ FreeDeMorganFunctor p x) (F-resp-≈ FreeDeMorganFunctor p x₁)
  F-resp-≈ FreeDeMorganFunctor p (x ∧ x₁)
    = ∧-cong (F-resp-≈ FreeDeMorganFunctor p x) (F-resp-≈ FreeDeMorganFunctor p x₁)
  F-resp-≈ FreeDeMorganFunctor p (¬ x) = ¬-cong (F-resp-≈ FreeDeMorganFunctor p x)
