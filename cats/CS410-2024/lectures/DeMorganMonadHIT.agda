{-# OPTIONS --cubical #-}

module DeMorganMonadHIT where

open import Cubical.Foundations.Prelude hiding (_∧_; _∨_)
open import Cubical.Foundations.Function
open import Agda.Primitive

variable
  ℓ : Level
  A B C : Set ℓ

data FreeDM (A : Set ℓ) : Set ℓ where
  var   : A → FreeDM A
  𝟎     : FreeDM A
  𝟏     : FreeDM A
  _∧_   : FreeDM A → FreeDM A → FreeDM A
  _∨_   : FreeDM A → FreeDM A → FreeDM A
  ¬_    : FreeDM A → FreeDM A

  -- Lattice laws as paths
  ∧-comm    : ∀ x y → PathP (λ i → FreeDM A) (x ∧ y) (y ∧ x)
  ∧-assoc   : ∀ x y z → PathP (λ i → FreeDM A) (x ∧ (y ∧ z)) ((x ∧ y) ∧ z)
  ∨-comm    : ∀ x y → PathP (λ i → FreeDM A) (x ∨ y) (y ∨ x)
  ∨-assoc   : ∀ x y z → PathP (λ i → FreeDM A) (x ∨ (y ∨ z)) ((x ∨ y) ∨ z)
  ∧-absorb  : ∀ x y → PathP (λ i → FreeDM A) (x ∧ (x ∨ y)) x
  ∨-absorb  : ∀ x y → PathP (λ i → FreeDM A) (x ∨ (x ∧ y)) x

  -- Bounded lattice laws
  ∧-identity : ∀ x → PathP (λ i → FreeDM A) (x ∧ 𝟏) x
  ∨-identity : ∀ x → PathP (λ i → FreeDM A) (x ∨ 𝟎) x

  -- De Morgan laws
  involution : ∀ x → PathP (λ i → FreeDM A) (¬ (¬ x)) x
  deMorgan-∧ : ∀ x y → PathP (λ i → FreeDM A) (¬ (x ∧ y)) ((¬ x) ∨ (¬ y))
  deMorgan-∨ : ∀ x y → PathP (λ i → FreeDM A) (¬ (x ∨ y)) ((¬ x) ∧ (¬ y))

  squash : (x y : FreeDM A) → (p q : x ≡ y) → p ≡ q

DM : Set ℓ → Set ℓ
DM = FreeDM

mapDM : (A → B) → DM A → DM B
mapDM f = {!!}

η : A → DM A
η = var

interpretDM : (A → DM B) → DM A → DM B
interpretDM f = {!!}

_>>=DM_ : DM A → (A → DM B) → DM B
m >>=DM f = interpretDM f m

record Monad (M : Set ℓ → Set ℓ) : Set (lsuc ℓ) where
  field
    return : A → M A
    _>>=_  : M A → (A → M B) → M B
    left-identity  : ∀ {x : A} {f : A → M B} → PathP (λ i → M B) ((return x) >>= f) (f x)
    right-identity : ∀ {m : M A} → PathP (λ i → M A) (m >>= return) m
    associativity  : ∀ {m : M A} {f : A → M B} {g : B → M C} →
                     PathP (λ i → M C) ((m >>= f) >>= g) (m >>= (λ x → f x >>= g))

dmMonad : Monad DM
dmMonad = record
  { return = η
  ; _>>=_ = _>>=DM_
  ; left-identity = leftId
  ; right-identity = rightId
  ; associativity = assoc
  }
  where
    leftId : ∀ {x : A} {f : A → DM B} → PathP (λ i → DM B) ((η x) >>=DM f) (f x)
    leftId {x = x} {f = f} = {!!}  -- Since (η x) >>=DM f = interpretDM f (var x) = f x

    rightId : ∀ {m : DM A} → PathP (λ i → DM A) (m >>=DM η) m
    rightId {m = m} = {!!}

    assoc : ∀ {m : DM A} {f : A → DM B} {g : B → DM C} →
            PathP (λ i → DM C) ((m >>=DM f) >>=DM g) (m >>=DM (λ x → f x >>=DM g))
    assoc {m = m} = {!!}









{-
    rightId : ∀ {m : DM A} → PathP (λ i → DM A) (m >>=DM η) m
    rightId {m = var x} = refl
    rightId {m = 𝟎} = refl
    rightId {m = 𝟏} = refl
    rightId {m = m ∧ n} = λ i → rightId {m = m} i ∧ rightId {m = n} i
    rightId {m = m ∨ n} = λ i → rightId {m = m} i ∨ rightId {m = n} i
    rightId {m = ¬ m} = λ i → ¬ (rightId {m = m} i)
    rightId {m = ∧-comm x y i} = λ i₁ → ∧-comm (rightId {m = x} i₁) (rightId {m = y} i₁) i
    rightId {m = ∧-assoc x y z i} = λ i₁ → ∧-assoc (rightId {m = x} i₁) (rightId {m = y} i₁) (rightId {m = z} i₁) i
    rightId {m = ∨-comm x y i} = λ i₁ → ∨-comm (rightId {m = x} i₁) (rightId {m = y} i₁) i
    rightId {m = ∨-assoc x y z i} = λ i₁ → ∨-assoc (rightId {m = x} i₁) (rightId {m = y} i₁) (rightId {m = z} i₁) i
    rightId {m = ∧-absorb x y i} = λ i₁ → ∧-absorb (rightId {m = x} i₁) (rightId {m = y} i₁) i
    rightId {m = ∨-absorb x y i} = λ i₁ → ∨-absorb (rightId {m = x} i₁) (rightId {m = y} i₁) i
    rightId {m = ∧-identity x i} = λ i₁ → ∧-identity (rightId {m = x} i₁) i
    rightId {m = ∨-identity x i} = λ i₁ → ∨-identity (rightId {m = x} i₁) i
    rightId {m = involution x i} = λ i₁ → involution (rightId {m = x} i₁) i
    rightId {m = deMorgan-∧ x y i} = λ i₁ → deMorgan-∧ (rightId {m = x} i₁) (rightId {m = y} i₁) i
    rightId {m = deMorgan-∨ x y i} = λ i₁ → deMorgan-∨ (rightId {m = x} i₁) (rightId {m = y} i₁) i

    assoc : ∀ {m : DM A} {f : A → DM B} {g : B → DM C} →
            PathP (λ i → DM C) ((m >>=DM f) >>=DM g) (m >>=DM (λ x → f x >>=DM g))
    assoc {m = var x} = refl
    assoc {m = 𝟎} = refl
    assoc {m = 𝟏} = refl
    assoc {m = m ∧ n} = λ i → assoc {m = m} i ∧ assoc {m = n} i
    assoc {m = m ∨ n} = λ i → assoc {m = m} i ∨ assoc {m = n} i
    assoc {m = ¬ m} = λ i → ¬ (assoc {m = m} i)
    assoc {m = ∧-comm x y i} = λ i₁ → ∧-comm (assoc {m = x} i₁) (assoc {m = y} i₁) i
    assoc {m = ∧-assoc x y z i} = λ i₁ → ∧-assoc (assoc {m = x} i₁) (assoc {m = y} i₁) (assoc {m = z} i₁) i
    assoc {m = ∨-comm x y i} = λ i₁ → ∨-comm (assoc {m = x} i₁) (assoc {m = y} i₁) i
    assoc {m = ∨-assoc x y z i} = λ i₁ → ∨-assoc (assoc {m = x} i₁) (assoc {m = y} i₁) (assoc {m = z} i₁) i
    assoc {m = ∧-absorb x y i} = λ i₁ → ∧-absorb (assoc {m = x} i₁) (assoc {m = y} i₁) i
    assoc {m = ∨-absorb x y i} = λ i₁ → ∨-absorb (assoc {m = x} i₁) (assoc {m = y} i₁) i
    assoc {m = ∧-identity x i} = λ i₁ → ∧-identity (assoc {m = x} i₁) i
    assoc {m = ∨-identity x i} = λ i₁ → ∨-identity (assoc {m = x} i₁) i
    assoc {m = involution x i} = λ i₁ → involution (assoc {m = x} i₁) i
    assoc {m = deMorgan-∧ x y i} = λ i₁ → deMorgan-∧ (assoc {m = x} i₁) (assoc {m = y} i₁) i
    assoc {m = deMorgan-∨ x y i} = λ i₁ → deMorgan-∨ (assoc {m = x} i₁) (assoc {m = y} i₁) i
-}
{-
    rightId : ∀ {m : DM A} → PathP (λ i → DM A) (m >>=DM η) m
    rightId {m = var x} = refl
    rightId {m = 𝟎} = refl
    rightId {m = 𝟏} = refl
    rightId {m = x ∧ y} i = rightId {m = x} i ∧ rightId {m = y} i
    rightId {m = x ∨ y} i = rightId {m = x} i ∨ rightId {m = y} i
    rightId {m = ¬ x} i = ¬ (rightId {m = x} i)
    rightId {m = ∧-comm x y i} j = ∧-comm (rightId {m = x} j) (rightId {m = y} j) i
    rightId {m = ∧-assoc x y z i} j = ∧-assoc (rightId {m = x} j) (rightId {m = y} j) (rightId {m = z} j) i
    rightId {m = ∨-comm x y i} j = ∨-comm (rightId {m = x} j) (rightId {m = y} j) i
    rightId {m = ∨-assoc x y z i} j = ∨-assoc (rightId {m = x} j) (rightId {m = y} j) (rightId {m = z} j) i
    rightId {m = ∧-absorb x y i} j = ∧-absorb (rightId {m = x} j) (rightId {m = y} j) i
    rightId {m = ∨-absorb x y i} j = ∨-absorb (rightId {m = x} j) (rightId {m = y} j) i
    rightId {m = ∧-identity x i} j = ∧-identity (rightId {m = x} j) i
    rightId {m = ∨-identity x i} j = ∨-identity (rightId {m = x} j) i
    rightId {m = involution x i} j = involution (rightId {m = x} j) i
    rightId {m = deMorgan-∧ x y i} j = deMorgan-∧ (rightId {m = x} j) (rightId {m = y} j) i
    rightId {m = deMorgan-∨ x y i} j = deMorgan-∨ (rightId {m = x} j) (rightId {m = y} j) i



    assoc : ∀ {m : DM A} {f : A → DM B} {g : B → DM C} →
            PathP (λ i → DM C) ((m >>=DM f) >>=DM g) (m >>=DM (λ x → f x >>=DM g))
    assoc {m = var x} = refl
    assoc {m = 𝟎} = refl
    assoc {m = 𝟏} = refl
    assoc {m = x ∧ y} i = assoc {m = x} i ∧ assoc {m = y} i
    assoc {m = x ∨ y} i = assoc {m = x} i ∨ assoc {m = y} i
    assoc {m = ¬ x} i = ¬ (assoc {m = x} i)
    assoc {m = ∧-comm x y i} j = ∧-comm (assoc {m = x} j) (assoc {m = y} j) i
    assoc {m = ∧-assoc x y z i} j = ∧-assoc (assoc {m = x} j) (assoc {m = y} j) (assoc {m = z} j) i
    assoc {m = ∨-comm x y i} j = ∨-comm (assoc {m = x} j) (assoc {m = y} j) i
    assoc {m = ∨-assoc x y z i} j = ∨-assoc (assoc {m = x} j) (assoc {m = y} j) (assoc {m = z} j) i
    assoc {m = ∧-absorb x y i} j = ∧-absorb (assoc {m = x} j) (assoc {m = y} j) i
    assoc {m = ∨-absorb x y i} j = ∨-absorb (assoc {m = x} j) (assoc {m = y} j) i
    assoc {m = ∧-identity x i} j = ∧-identity (assoc {m = x} j) i
    assoc {m = ∨-identity x i} j = ∨-identity (assoc {m = x} j) i
    assoc {m = involution x i} j = involution (assoc {m = x} j) i
    assoc {m = deMorgan-∧ x y i} j = deMorgan-∧ (assoc {m = x} j) (assoc {m = y} j) i
    assoc {m = deMorgan-∨ x y i} j = deMorgan-∨ (assoc {m = x} j) (assoc {m = y} j) i
-}
{-
    rightId : ∀ {m : DM A} → PathP (λ i → DM A) (m >>=DM η) m
    rightId {m = var x} = refl
    rightId {m = 𝟎} = refl
    rightId {m = 𝟏} = refl
    rightId {m = m ∧ n} = λ i → rightId {m = m} i ∧ rightId {m = n} i
    rightId {m = m ∨ n} = λ i → rightId {m = m} i ∨ rightId {m = n} i
    rightId {m = ¬ m} = λ i → ¬ (rightId {m = m} i)
    rightId {m = ∧-comm x y i} j = ∧-comm (rightId {m = x} j) (rightId {m = y} j) i
    -- Similar cases for other constructors...

    assoc : ∀ {m : DM A} {f : A → DM B} {g : B → DM C} →
            PathP (λ i → DM C) ((m >>=DM f) >>=DM g) (m >>=DM (λ x → f x >>=DM g))
    assoc {m = var x} = refl
    assoc {m = 𝟎} = refl
    assoc {m = 𝟏} = refl
    assoc {m = m ∧ n} = λ i → assoc {m = m} i ∧ assoc {m = n} i
    -- Continue inductively...
-}
