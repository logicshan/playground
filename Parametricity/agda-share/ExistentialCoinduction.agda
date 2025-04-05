{-# OPTIONS --universe-polymorphism #-}

module ExistentialCoinduction where

-- Implementing coinductive values using existential quantification
-- and shape functors. We need universe polymorphism for observation.

record Unit : Set where

unit : Unit
unit = _

data Level : Set where
  zero : Level
  suc  : Level → Level
{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO zero  #-}
{-# BUILTIN LEVELSUC  suc   #-}

max : Level → Level → Level
max zero    j       = j
max (suc i) zero    = suc i
max (suc i) (suc j) = suc (max i j)
{-# BUILTIN LEVELMAX max #-}

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
{-# BUILTIN NATURAL ℕ    #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}

data _≡_ {i : Level} {A : Set i} (x : A) : A → Set i where
  refl : x ≡ x

infixr 50 _,_
infixr 50 _×_
data _×_ {i j : Level} (A : Set i) (B : Set j) : Set (max i j) where
  _,_ : A → B → A × B

-- The shape of natural numbers N X = 1 + X
data ℕ-Shape {i : Level} (X : Set i) : Set i where
  z : ℕ-Shape X
  s : X → ℕ-Shape X

map-ℕ : ∀{i j} {X : Set i} {Y : Set j} → (X → Y) → ℕ-Shape X → ℕ-Shape Y
map-ℕ f z     = z
map-ℕ f (s x) = s (f x)

data ∃ {i j : Level} (A : Set i) (P : A → Set j) : Set (max i j) where
  _,_ : (x : A) (w : P x) → ∃ A P

Coℕ : Set₁
Coℕ = ∃ Set λ S → S × (S → ℕ-Shape S)

∞ : Coℕ
∞ = (Unit , unit , (λ u → s u))

∞' : Coℕ
∞' = (ℕ , 0 , λ n → s (suc n))

obs-Coℕ : Coℕ → ℕ-Shape Coℕ
obs-Coℕ (S , (seed , step)) =
  map-ℕ (λ seed' -> (S , (seed' , step))) (step seed)

-- Proofs that a particular conatural is infinite, also defined
-- using existential quantification. This is completely my own
-- ad-hoc invention, not based on any theory.
data Infinite-Shape {i : Level} (X : Coℕ → Set i) : 
  ℕ-Shape Coℕ → Set (max (suc zero) i) where
  expand : ∀{cn} → X cn → Infinite-Shape X (s cn)

Infinite : Coℕ → Set₂
Infinite cn = ∃ (Coℕ → Set₁) λ S → S cn × (S cn → Infinite-Shape S (obs-Coℕ cn))

data Lift (A : Set) : Set₁ where
  lift : A → Lift A

data Witness (cn : Coℕ) : Set₁ where
  wit : Witness cn

inf-∞ : Infinite ∞
inf-∞ = (Witness , wit , step)
 where
 step : Witness ∞ → Infinite-Shape Witness (s ∞)
 step wit = expand wit

inf-∞' : Infinite ∞'
inf-∞' = (Witness , wit , step')
 where
 step : ℕ → ℕ-Shape ℕ
 step n = s (suc n)

 step' : ∀{n} →  Witness (ℕ , n , step)
       → Infinite-Shape Witness (s (ℕ , suc n , step))
 step' {n} wit = expand wit
