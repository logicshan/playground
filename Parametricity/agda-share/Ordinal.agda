
module Ordinal where

-- An implementation of the ideas expressed in "Ordinals in Type Theory"
-- which can be found here:
--   http://www.cs.nott.ac.uk/~pgh/chat.html

data ⊥ : Set where

data Σ (A : Set) (T : A → Set) : Set where
  _,_ : (x : A) (w : T x) → Σ A T

data S (A : Set) : Set where
  o : S A
  s : A → S A

data W (A : Set) (T : A → Set) : Set where
  zero : W A T
  suc  : W A T → W A T
  _◃_  : (x : A) → (T x → W A T) → W A T

{-
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
{-# BUILTIN NATURAL ℕ    #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}
-}

mutual
  infix 90 _+1
  data On : Set where
    z   : On
    _+1 : On → On
    lim : (α : On) (i : I α) (f : J α i → On) → On

  -- I α seems to be the type of sets of size α
  --  I z      = ⊥ = Fin 0
  --  I (α +1) = 1 + I α = Fin (α +1) for finite α
  -- This would also match the idea that for the ordinal:
  --  lim α i f
  -- We're defining something in the α-th iteration of
  --  W₀ = ⊥
  --  W₁ = W ⊤ W₀ = ℕ
  --  W₂ = W 2 (i ↦ W_i)
  --  ...
  -- And naturally for W_α, where α is a limit ordinal:
  --  W_α = Σ β<α (W_β)
  -- Is a union that lets us make an unbounded, but still
  -- well-founded choice of which iteration to work in.
  I : On → Set
  I z           = ⊥
  I (α +1)      = S (I α)
  I (lim α i f) = Σ (J α i) (λ j → I (f j))

  J : ∀ α → I α → Set
  J z           ()
  J (α +1)      (s i)    = J α i
  J (α +1)      o        = W (I α) (J α)
  J (lim α i f) (j , i') = J (f j) i'

infix 90 _[_/_]
_[_/_] : ∀ α (i : I α) → J α i → On
z         [ ()  / _ ]
α +1      [ s i / j ]     = α [ i / j ]
α +1      [ o / zero ]    = z
α +1      [ o / suc w ]   = α +1 [ o / w ] +1
α +1      [ o / i ◃ f ]   = lim α i (λ j → α +1 [ o / f j ])
lim α i f [ j , i' / j' ] = f j [ i' / j' ]

reg : On → On
reg α = lim (α +1) o (λ j → α +1 [ o / j ])

ℕ : Set
ℕ = W ⊥ (J z)
-- {-# BUILTIN NATURAL ℕ    #-}
-- {-# BUILTIN ZERO    zero #-}
-- {-# BUILTIN SUC     suc  #-}

infixl 50 _⊕_
_⊕_ : ℕ → ℕ → ℕ
zero     ⊕ n = n
suc m    ⊕ n = suc (m ⊕ n)
(() ◃ _) ⊕ _
-- {-# BUILTIN NATPLUS _⊕_ #-}

ℕ-to-On : ℕ → On
ℕ-to-On zero     = z
ℕ-to-On (suc n)  = ℕ-to-On n +1
ℕ-to-On (() ◃ _)

ω : On
ω = lim (z +1) o (ℕ-to-On)

infixl 50 _+_
_+_ : On → On → On
α + z = α
α + β +1 = (α + β) +1
α + lim β i f = lim β i (λ j → α + f j)

infixl 60 _∙_
_∙_ : On → On → On
α ∙ z         = z
α ∙ β +1      = α ∙ β + α
α ∙ lim β i f = lim β i (λ j → α ∙ f j)

infixr 70 _^_
_^_ : On → On → On
α ^ z         = z +1
α ^ β +1      = α ^ β ∙ α
α ^ lim β i f = lim β i (λ j → α ^ f j)

-- tetration
infixr 80 _↑↑_
_↑↑_ : On → On → On
α ↑↑ z         = z +1
α ↑↑ β +1      = α ^ (α ↑↑ β)
α ↑↑ lim β i f = lim β i (λ j → α ↑↑ f j)

_↑_ : (On → On) → On → On → On
(g ↑ z)         β = β
(g ↑ α +1)      β = (g ↑ α) (g β)
(g ↑ lim α i f) β = lim α i (λ j → (g ↑ f j) β)

fix : On → (On → On) → On
fix z           g = (g ↑ ω) z
fix (β +1)      g = (g ↑ ω) (fix β g +1)
fix (lim β i f) g = lim β i (λ j → fix (f j) g)

-- epsilon numbers
ε₀ : On
ε₀ = ω ↑↑ ω

ε : On → On
ε z           = ω ↑↑ ω
ε (α +1)      = ε α ↑↑ ω
ε (lim β i f) = lim β i (λ j → ε (f j))

-- Veblen functions ?
φ : On → On → On
φ z           β           = ω ^ β
φ (α +1)      β           = fix β (φ α)
φ (lim α i f) β           = lim α i (λ j → φ (f j) β)

-- φ (z +1) β
--  = fix β (φ z)
--  = fix β (ω ^)
--
-- fix z (ω ^)
--  = ((ω ^) ↑ ω) z
--  = lim (((ω ^) ↑ n) z)
--  = ε z
--
-- fix (α +1) (ω ^)
--  = ((ω ^) ↑ ω) (fix α (ω ^) +1)
--  = ε (α +1)
--
-- φ 1 = ε
