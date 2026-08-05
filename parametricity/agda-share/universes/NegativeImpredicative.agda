{-# OPTIONS --no-positivity-check #-}

module NegativeImpredicative where

module Meta where
  data ⊥ : Set where

  record ⊤ : Set where

  data Bool : Set where
    false true : Bool

  record Σ (A : Set) (P : A → Set) : Set where
    field
      fst : A
      snd : P fst

  data Eq {A : Set} (x : A) : A → Set where
    refl : Eq x x

mutual
  data P : Set where
    ⊥ ⊤ : P
    ∀̂   : (s : U) (q : T s → P) → P

  Prf : P → Set
  Prf ⊥       = Meta.⊥
  Prf ⊤       = Meta.⊤
  Prf (∀̂ s p) = (x : T s) → Prf (p x)

  data U : Set where
    Z O B p : U
    Π Σ : (s : U) (f : T s → U) → U
    prf : P → U

  T : U → Set
  T p       = P
  T Z       = Meta.⊥
  T O       = Meta.⊤
  T B       = Meta.Bool
  T (Π s f) = (x : T s) → T (f x)
  T (Σ s f) = Meta.Σ (T s) (\x → T (f x))
  T (prf q) = Prf q

bad₁ : (P → P) → P
bad₁ f = ∀̂ p f

bad₂ : P → P → P
bad₂ (∀̂ p q)       = q
bad₂ _             = λ _ → ⊥

ω : P → P
ω q = bad₂ q q

Ω : P
Ω = ω (bad₁ ω)

-- Ω = ω (bad₁ ω)
--   = bad₂ (bad₁ ω) (bad₁ ω)  <--\
--   = bad₂ (∀̂ p ω) (bad₁ ω)      |
--   = ω (bad₁ ω)                 |
--   = bad₂ (bad₁ ω) (bad₁ ω)  <--/
