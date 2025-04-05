{-# OPTIONS --no-positivity-check #-}

-- Hurkens' paradox, as distributed in the Agda test suite,
-- using induction-recursion to model an impredicative hierarchy
-- of universes.

module IRHurkens where

mutual
  -- Defining impredicative universes requires the positivity
  -- checker to be off.

  -- U₀ is closed under Π-types with a domain from any other
  -- universe.
  data U₀ : Set where
    Π₀ : (s : U₀) (f : T₀ s → U₀) → U₀
    Π₁ : (s : U₁) (f : T₁ s → U₀) → U₀
    Π₂ : (s : U₂) (f : T₂ s → U₀) → U₀

  T₀ : U₀ → Set
  T₀ (Π₀ s f) = (x : T₀ s) → T₀ (f x)
  T₀ (Π₁ s f) = (x : T₁ s) → T₀ (f x)
  T₀ (Π₂ s f) = (x : T₂ s) → T₀ (f x)

  -- U₁ is closed under similar Π-types, and contains a code
  -- for U₀. Quantification over U₀ is not actually necessary, though.
  data U₁ : Set where
    Π₁ : (s : U₁) (f : T₁ s → U₁) → U₁
    Π₂ : (s : U₂) (f : T₂ s → U₁) → U₁
    ∗  : U₁

  T₁ : U₁ → Set
  T₁ (Π₁ s f) = (x : T₁ s) → T₁ (f x)
  T₁ (Π₂ s f) = (x : T₂ s) → T₁ (f x)
  T₁ ∗        = U₀

  -- U₂ contains only a code for U₁
  data U₂ : Set where
    □ : U₂

  T₂ : U₂ → Set
  T₂ □ = U₁

-- Some handy abbreviations
_₀⇒₀_ : U₀ → U₀ → U₀
A ₀⇒₀ B = Π₀ A \_ → B

_₁⇒₁_ : U₁ → U₁ → U₁
A ₁⇒₁ B = Π₁ A \_ → B

-- The 'empty' type, for which we will provide an inhabitant.
⊥ : U₀
⊥ = Π₁ ∗ \A → A

-- This is an abbreviation, as can be seen from the Agda function
-- space in the type. It could be made an inhabitant of ∗ ₁⇒₁ ∗, though.
¬_ : U₀ → U₀
¬ A = A ₀⇒₀ ⊥

-- This is not optional as an abbreviation, since there is no Π in
-- U₂.
P : U₁ → U₁
P A = A ₁⇒₁ ∗

U : U₁
U = Π₂ □ \X → (P (P X) ₁⇒₁ X) ₁⇒₁ P (P X)

τ : T₁ (P (P U) ₁⇒₁ U)
τ t = λ X f p → t (λ x → p (f (x X f)))

σ : T₁ (U ₁⇒₁ P (P U))
σ s = s U τ

Δ : T₁ (P U)
Δ = λ y → ¬ Π₁ (P U) \p → σ y p ₀⇒₀ p (τ (σ y))

Ω : T₁ U
Ω = τ (λ p → Π₁ U \x → σ x p ₀⇒₀ p x)

D : U₀
D = Π₁ (P U) \p → σ Ω p ₀⇒₀ p (τ (σ Ω))

lem₁ : T₀ (Π₁ (P U) \p → (Π₁ U \x → σ x p ₀⇒₀ p x) ₀⇒₀ p Ω)
lem₁ p H1 = H1 Ω (λ x → H1 (τ (σ x)))

lem₂ : T₀ (¬ D)
lem₂ = lem₁ Δ (λ x H2 H3 → H3 Δ H2 (λ p → H3 (λ y → p (τ (σ y)))))

lem₃ : T₀ D
lem₃ p = lem₁ (λ y → p (τ (σ y)))

loop : T₀ ⊥
loop = lem₂ lem₃
