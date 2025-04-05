module Logic where

infixr 1 _∨_
infixr 0 _∧_

-- Type of propositions denoted by Ω, like in a topos:

Ω = Set

data ⊥ : Ω where
-- nothing defined here: there are not constructors of this type.

⊥-elim : {A : Ω} → ⊥ → A
⊥-elim = λ ()

¬ : Ω → Ω
¬ A = (A → ⊥)

data ⊤ : Ω where
 * : ⊤

data _∧_ (A₀ A₁ : Ω) : Ω where
  ∧-intro : A₀ → A₁ → A₀ ∧ A₁

∧-elim₀ : {A₀ A₁ : Ω} → A₀ ∧ A₁ → A₀
∧-elim₀ (∧-intro a₀ a₁) = a₀

∧-elim₁ : {A₀ A₁ : Ω} → A₀ ∧ A₁ → A₁
∧-elim₁ (∧-intro a₀ a₁) = a₁

data _∨_ (A₀ A₁ : Ω) : Ω where
  ∨-intro₀ : A₀ → A₀ ∨ A₁
  ∨-intro₁ : A₁ → A₀ ∨ A₁

∨-elim : {A₀ A₁ B : Ω} → (A₀ → B) → (A₁ → B) → A₀ ∨ A₁ → B
∨-elim f₀ f₁ (∨-intro₀ a₀) = f₀ a₀
∨-elim f₀ f₁ (∨-intro₁ a₁) = f₁ a₁

decidable : Ω → Ω
decidable A = A ∨ ¬ A 

data ∃ {X : Set} (A : X → Ω) : Ω where
     ∃-intro : (x₀ : X) → A x₀ → ∃(\(x : X) → A x)

∃-witness : {X : Set} {A : X → Ω} → ∃(\(x : X) → A x) → X
∃-witness (∃-intro x a) = x

∃-elim : {X : Set} {A : X → Ω} → (proof : ∃(\(x : X) → A x)) → A (∃-witness proof)
∃-elim (∃-intro x a) = a

inhabited : Set → Ω
inhabited X = ∃(\(x : X) → ⊤)

_⇔_ : Ω → Ω → Ω
A ⇔ B = (A → B) ∧ (B → A)
