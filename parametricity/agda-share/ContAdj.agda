
module ContAdj where

open import Function

open import Relation.Binary.PropositionalEquality

_⇒_ : Set → Set → Set
A ⇒ B = A → B

_⇐_ : Set → Set → Set
A ⇐ B = B → A

module Result (R : Set) where
  -- (─ ⇒ R) : C → C^op
  map-⇒R : ∀{A B} → (A ⇒ B) → (A ⇒ R) ⇐ (B ⇒ R)
  map-⇒R f k = k ∘ f

  -- (R ⇐ ─) : C^op → C
  map-R⇐ : ∀{A B} → (A ⇐ B) → (R ⇐ A) ⇒ (R ⇐ B)
  map-R⇐ f k = k ∘ f

  -- (─ ⇒ R) ⊣ (R ⇐ ─)
  adj-l₁ : ∀{A B} → ((A ⇒ R) ⇐ B) → (A ⇒ (R ⇐ B))
  adj-l₁ f x y = f y x

  adj-r₁ : ∀{A B} → (A ⇒ (R ⇐ B)) → ((A ⇒ R) ⇐ B)
  adj-r₁ f y x = f x y

  lemma₁₁ : ∀{A B} (f : A ⇒ (R ⇐ B)) x y → adj-l₁ (adj-r₁ f) x y ≡ f x y
  lemma₁₁ f x y = refl

  lemma₁₂ : ∀{A B} (f : (A ⇒ R) ⇐ B) x y → adj-r₁ (adj-l₁ f) y x ≡ f y x
  lemma₁₂ f x y = refl

  -- (R ⇐ ─)^op : C → C^op
  -- (─ ⇒ R)^op : C^op → C
  --
  -- (R ⇐ ─)^op ⊣ (─ ⇒ R)^op
  adj-l₂ : ∀{A B} → ((R ⇐ A) ⇐ B) → (A ⇒ (B ⇒ R))
  adj-l₂ f x y = f y x

  adj-r₂ : ∀{A B} → (A ⇒ (B ⇒ R)) → ((R ⇐ A) ⇐ B)
  adj-r₂ f y x = f x y

  lemma₂₁ : ∀{A B} (f : A ⇒ (B ⇒ R)) x y → adj-l₂ (adj-r₂ f) x y ≡ f x y
  lemma₂₁ f x y = refl

  lemma₂₂ : ∀{A B} (f : (R ⇐ A) ⇐ B) x y → adj-r₂ (adj-l₂ f) y x ≡ f y x
  lemma₂₂ f x y = refl

  unit₁ : ∀{A} → A ⇒ (R ⇐ (A ⇒ R))
  unit₁ = adj-l₁ id

  counit₁ : ∀{A} → ((R ⇐ A) ⇒ R) ⇐ A
  counit₁ = adj-r₁ id

  unit₂ : ∀{A} → A ⇒ ((R ⇐ A) ⇒ R)
  unit₂ = adj-l₂ id

  counit₂ : ∀{A} → (R ⇐ (A ⇒ R)) ⇐ A
  counit₂ = adj-r₂ id
