module Verona2024.Basics.Common where

infix 1 _∨_
data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

infixr 2 _∧_
infixr 4 _,_
data _∧_ (A B : Set) : Set where
  _,_ : A → B → A ∧ B

data ⊥ : Set where

infix 3 ¬_
¬_ : Set → Set
¬ X = X → ⊥

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

data _≡_ {X : Set} : X → X → Set where
  refl : {x : X} → x ≡ x

trans : {X : Set} {x y z : X} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

data Bool : Set where
  false true : Bool

infix 2 Σ
data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (x : A) → (y : B x) → Σ A B

syntax Σ A (λ x → B) = Σ[ x ∈ A ] B

subst : {A : Set} (P : A → Set) {x y : A} → (x ≡ y) → P x → P y
subst P refl u = u

data _≤_ : ℕ → ℕ → Set where
  ≤-base : {x : ℕ} → zero ≤ x
  ≤-succ : {x y : ℕ} → x ≤ y → succ x ≤ succ y

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()
