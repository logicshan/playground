module Equality where

infix  2 _≡_
infix  2 _≠_

open import Logic

data _≡_ {X : Set} : X → X → Ω where
  reflexivity : {x : X} -> x ≡ x

_≠_ : {X : Set} → X → X → Ω
x ≠ y = ¬(x ≡ y)

two-things-equal-to-a-third-are-equal : {X : Set} →
             ∀(x y z : X) → x ≡ y ∧ x ≡ z → y ≡ z

two-things-equal-to-a-third-are-equal x .x .x (∧-intro reflexivity reflexivity) = reflexivity

transitivity : {X : Set} → {x y z : X} →  x ≡ y  →  y ≡ z  →  x ≡ z
transitivity {X} {x} {.x} {.x} reflexivity reflexivity = reflexivity

symmetry : {X : Set} → {x y : X} → x ≡ y → y ≡ x
symmetry {X} {x} {.x} reflexivity = reflexivity

compositionality : {X Y : Set} → ∀(f : X → Y) → {x₀ x₁ : X} → x₀ ≡ x₁ →  f x₀ ≡ f x₁
compositionality {X} {Y} f {x} {.x} reflexivity = reflexivity

predicate-compositionality : {X : Set} (A : X → Ω) → {x y : X} → x ≡ y → A x → A y
predicate-compositionality A reflexivity a = a

predicate-compositionality' : {X : Set} {A : X → Ω} → {x y : X} → x ≡ y → A x → A y
predicate-compositionality' reflexivity a = a

set-compositionality : {I : Set} (X : I → Set) → {i j : I} → i ≡ j → X i → X j
set-compositionality X reflexivity x = x

