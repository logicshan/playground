
open import Function
open import Data.Product
open import Relation.Binary.PropositionalEquality

module HEqExt (funExt : ∀{A B : Set} {f g : A -> B} → (∀ x → f x ≡ g x) -> f ≡ g) where

variable
  A B C : Set

cast : A ≡ B -> A -> B
cast refl x = x

module Sigma where
  HEq : A -> B -> Set _
  HEq {A} {B} x y = Σ[ P ∈ A ≡ B ] cast P x ≡ y

  heq-funext₁ : (P : A ≡ B) (f : A -> C) (g : B -> C) -> (∀ x → f x ≡ g (cast P x)) -> HEq f g
  heq-funext₁ refl f g e = refl , funExt e

  heq-funext₂ : (P : A ≡ B) (f : A -> C) (g : B -> C) -> (∀ x → f x ≡ g (cast P x)) -> HEq f g
  heq-funext₂ {C = C} P f = J Q P λ g e → refl , funExt e
    where
    Q : (Z : Set) -> _ ≡ Z -> _
    Q Z Q = (g : Z -> C) -> (∀ x → f x ≡ g (cast Q x)) -> HEq f g

module STD where
  open import Relation.Binary.HeterogeneousEquality

  heq-funext : (P : A ≡ B)  (f : A -> C) (g : B -> C) -> (∀ x → f x ≡ g (cast P x)) -> f ≅ g
  heq-funext refl f g e = reflexive (funExt e)
