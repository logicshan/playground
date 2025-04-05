module Monoid where

open import Data.List using (List; _∷_; []; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)


-- 自由幺半群模型的定义
record MonoidModel (A : Set) : Set₁ where
  field
    C      : Set
    f      : A → C
    _∘_    : C → C → C
    id     : C
    assoc  : ∀ {a b c : C} → (a ∘ b) ∘ c ≡ a ∘ (b ∘ c)
    idl    : ∀ {a : C} → id ∘ a ≡ a
    idr    : ∀ {a : C} → a ∘ id ≡ a

module FreeMonoid (A : Set) where
  postulate
    C      : Set
    f      : A → C
    _∘_    : C → C → C
    id     : C
    assoc  : ∀ {a b c : C} → (a ∘ b) ∘ c ≡ a ∘ (b ∘ c)
    idl    : ∀ {a : C} → id ∘ a ≡ a
    idr    : ∀ {a : C} → a ∘ id ≡ a
