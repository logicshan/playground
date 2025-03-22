{-# OPTIONS --universe-polymorphism #-}

module Setoids where
open import Level
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

record Setoid (a b : Level) : Set (suc (a ⊔ b)) where
  infix 2 _∼_
  field
    object : Set a
    _∼_ : object → object → Set b
    refl∼ : {x : object} → x ∼ x
    sym∼ : {x y : object} → x ∼ y → y ∼ x
    trans∼ : {x y z : object} → y ∼ z → x ∼ y → x ∼ z

-- Fun∼ is the set of functions which respects
-- the attached equivalence relation
record Fun∼ {a b} (X Y : Setoid a b) : Set (a ⊔ b) where
  field
    function : Setoid.object X → Setoid.object Y
    respects∼ : {x0 x1 : Setoid.object X} → (let open Setoid X in x0 ∼ x1) →
            (let open Setoid Y in function x0 ∼ function x1)
-- FunSetoid X Y is a Setoid0 on top of Fun∼ X Y;
-- its equality is taken to be the extensional one
-- with respect to the target Setoid0 equality.
FunSetoid : ∀ {a b} → Setoid a b → Setoid a b → Setoid (a ⊔ b) (a ⊔ b)
FunSetoid X Y = record { object = Fun∼ X Y
                    ; _∼_ = λ F → λ G → (x : Setoid.object X) →
                        Setoid._∼_  Y (Fun∼.function F x) (Fun∼.function G x)
                    ; refl∼ = λ x → Setoid.refl∼ Y
                    ; sym∼ = λ p → λ x → Setoid.sym∼ Y (p x)
                    ; trans∼ = λ g∼h → λ f∼g → λ x →
                               Setoid.trans∼ Y (g∼h x) (f∼g x)
                    }

strictSetoid : ∀ {a} → Set a → Setoid a a
strictSetoid A = record
  { object = A
  ; _∼_ = _≡_
  ; refl∼ = refl
  ; sym∼ = sym≡
  ; trans∼ = trans≡
  }
  where
  sym≡ : ∀ {a} {X : Set a} {t u : X} → t ≡ u → u ≡ t
  sym≡ {_} {t = x} {u = .x} refl = refl
  trans≡ : ∀ {a}{X : Set a} → {t u v : X} → u ≡ v → t ≡ u → t ≡ v
  trans≡ {_} {t = x} {u = .x} {v = .x} refl refl = refl
