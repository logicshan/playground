{-# OPTIONS --postfix-projections #-}

module WISC where

open import Level
open import Function hiding (_↠_ ; _⟶_)
open import Function.Equality hiding (_∘_)

open import Relation.Binary
import Relation.Binary.PropositionalEquality as PE

open import Data.Product as Prod
open Prod using (Σ ; Σ-syntax)

open import Data.Unit using (⊤)

variable
  c c₁ c₂ r r₁ r₂ : Level
  A B : Setoid c r

-- Predicates that respect a setoid equivalence. It is intended that
-- the underlying predicate be considered propositional, so no
-- relation is given on its carrier, since it should just be the
-- trivially true relation.
--
-- With types:
--   A → Prop <-- use your favorite extensional Prop
record Predicoid c₂ (A : Setoid c₁ r₁) : Set (suc c₂ ⊔ c₁ ⊔ r₁) where
  open Setoid A renaming (Carrier to |A|)
  field
    Pred : |A| → Set c₂
    ext : ∀ x y → x ≈ y → Pred x → Pred y

module _ where
  open Π

  -- With types:
  --   Surj f = ∀ y → ∃[ x ] f x ≡ y
  Surj : Predicoid _ (A ⇨ B)
  Surj {B = B} .Predicoid.Pred f
    = ∀ y → Σ[ x ∈ _ ] (f ⟨$⟩ x ≈ y)
    where open Setoid B
  Surj {A = A} {B = B} .Predicoid.ext f g f~g sf y with sf y
  ... | (x , fx~y) = λ where
      .proj₁ → x
      .proj₂ → trans (sym (f~g (Setoid.refl A))) fx~y
    where open Setoid B

module _ where
  open Setoid
  open Predicoid

  -- With types:
  --   Sub A P = Σ A P
  --
  -- This is a simplified definition based on the idea that P is meant
  -- to be propositional, so the triviality of P's equivalence is
  -- incorporated into the definition.
  Sub : (A : Setoid c₁ r₁) → (P : Predicoid c₂ A) → Setoid _ _
  Sub A P .Setoid.Carrier = Σ (Carrier A) (Pred P)
  Sub A P .Setoid._≈_ (x , _) (y Prod., _) = _≈_ A x y
  -- not inferred
  Sub A P .Setoid.isEquivalence = λ where
    .IsEquivalence.refl → IsEquivalence.refl (isEquivalence A)
    .IsEquivalence.sym → IsEquivalence.sym (isEquivalence A)
    .IsEquivalence.trans → IsEquivalence.trans (isEquivalence A)

  -- The setoid of surjections
  _↠_ : Setoid c₁ r₁ → Setoid c₂ r₂ → Setoid _ _
  A ↠ B = Sub (A ⇨ B) Surj

  -- !A is the setoid consisting of the carriers of A up to equality
  ! : Setoid c r → Setoid c c
  ! A .Carrier = Carrier A
  ! A ._≈_ = PE._≡_
  ! A .isEquivalence = PE.isEquivalence

  cover! : (X : Setoid c r) → Carrier (! X ↠ X)
  cover! X .proj₁ ._⟨$⟩_ x = x
  cover! X .proj₁ .cong = reflexive X
  cover! X .proj₂ x = x Prod., refl X

module WISC
  {X : Setoid c₁ r₁}
  {Y : Setoid c₂ r₂}
  ((f , surj) : Setoid.Carrier (Y ↠ X))
  where
  g : (! X) ⟶ Y
  g ._⟨$⟩_ x = surj x .proj₁
  g .cong = λ e → reflexive (PE.cong (proj₁ ∘ surj) e)
    where open Setoid Y

  open Setoid X renaming (Carrier to |X|)

  -- With types:
  --   ∀ x → f (g x) ≡ proj₁ cover x
  --
  -- Agda can't infer X for cover!
  g-comm : ∀ x → (f ⟨$⟩ (g ⟨$⟩ x)) ≈ (proj₁ (cover! X) ⟨$⟩ x)
  g-comm x = surj x .proj₂
