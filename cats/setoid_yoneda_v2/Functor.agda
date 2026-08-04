module Functor where

open import Level using (Level; _⊔_)
open import Setoids
open import Category

-- ============================================================================
-- 1. 函子 (Functor) 定义
-- ============================================================================
record _=>_ {a b c a' b' c'} (C : Cat a b c) (D : Cat a' b' c')
  : Set (a ⊔ a' ⊔ b ⊔ b' ⊔ c ⊔ c') where
  field
    object    : ob C → ob D
    hom       : {X Y : ob C} → C 〈 X , Y 〉 → D 〈 object X , object Y 〉
    hom∼      : {X Y : ob C} {f g : C 〈 X , Y 〉} → C ! f ∼ g → D ! hom f ∼ hom g
    identity∼ : {X : ob C} → D ! hom (id C X) ∼ id D (object X)
    comp∼     : {X Y Z : ob C} (f : C 〈 Y , Z 〉) (g : C 〈 X , Y 〉)
              → D ! hom (C ! f ∘ g) ∼ (D ! hom f ∘ hom g)

-- ============================================================================
-- 2. 函子作用简写记号
-- ============================================================================
-- 函子作用于对象
_`_ : ∀ {a b c a' b' c'} {X : Cat a b c} {Y : Cat a' b' c'}
    → X => Y → ob X → ob Y
F ` x = _=>_.object F x

-- 函子作用于态射
_``_ : ∀ {a b c a' b' c'} {X : Cat a b c} {Y : Cat a' b' c'}
     {x₀ x₁ : ob X} → (F : X => Y) → X 〈 x₀ , x₁ 〉 → Y 〈 F ` x₀ , F ` x₁ 〉
F `` f = _=>_.hom F f

-- ============================================================================
-- 3. 反变 Hom 函子 (Contravariant Hom-Functor)
-- h : C(V, U) = C_op(U, V)
-- ============================================================================
_〈-,_〉 : ∀ {a b c} → (C : Cat a b c) → (X : ob C) → (C op) => SETOID b c
C 〈-, X 〉 = record
  { object    = λ U → C ⟪ U , X ⟫
  ; hom       = λ h → record
    { function  = λ f → C ! f ∘ h
    ; respects∼ = λ f₀∼f₁ → C !! f₀∼f₁ ∘ Setoid.refl∼ (C ⟪ _ , _ ⟫)
    }
  ; hom∼      = λ f∼g x → C !! Setoid.refl∼ (C ⟪ _ , _ ⟫) ∘ f∼g
  ; identity∼ = λ f → Cat.right-identity∼ C f
  ; comp∼     = λ f g x → Setoid.sym∼ (C ⟪ _ , _ ⟫) (Cat.associativity∼ C x g f)
  }
