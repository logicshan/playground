module Yoneda where

open import Level using (Level; _⊔_)
open import Setoids
open import Category
open import Functor
open import NaturalTransformation

-- ============================================================================
-- 1. 米田引理中的同构映射 Φ 与 Ψ
-- ============================================================================

-- Φ : 将自然变换转换为态射
Φ : ∀ {a b c} {C : Cat a b c} {x y : ob C}
  → [ C op , SETOID b c ] 〈 C 〈-, x 〉 , C 〈-, y 〉 〉 → C 〈 x , y 〉
Φ {C = C} {x = x} δ = Fun∼.function (δ ↓ x) (id C x)

-- Ψ : 将态射转换为自然变换
Ψ : ∀ {a b c} {C : Cat a b c} {x y : ob C}
  → C 〈 x , y 〉 → [ C op , SETOID b c ] 〈 C 〈-, x 〉 , C 〈-, y 〉 〉
Ψ {C = C} {x = x} {y = y} f = record
  { object     = λ u → record
    { function  = λ h → C ! f ∘ h
    ; respects∼ = λ h∼k → C !! Setoid.refl∼ (C ⟪ x , y ⟫) ∘ h∼k
    }
  ; naturality = λ g h → Cat.associativity∼ C f h g
  }

-- ============================================================================
-- 2. 米田引理 (Yoneda Lemma)
-- ============================================================================

-- 引理 1: δ ∼ Ψ (Φ δ) (自然变换与其由 Φ 导出的自然变换外延相等)
Lemma1 : ∀ {a b c} {C : Cat a b c} {x y : ob C}
       (δ : [ C op , SETOID b c ] 〈 C 〈-, x 〉 , C 〈-, y 〉 〉)
       → [ C op , SETOID b c ] ! δ ∼ Ψ (Φ δ)
Lemma1 {C = C} {x = x} {y = y} δ u h =
  Setoid.sym∼ (C ⟪ u , y ⟫)
    (Setoid.trans∼ (C ⟪ u , y ⟫)
      (Fun∼.respects∼ (δ ↓ u) (Cat.left-identity∼ C h))
      (_≐>_.naturality δ h (id C x)))

-- 引理 2: f ∼ Φ (Ψ f) (态射与其由 Ψ 导出的态射等价)
Lemma2 : ∀ {a b c} {C : Cat a b c} {x y : ob C}
       (f : C 〈 x , y 〉) → C ! f ∼ Φ (Ψ {C = C} f)
Lemma2 {C = C} f = Setoid.sym∼ (C ⟪ _ , _ ⟫) (Cat.right-identity∼ C f)

-- ============================================================================
-- 3. 米田嵌入 (Yoneda Embedding)
-- C → [ C^op , SETOID ]
-- ============================================================================
¥ : ∀ {a b c} (C : Cat a b c) → C => [ C op , SETOID b c ]
¥ C = record
  { object     = λ X → C 〈-, X 〉
  ; hom        = λ f → C 〈-,, f 〉
  ; hom∼       = λ {X = X} f∼g U h → C !! f∼g ∘ Setoid.refl∼ (C ⟪ U , X ⟫)
  ; identity∼  = λ U f → Cat.left-identity∼ C f
  ; comp∼      = λ f g U h → Cat.associativity∼ C f g h
  }
