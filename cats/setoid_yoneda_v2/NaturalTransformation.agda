module NaturalTransformation where

open import Level using (Level; _⊔_)
open import Setoids
open import Category
open import Functor
import SetoidEqReasoning as EQ

-- ============================================================================
-- 1. 自然变换 (Natural Transformation) 定义
-- ============================================================================
record _≐>_ {a b c a' b' c'} {C : Cat a b c} {D : Cat a' b' c'}
  (F G : C => D) : Set (a ⊔ b ⊔ b' ⊔ c') where
  field
    object     : (x : ob C) → D 〈 F ` x , G ` x 〉
    naturality : {x y : ob C} (f : C 〈 x , y 〉)
               → D ! D ! G `` f ∘ object x ∼ (D ! object y ∘ (F `` f))

open _≐>_

-- ============================================================================
-- 2. 自然变换作用于对象 (Component Extraction)
-- ============================================================================
_↓_ : ∀ {a b c a' b' c'} {C : Cat a b c} {D : Cat a' b' c'} {F G : C => D}
    → F ≐> G → (x : ob C) → D 〈 F ` x , G ` x 〉
α ↓ x = _≐>_.object α x

-- ============================================================================
-- 3. Hom 自然变换 (米田嵌入相关)
-- ============================================================================
_〈-,,_〉 : ∀ {a b c} → (C : Cat a b c) → {X Y : ob C} → C 〈 X , Y 〉 → (C 〈-, X 〉) ≐> (C 〈-, Y 〉)
_〈-,,_〉 C {X} {Y} f = record
  { object     = λ x → record
    { function  = λ h → C ! f ∘ h
    ; respects∼ = λ x₀∼x₁ → C !! Setoid.refl∼ (C ⟪ X , Y ⟫) ∘ x₀∼x₁
    }
  ; naturality = λ p q → Cat.associativity∼ C f q p
  }

-- ============================================================================
-- 4. 恒等自然变换 (Identity Natural Transformation)
-- ============================================================================
Id : ∀ {a b c a' b' c'} {C : Cat a b c} {D : Cat a' b' c'} (F : C => D) → F ≐> F
Id {D = D} F = record
  { object     = λ x → id D (F ` x)
  ; naturality = λ {X} {Y} f → Setoid.trans∼ (D ⟪ F ` X , F ` Y ⟫)
      (Setoid.sym∼ (D ⟪ F ` X , F ` Y ⟫) (Cat.left-identity∼ D (F `` f)))
      (Cat.right-identity∼ D (F `` f))
  }

-- ============================================================================
-- 5. 自然变换的外延相等与 Setoid (函子范畴的 Hom Setoid)
-- ============================================================================
eqNT : ∀ {a b c a' b' c'} {C : Cat a b c} {D : Cat a' b' c'} {F G : C => D}
     → (α β : F ≐> G) → Set (a ⊔ c')
eqNT {C = C} {D = D} α β = (x : ob C) → D ! α ↓ x ∼ (β ↓ x)

NTSetoid : ∀ {a b c a' b' c'} {C : Cat a b c} {D : Cat a' b' c'} (F G : C => D)
         → Setoid (a ⊔ b ⊔ b' ⊔ c') (a ⊔ c')
NTSetoid {C = C} {D = D} F G = record
  { Carrier = F ≐> G
  ; _∼_     = eqNT
  ; refl∼   = λ x → Setoid.refl∼ (D ⟪ _ , _ ⟫)
  ; sym∼    = λ α∼β x → Setoid.sym∼ (D ⟪ _ , _ ⟫) (α∼β x)
  ; trans∼  = λ β∼γ α∼β x → Setoid.trans∼ (D ⟪ _ , _ ⟫) (β∼γ x) (α∼β x)
  }

-- ============================================================================
-- 6. 自然变换的垂直复合 (Vertical Composition)
-- ============================================================================
_∙_ : ∀ {a b c a' b' c'} {C : Cat a b c} {D : Cat a' b' c'} {F G H : C => D}
    → (β : G ≐> H) (α : F ≐> G) → F ≐> H
_∙_ {C = C} {D = D} {F = F} {G = G} {H = H} β α = record
  { object     = λ x → D ! (β ↓ x) ∘ (α ↓ x)
  ; naturality = λ {x y} f →
      let open EQ (D ⟪ F ` x , H ` y ⟫)
          open Cat D
      in ∵ D ! H `` f ∘ (D ! β ↓ x ∘ (α ↓ x))
         ∼ D ! (D ! H `` f ∘ (β ↓ x)) ∘ (α ↓ x)
           yb associativity∼ (H `` f) (β ↓ x) (α ↓ x)
         ∼ D ! (D ! (β ↓ y) ∘ (G `` f)) ∘ (α ↓ x)
           by comp∼ (_≐>_.naturality β f) (Setoid.refl∼ (D ⟪ F ` x , G ` x ⟫))
         ∼ D ! (β ↓ y) ∘ (D ! G `` f ∘ (α ↓ x))
           by associativity∼ (β ↓ y) (G `` f) (α ↓ x)
         ∼ D ! (β ↓ y) ∘ (D ! (α ↓ y) ∘ (F `` f))
           by comp∼ (Setoid.refl∼ (D ⟪ G ` y , H ` y ⟫)) (_≐>_.naturality α f)
         ∼ D ! (D ! β ↓ y ∘ (α ↓ y)) ∘ (F `` f)
           yb associativity∼ (β ↓ y) (α ↓ y) (F `` f)
  }

-- ============================================================================
-- 7. 函子范畴 (Functor Category [C, D])
-- ============================================================================
[_,_] : ∀ {a b c a' b' c'} → Cat a b c → Cat a' b' c' → Cat (a ⊔ b ⊔ c ⊔ a' ⊔ b' ⊔ c') (a ⊔ b ⊔ b' ⊔ c') (a ⊔ c')
[ C , D ] = record
  { object          = C => D
  ; hom             = NTSetoid
  ; identity        = Id
  ; comp            = _∙_
  ; comp∼           = λ α∼β γ∼δ x → D.comp∼ (α∼β x) (γ∼δ x)
  ; associativity∼  = λ α β γ x → D.associativity∼ (α ↓ x) (β ↓ x) (γ ↓ x)
  ; left-identity∼  = λ α x → D.left-identity∼ (α ↓ x)
  ; right-identity∼ = λ α x → D.right-identity∼ (α ↓ x)
  }
  where
  module D = Cat D
