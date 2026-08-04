module Category where

open import Level using (Level; _⊔_; suc)
open import Function using (_∘_)
open import Setoids

-- ============================================================================
-- 1. 辅助函数：提取 Hom Setoid 的 Carrier (底层态射集合)
-- ============================================================================
∥_∥ : ∀ {a b c} {X : Set a} → (X → X → Setoid b c) → X → X → Set b
∥ h ∥ x y = Setoid.Carrier (h x y)

-- ============================================================================
-- 2. 范畴 (Category) 定义
-- a: 对象 (object) 的宇宙层级
-- b: 态射集合 (hom-set) 的宇宙层级
-- c: 态射相等关系 (hom-equality) 的宇宙层级
-- ============================================================================
record Cat (a b c : Level) : Set (suc (a ⊔ b ⊔ c)) where
  field
    object         : Set a
    hom            : object → object → Setoid b c
    identity       : (x : object) → ∥ hom ∥ x x
    comp           : {x y z : object} → ∥ hom ∥ y z → ∥ hom ∥ x y → ∥ hom ∥ x z
    comp∼          : {x y z : object} {g₀ g₁ : ∥ hom ∥ y z} {f₀ f₁ : ∥ hom ∥ x y}
                   → Setoid._∼_ (hom y z) g₀ g₁
                   → Setoid._∼_ (hom x y) f₀ f₁
                   → Setoid._∼_ (hom x z) (comp g₀ f₀) (comp g₁ f₁)
    associativity∼ : {w x y z : object} (f : ∥ hom ∥ y z) (g : ∥ hom ∥ x y) (h : ∥ hom ∥ w x)
                   → Setoid._∼_ (hom w z) (comp (comp f g) h) (comp f (comp g h))
    left-identity∼ : {x y : object} (f : ∥ hom ∥ x y)
                   → Setoid._∼_ (hom x y) (comp (identity y) f) f
    right-identity∼ : {x y : object} (f : ∥ hom ∥ x y)
                   → Setoid._∼_ (hom x y) (comp f (identity x)) f

-- ============================================================================
-- 3. 范畴记号与导出运算
-- ============================================================================
ob : ∀ {a b c} → Cat a b c → Set a
ob = Cat.object

-- 态射 Carrier 简写
_〈_,_〉 : ∀ {a b c} → (C : Cat a b c) → ob C → ob C → Set b
C 〈 X , Y 〉 = ∥ Cat.hom C ∥ X Y

-- Hom Setoid 简写
_⟪_,_⟫ : ∀ {a b c} → (C : Cat a b c) → ob C → ob C → Setoid b c
C ⟪ X , Y ⟫ = Cat.hom C X Y

-- 态射相等关系
_!_∼_ : ∀ {a b c} → (C : Cat a b c) {X Y : ob C} → C 〈 X , Y 〉 → C 〈 X , Y 〉 → Set c
_!_∼_ C {X} {Y} f g = Setoid._∼_ (C ⟪ X , Y ⟫) f g

-- 恒等态射
id : ∀ {a b c} → (C : Cat a b c) → (x : ob C) → C 〈 x , x 〉
id C x = Cat.identity C x

-- 态射复合
_!_∘_ : ∀ {a b c} → (C : Cat a b c) {x y z : ob C} → C 〈 y , z 〉 → C 〈 x , y 〉 → C 〈 x , z 〉
C ! g ∘ f = Cat.comp C g f

-- 态射复合的保关系性质 (Congruence)
_!!_∘_ : ∀ {a b c} (C : Cat a b c) {x y z : ob C}
         {g₀ g₁ : C 〈 y , z 〉} {f₀ f₁ : C 〈 x , y 〉}
       → C ! g₀ ∼ g₁
       → C ! f₀ ∼ f₁
       → C ! (C ! g₀ ∘ f₀) ∼ (C ! g₁ ∘ f₁)
_!!_∘_ C g0∼g1 f0∼f1 = Cat.comp∼ C g0∼g1 f0∼f1

-- ============================================================================
-- 4. SETOID 范畴
-- 对象为 Setoid，态射为保关系的函数 (FunSetoid)
-- ============================================================================
SETOID : (a b : Level) → Cat (suc (a ⊔ b)) (a ⊔ b) (a ⊔ b)
SETOID a b = record
  { object   = Setoid a b
  ; hom      = FunSetoid
  ; identity = λ X → record
    { function  = λ x → x
    ; respects∼ = λ x0∼x1 → x0∼x1
    }
  ; comp     = λ g f → record
    { function  = Fun∼.function g ∘ Fun∼.function f
    ; respects∼ = Fun∼.respects∼ g ∘ Fun∼.respects∼ f
    }
  ; comp∼    = λ {X} {Y} {Z} {g₀} {g₁} {f₀} {f₁} g0∼g1 f0∼f1 x →
      let module Z = Setoid Z
          module G₀ = Fun∼ g₀
          module F₁ = Fun∼ f₁
      in Z.trans∼ (g0∼g1 (F₁.function x)) (G₀.respects∼ (f0∼f1 x))
  ; associativity∼ = λ {_ _ _ Z} _ _ _ _ → Setoid.refl∼ Z
  ; left-identity∼   = λ {_ Y} _ _ → Setoid.refl∼ Y
  ; right-identity∼  = λ {_ Y} _ _ → Setoid.refl∼ Y
  }

-- ============================================================================
-- 5. 对偶范畴 (Opposite / Dual Category)
-- ============================================================================
_op : ∀ {a b c} → Cat a b c → Cat a b c
C op = record
  { object         = ob C
  ; hom            = λ x y → C ⟪ y , x ⟫
  ; identity       = id C
  ; comp           = λ f g → C ! g ∘ f
  ; comp∼          = λ g0∼g1 f0∼f1 → C !! f0∼f1 ∘ g0∼g1
  ; associativity∼ = λ f g h → Setoid.sym∼ (C ⟪ _ , _ ⟫) (Cat.associativity∼ C h g f)
  ; left-identity∼ = Cat.right-identity∼ C
  ; right-identity∼ = Cat.left-identity∼ C
  }
