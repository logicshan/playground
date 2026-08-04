module Setoids where

open import Level using (Level; _⊔_; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

-- ============================================================================
-- 1. Setoid 定义
-- c: 载体类型 (Carrier) 的宇宙层级
-- ℓ: 等价关系 (_∼_) 的宇宙层级
-- ============================================================================
record Setoid (c ℓ : Level) : Set (suc (c ⊔ ℓ)) where
  infix 2 _∼_
  field
    Carrier : Set c
    _∼_     : Carrier → Carrier → Set ℓ
    refl∼   : {x : Carrier} → x ∼ x
    sym∼    : {x y : Carrier} → x ∼ y → y ∼ x
    trans∼  : {x y z : Carrier} → y ∼ z → x ∼ y → x ∼ z

-- ============================================================================
-- 2. 保等价关系的态射 (Setoid 间的函数)
-- 解耦了源 Setoid 与目标 Setoid 的宇宙层级
-- ============================================================================
record Fun∼ {c₁ ℓ₁ c₂ ℓ₂} (X : Setoid c₁ ℓ₁) (Y : Setoid c₂ ℓ₂) : Set (c₁ ⊔ ℓ₁ ⊔ c₂ ⊔ ℓ₂) where
  private
    module X = Setoid X
    module Y = Setoid Y

  field
    function  : X.Carrier → Y.Carrier
    respects∼ : {x₀ x₁ : X.Carrier} → x₀ X.∼ x₁ → function x₀ Y.∼ function x₁

-- ============================================================================
-- 3. 函数 Setoid (以外延相等作为等价关系)
-- ============================================================================
FunSetoid : ∀ {c₁ ℓ₁ c₂ ℓ₂} → Setoid c₁ ℓ₁ → Setoid c₂ ℓ₂ → Setoid (c₁ ⊔ ℓ₁ ⊔ c₂ ⊔ ℓ₂) (c₁ ⊔ ℓ₂)
FunSetoid X Y = record
  { Carrier = Fun∼ X Y
  ; _∼_     = λ f g → ∀ x → function f x Y.∼ function g x
  ; refl∼   = λ x → Y.refl∼
  ; sym∼    = λ f∼g x → Y.sym∼ (f∼g x)
  ; trans∼  = λ g∼h f∼g x → Y.trans∼ (g∼h x) (f∼g x)
  }
  where
  open Fun∼
  module Y = Setoid Y

-- ============================================================================
-- 4. 离散 Setoid (由命题相等构造)
-- ============================================================================
strictSetoid : ∀ {c} → Set c → Setoid c c
strictSetoid A = record
  { Carrier = A
  ; _∼_     = _≡_
  ; refl∼   = refl
  ; sym∼    = sym
  ; trans∼  = λ g∼h f∼g → trans f∼g g∼h
  }
