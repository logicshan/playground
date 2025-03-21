{-# OPTIONS --without-K --safe #-}

module LatticeCat where

open import Level
open import Data.Product using (Σ; _,_)
open import Function.Base using (_∘_; id)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl; cong)

-- 从 agda-stdlib 导入格的定义
open import Algebra.Lattice.Bundles
open import Algebra.Lattice.Properties.Lattice
open import Algebra.Lattice.Structures

-- 从 agda-categories 导入范畴相关定义
open import Categories.Category

-- 定义格之间的同态（保持 join 和 meet 运算的映射）
record LatticeHom {c₁ ℓ₁ c₂ ℓ₂} (L₁ : Lattice c₁ ℓ₁) (L₂ : Lattice c₂ ℓ₂) : Set (c₁ ⊔ ℓ₁ ⊔ c₂ ⊔ ℓ₂) where
  private 
    module L₁ = Lattice L₁
    module L₂ = Lattice L₂

  field
    -- 底层的函数
    morphism : L₁.Carrier → L₂.Carrier 
    -- 保持 join(∨) 运算
    preserve-∨ : ∀ x y → morphism (x L₁.∨ y) ≡ (morphism x) L₂.∨ (morphism y)
    -- 保持 meet(∧) 运算
    preserve-∧ : ∀ x y → morphism (x L₁.∧ y) ≡ (morphism x) L₂.∧ (morphism y)

-- 格同态的复合
∘-LatticeHom : ∀ {c₁ ℓ₁ c₂ ℓ₂ c₃ ℓ₃}
             {L₁ : Lattice c₁ ℓ₁} {L₂ : Lattice c₂ ℓ₂} {L₃ : Lattice c₃ ℓ₃}
             → LatticeHom L₂ L₃ → LatticeHom L₁ L₂ → LatticeHom L₁ L₃
∘-LatticeHom {L₁ = L₁} {L₂} {L₃} g f = record
  { morphism = g.morphism ∘ f.morphism
  ; preserve-∨ = λ x y → begin
      (g.morphism ∘ f.morphism) (x L₁.∨ y)     ≡⟨ cong g.morphism (f.preserve-∨ x y) ⟩
      g.morphism (f.morphism x L₂.∨ f.morphism y) ≡⟨ g.preserve-∨ (f.morphism x) (f.morphism y) ⟩
      g.morphism (f.morphism x) L₃.∨ g.morphism (f.morphism y) ∎
  ; preserve-∧ = λ x y → begin
      (g.morphism ∘ f.morphism) (x L₁.∧ y)     ≡⟨ cong g.morphism (f.preserve-∧ x y) ⟩
      g.morphism (f.morphism x L₂.∧ f.morphism y) ≡⟨ g.preserve-∧ (f.morphism x) (f.morphism y) ⟩
      g.morphism (f.morphism x) L₃.∧ g.morphism (f.morphism y) ∎
  }
  where
    module L₁ = Lattice L₁
    module L₂ = Lattice L₂
    module L₃ = Lattice L₃
    module f = LatticeHom f
    module g = LatticeHom g
    open ≡.≡-Reasoning

-- 恒等格同态
id-LatticeHom : ∀ {c ℓ} {L : Lattice c ℓ} → LatticeHom L L
id-LatticeHom = record
  { morphism = id
  ; preserve-∨ = λ _ _ → refl
  ; preserve-∧ = λ _ _ → refl
  }

-- 定义所有格构成的范畴
LatticeCategory : ∀ c ℓ → Category _ _ _  
LatticeCategory c ℓ = record
  { Obj = Lattice c ℓ
  ; _⇒_ = LatticeHom
  ; _≈_ = λ f g → ∀ x → LatticeHom.morphism f x ≡ LatticeHom.morphism g x  -- 态射等价关系
  ; id = id-LatticeHom
  ; _∘_ = ∘-LatticeHom
  ; assoc = λ _ → refl
  ; sym-assoc = λ _ → refl
  ; identityˡ = λ _ → refl
  ; identityʳ = λ _ → refl
  ; identity² = λ _ → refl
  ; equiv = record
    { refl = λ _ → refl
    ; sym = λ f≈g x → ≡.sym (f≈g x)
    ; trans = λ f≈g g≈h x → ≡.trans (f≈g x) (g≈h x)
    }
  ; ∘-resp-≈ = λ {_} {_} {_} {f} {h} {g} {i} f≈h g≈i x →
-- λ {_} {_} {_} {f} {h} {g} {i} f≈h g≈i x → ?
      begin
        LatticeHom.morphism f (LatticeHom.morphism g x)
      ≡⟨ cong (LatticeHom.morphism f) (g≈i x) ⟩
        LatticeHom.morphism f (LatticeHom.morphism i x)
      ≡⟨ f≈h (LatticeHom.morphism i x) ⟩
        LatticeHom.morphism h (LatticeHom.morphism i x)
      ≡⟨ refl ⟩
        LatticeHom.morphism h (LatticeHom.morphism i x)
      ∎
  }
  where open ≡.≡-Reasoning
