-- 导入必要的基础库和之前的德摩根代数定义
module DeMorganCategory where

open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary using (Rel; Setoid; IsEquivalence)
open import Algebra.Lattice using (Lattice; DeMorganAlgebra; IsLattice; IsDistributiveLattice; IsDeMorganAlgebra)
open import Function using (id; _∘_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl; cong; cong₂)

open import Categories.Category
{-
open import Categories.Functor
open import Categories.NaturalTransformation
open import Categories.Monad
open import Categories.Category.Instance.Sets using (Sets)
-}

--open import Algebra.Lattice.Morphism.Structures using (IsLatticeHomomorphism)
open import Relation.Binary.Morphism.Structures using (IsRelHomomorphism)

-- 定义德摩根代数之间的态射
record DeMorganHom {c₁ ℓ₁ c₂ ℓ₂} (A : DeMorganAlgebra c₁ ℓ₁) (B : DeMorganAlgebra c₂ ℓ₂) : Set (c₁ ⊔ ℓ₁ ⊔ c₂ ⊔ ℓ₂) where
  open DeMorganAlgebra A using () renaming (Carrier to ∣A∣; _≈_ to _≈A_; _∨_ to _∨A_; _∧_ to _∧A_; ¬_ to ¬A; ⊤ to ⊤A; ⊥ to ⊥A)
  open DeMorganAlgebra B using () renaming (Carrier to ∣B∣; _≈_ to _≈B_; _∨_ to _∨B_; _∧_ to _∧B_; ¬_ to ¬B; ⊤ to ⊤B; ⊥ to ⊥B)

  field
    

    ⟦_⟧ : ∣A∣ → ∣B∣                                   -- 载体集合之间的映射
    isRelHomomorphism : IsRelHomomorphism _≈A_ _≈B_ ⟦_⟧
    pres-∨ : ∀ x y → ⟦ (x ∨A y) ⟧ ≈B ⟦ x ⟧ ∨B ⟦ y ⟧ -- 保持∨运算
    pres-∧ : ∀ x y → ⟦ (x ∧A y) ⟧ ≈B ⟦ x ⟧ ∧B ⟦ y ⟧ -- 保持∧运算
    pres-¬ : ∀ x → ⟦ (¬A x) ⟧ ≈B ¬B (⟦ x ⟧)         -- 保持¬运算
    pres-⊤ : ⟦ ⊤A ⟧ ≈B ⊤B                           -- 保持顶元素
    pres-⊥ : ⟦ ⊥A ⟧ ≈B ⊥B                           -- 保持底元素


-- DeMorgan 代数同态的复合
∘-DeMorganHom : ∀ {c₁ ℓ₁ c₂ ℓ₂ c₃ ℓ₃}
             {L₁ : DeMorganAlgebra c₁ ℓ₁} {L₂ : DeMorganAlgebra c₂ ℓ₂} {L₃ : DeMorganAlgebra c₃ ℓ₃}
             → DeMorganHom L₂ L₃ → DeMorganHom L₁ L₂ → DeMorganHom L₁ L₃
∘-DeMorganHom {L₁ = L₁} {L₂} {L₃} g f = record
  { ⟦_⟧ = g.⟦_⟧ ∘ f.⟦_⟧
  ; isRelHomomorphism = record { cong = λ x → IsRelHomomorphism.cong g.isRelHomomorphism
                                               (IsRelHomomorphism.cong f.isRelHomomorphism x) }
  ; pres-∨ = λ x y → L₃.trans
                      (IsRelHomomorphism.cong g.isRelHomomorphism (f.pres-∨ x y))
                      (g.pres-∨ f.⟦ x ⟧ f.⟦ y ⟧)
  ; pres-∧ = λ x y →
                L₃.trans
                (IsRelHomomorphism.cong g.isRelHomomorphism (f.pres-∧ x y))
                (g.pres-∧ f.⟦ x ⟧ f.⟦ y ⟧)
  ; pres-¬ = λ x →
                L₃.trans (IsRelHomomorphism.cong g.isRelHomomorphism (f.pres-¬ x))
                (g.pres-¬ f.⟦ x ⟧)
  ; pres-⊤ = L₃.trans (IsRelHomomorphism.cong g.isRelHomomorphism f.pres-⊤)
              g.pres-⊤
  ; pres-⊥ = L₃.trans (IsRelHomomorphism.cong g.isRelHomomorphism f.pres-⊥)
              g.pres-⊥
  }
  where
    module L₁ = DeMorganAlgebra L₁
    module L₂ = DeMorganAlgebra L₂
    module L₃ = DeMorganAlgebra L₃
    module f = DeMorganHom f
    module g = DeMorganHom g

-- 恒等 DeMorgan Algebra 同态
id-DeMorganHom : ∀ {c ℓ} {L : DeMorganAlgebra c ℓ} → DeMorganHom L L
id-DeMorganHom {L = L} = let module L = DeMorganAlgebra L in
  record
                  { ⟦_⟧ = id
                  ; isRelHomomorphism = record { cong = λ {x} {y} z → z }
                  ; pres-∨ = λ x y → L.refl
                  ; pres-∧ = λ x y → L.refl
                  ; pres-¬ = λ x → L.refl
                  ; pres-⊤ = L.refl
                  ; pres-⊥ = L.refl
                  }


-- 定义德摩根代数范畴
DeMorganCategory : ∀ c ℓ → Category _ _ _
DeMorganCategory c ℓ = record
             { Obj = DeMorganAlgebra c ℓ
             ; _⇒_ = DeMorganHom
             ; _≈_ = λ {A} {B} f g → ∀ x → B .DeMorganAlgebra._≈_ (DeMorganHom.⟦ f ⟧ x)  (DeMorganHom.⟦ g ⟧ x)
             ; id = id-DeMorganHom
             ; _∘_ = ∘-DeMorganHom
             ; assoc = λ {A} {B} {C} {D} {f} {g} {h} x → let module D = DeMorganAlgebra D in D.refl
             ; sym-assoc = λ {A} {B} {C} {D} {f} {g} {h} x → let module D = DeMorganAlgebra D in D.refl
             ; identityˡ = λ {A} {B} {f} x → let module B = DeMorganAlgebra B in B.refl
             ; identityʳ = λ {A} {B} {f} x → let module B = DeMorganAlgebra B in B.refl
             ; identity² = λ {A} x → let module A = DeMorganAlgebra A in A.refl
             ; equiv = λ {A} {B} → let module B = DeMorganAlgebra B in
                     record
                       { refl = λ x → B.refl
                       ; sym = λ x x₁ → B.sym (x x₁)
                       ; trans = λ {i} {j} {k} z z₁ x → B.trans (z x) (z₁ x)
                       }
  ; ∘-resp-≈ = λ {A} {B} {C} {f} {g} {h} {i} x x₁ x₂ → let module C = DeMorganAlgebra C
                                                           module f = DeMorganHom f in
             C.trans
             (IsRelHomomorphism.cong f.isRelHomomorphism (x₁ x₂))
             (x (DeMorganHom.⟦ i ⟧ x₂))

             }
