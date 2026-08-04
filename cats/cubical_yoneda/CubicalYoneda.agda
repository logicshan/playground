{-# OPTIONS --cubical --guardedness #-}

module CubicalYoneda where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

-- ==========================================
-- 1. 范畴 (Category)
-- ==========================================
record Category (o h : Level) : Type (ℓ-suc (ℓ-max o h)) where
  field
    ob : Type o
    Hom : ob → ob → Type h
    id : ∀ {x} → Hom x x
    _⋆_ : ∀ {x y z} → Hom x y → Hom y z → Hom x z
    
    ⋆IdL : ∀ {x y} (f : Hom x y) → id ⋆ f ≡ f
    ⋆IdR : ∀ {x y} (f : Hom x y) → f ⋆ id ≡ f
    ⋆Assoc : ∀ {x y z w} (f : Hom x y) (g : Hom y z) (h : Hom z w) 
           → (f ⋆ g) ⋆ h ≡ f ⋆ (g ⋆ h)
    
    isSetHom : ∀ {x y} → isSet (Hom x y)

-- ==========================================
-- 2. 函子 (Functor)
-- ==========================================
record Functor {o h o' h' : Level} (C : Category o h) (D : Category o' h') 
               : Type (ℓ-max (ℓ-max o h) (ℓ-max o' h')) where
  private
    module C = Category C
    module D = Category D
  field
    F-ob : C.ob → D.ob
    F-hom : ∀ {x y} → C.Hom x y → D.Hom (F-ob x) (F-ob y)
    
    F-id : ∀ {x} → F-hom (C.id {x}) ≡ D.id {F-ob x}
    F-seq : ∀ {x y z} (f : C.Hom x y) (g : C.Hom y z) 
          → F-hom (C._⋆_ f g) ≡ D._⋆_ (F-hom f) (F-hom g)

-- ==========================================
-- 3. 自然变换 (Natural Transformation)
-- ==========================================
record NatTrans {o h o' h' : Level} {C : Category o h} {D : Category o' h'} 
                (F G : Functor C D) : Type (ℓ-max (ℓ-max o h) (ℓ-max o' h')) where
  private
    module C = Category C
    module D = Category D
    module F = Functor F
    module G = Functor G
  field
    N-ob : ∀ x → D.Hom (F.F-ob x) (G.F-ob x)
    N-hom : ∀ {x y} (f : C.Hom x y) 
          → D._⋆_ (F.F-hom f) (N-ob y) ≡ D._⋆_ (N-ob x) (G.F-hom f)

-- ==========================================
-- 4. SET 范畴与 Hom 函子
-- ==========================================

SET : (ℓ : Level) → Category (ℓ-suc ℓ) ℓ
Category.ob (SET ℓ) = Σ (Type ℓ) isSet
Category.Hom (SET ℓ) A B = fst A → fst B
Category.id (SET ℓ) = λ x → x
Category._⋆_ (SET ℓ) f g = λ x → g (f x)
Category.⋆IdL (SET ℓ) f = refl
Category.⋆IdR (SET ℓ) f = refl
Category.⋆Assoc (SET ℓ) f g h = refl
Category.isSetHom (SET ℓ) {A} {B} = isSetΠ (λ _ → snd B)

HomFunctor : ∀ {o h} (C : Category o h) (c : Category.ob C) → Functor C (SET h)
Functor.F-ob (HomFunctor C c) x = Category.Hom C c x , Category.isSetHom C
Functor.F-hom (HomFunctor C c) f = λ g → Category._⋆_ C g f
Functor.F-id (HomFunctor C c) = funExt (Category.⋆IdR C)
Functor.F-seq (HomFunctor C c) f g = funExt (λ h → sym (Category.⋆Assoc C h f g))

-- ==========================================
-- 5. Yoneda Lemma 证明
-- ==========================================

yoneda-fwd : ∀ {o h} {C : Category o h} {c : Category.ob C} 
             (F : Functor C (SET h)) 
           → NatTrans (HomFunctor C c) F → fst (Functor.F-ob F c)
yoneda-fwd {C = C} {c = c} F α = NatTrans.N-ob α c (Category.id C)

yoneda-bwd : ∀ {o h} {C : Category o h} {c : Category.ob C} 
             (F : Functor C (SET h)) 
           → fst (Functor.F-ob F c) → NatTrans (HomFunctor C c) F
NatTrans.N-ob (yoneda-bwd {C = C} F x) y f = Functor.F-hom F f x
NatTrans.N-hom (yoneda-bwd {C = C} {c = c} F x) {y} {z} f = 
  funExt (λ g → funExt⁻ (Functor.F-seq F g f) x)

yoneda-id1 : ∀ {o h} {C : Category o h} {c : Category.ob C} 
             (F : Functor C (SET h)) (x : fst (Functor.F-ob F c))
           → yoneda-fwd F (yoneda-bwd F x) ≡ x
yoneda-id1 F x = funExt⁻ (Functor.F-id F) x

yoneda-id2-pointwise : ∀ {o h} {C : Category o h} {c : Category.ob C} 
                       (F : Functor C (SET h)) (α : NatTrans (HomFunctor C c) F)
                       (y : Category.ob C) (f : Category.Hom C c y)
                     → NatTrans.N-ob (yoneda-bwd F (yoneda-fwd F α)) y f ≡ NatTrans.N-ob α y f
yoneda-id2-pointwise {C = C} {c = c} F α y f =
  let 
    id = Category.id C
    α-nat = funExt⁻ (NatTrans.N-hom α f) id 
    id-lem = cong (NatTrans.N-ob α y) (Category.⋆IdL C f)
  in 
    sym α-nat ∙ id-lem
