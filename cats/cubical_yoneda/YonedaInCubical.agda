{-# OPTIONS --cubical --guardedness #-}

module YonedaInCubical where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

private
  variable
    ℓ ℓob ℓhom ℓCob ℓChom ℓDob ℓDhom : Level

-- ============================================================================
-- 1. 范畴 (Category) 定义
-- ============================================================================
record Category (ℓob ℓhom : Level) : Type (ℓ-suc (ℓ-max ℓob ℓhom)) where
  field
    Ob       : Type ℓob
    Hom      : Ob → Ob → Type ℓhom
    isSetHom : ∀ {x y} → isSet (Hom x y)
    id       : ∀ {x} → Hom x x
    _∘_      : ∀ {x y z} → Hom y z → Hom x y → Hom x z
    idL      : ∀ {x y} (f : Hom x y) → id ∘ f ≡ f
    idR      : ∀ {x y} (f : Hom x y) → f ∘ id ≡ f
    assoc    : ∀ {x y z w} (f : Hom x y) (g : Hom y z) (h : Hom z w)
             → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)

-- ============================================================================
-- 2. 函子 (Functor) 定义
-- ============================================================================
record Functor (C : Category ℓCob ℓChom) (D : Category ℓDob ℓDhom) 
               : Type (ℓ-max (ℓ-max ℓCob ℓChom) (ℓ-max ℓDob ℓDhom)) where
  private
    module C = Category C
    module D = Category D
  field
    F-ob  : C.Ob → D.Ob
    F-hom : ∀ {x y} → C.Hom x y → D.Hom (F-ob x) (F-ob y)
    F-id  : ∀ {x} → F-hom (C.id {x}) ≡ D.id {F-ob x}
    F-seq : ∀ {x y z} (f : C.Hom x y) (g : C.Hom y z)
          → F-hom (g C.∘ f) ≡ (F-hom g) D.∘ (F-hom f)

-- ============================================================================
-- 3. 自然变换 (Natural Transformation) 定义
-- ============================================================================
record NatTrans {C : Category ℓCob ℓChom} {D : Category ℓDob ℓDhom}
                (F G : Functor C D) : Type (ℓ-max (ℓ-max ℓCob ℓChom) (ℓ-max ℓDob ℓDhom)) where
  private
    module C = Category C
    module D = Category D
    module F = Functor F
    module G = Functor G
  field
    N-ob  : ∀ (x : C.Ob) → D.Hom (F.F-ob x) (G.F-ob x)
    N-hom : ∀ {x y : C.Ob} (f : C.Hom x y)
          → (N-ob y) D.∘ (F.F-hom f) ≡ (G.F-hom f) D.∘ (N-ob x)

-- ============================================================================
-- 4. 集合范畴 (SET Category)
-- ============================================================================
SET : (ℓ : Level) → Category (ℓ-suc ℓ) ℓ
Category.Ob (SET ℓ) = hSet ℓ
Category.Hom (SET ℓ) A B = A .fst → B .fst
Category.isSetHom (SET ℓ) {A} {B} = isSet→ (B .snd)
Category.id (SET ℓ) = λ x → x
Category._∘_ (SET ℓ) g f = λ x → g (f x)
Category.idL (SET ℓ) f = refl
Category.idR (SET ℓ) f = refl
Category.assoc (SET ℓ) f g h = refl

-- ============================================================================
-- 5. Hom 函子 (Hom-functor)
-- ============================================================================
Hom-functor : (C : Category ℓCob ℓChom) (c : Category.Ob C) → Functor C (SET ℓChom)
Functor.F-ob (Hom-functor C c) x = (Category.Hom C c x , Category.isSetHom C)
Functor.F-hom (Hom-functor C c) f g = Category._∘_ C f g
Functor.F-id (Hom-functor C c) {x} = funExt (λ g → Category.idL C g)
Functor.F-seq (Hom-functor C c) f g = funExt (λ h → Category.assoc C h f g)

-- ============================================================================
-- 6. 米田引理 (Yoneda Lemma)
-- ============================================================================
module Yoneda (C : Category ℓCob ℓChom) (c : Category.Ob C) (F : Functor C (SET ℓChom)) where
  open Category C
  open Functor F

  yoneda-map : NatTrans (Hom-functor C c) F → F-ob c .fst
  yoneda-map α = NatTrans.N-ob α c (id {c})

  yoneda-inv : F-ob c .fst → NatTrans (Hom-functor C c) F
  NatTrans.N-ob (yoneda-inv x) d f = F-hom f x
  NatTrans.N-hom (yoneda-inv x) {d} {e} g = funExt (λ f → 
    funExt⁻ (F-seq f g) x)

  yoneda-map-inv : ∀ (x : F-ob c .fst) → yoneda-map (yoneda-inv x) ≡ x
  yoneda-map-inv x = 
    yoneda-map (yoneda-inv x) ≡⟨ refl ⟩
    F-hom id x                ≡⟨ funExt⁻ F-id x ⟩
    x ∎

  NatTrans-≡ : ∀ {F' G' : Functor C (SET ℓChom)} (α β : NatTrans F' G')
             → (∀ x → NatTrans.N-ob α x ≡ NatTrans.N-ob β x)
             → α ≡ β
  NatTrans-≡ {F' = F'} {G' = G'} α β p i .NatTrans.N-ob x = p x i
  NatTrans-≡ {F' = F'} {G' = G'} α β p i .NatTrans.N-hom {x} {y} f =
    isProp→PathP
      (λ i → isSet→ (Functor.F-ob G' y .snd)
               (λ z → p y i (Functor.F-hom F' f z))
               (λ z → Functor.F-hom G' f (p x i z)))
      (NatTrans.N-hom α f)
      (NatTrans.N-hom β f)
      i

  yoneda-inv-map : ∀ (α : NatTrans (Hom-functor C c) F) → yoneda-inv (yoneda-map α) ≡ α
  yoneda-inv-map α = NatTrans-≡ (yoneda-inv (yoneda-map α)) α λ d → funExt λ f →
    let nat-step = funExt⁻ (NatTrans.N-hom α f) id
        idR-step = cong (NatTrans.N-ob α d) (idR f)
    in sym nat-step ∙ idR-step
