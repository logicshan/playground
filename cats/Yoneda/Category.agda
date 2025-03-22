{-# OPTIONS --universe-polymorphism #-}
module Category where
open import Level
open import Function using (_∘_)
open import Setoids

∥_∥ : ∀ {a b c} {X : Set a} → (h : X → X → Setoid b c) → (x y : X) → Set b
∥ h ∥ x y = Setoid.object (h x y)

record Cat (a b c : Level) : Set (suc (a ⊔ b ⊔ c)) where
  field
    object : Set a
    hom : object → object → Setoid b c
    identity : (x : object) → ∥ hom ∥ x x
    comp : {x y z : object} → ∥ hom ∥ y z → ∥ hom ∥ x y → ∥ hom ∥ x z
    comp∼ : {x y z : object} →
             {g0 g1 : ∥ hom ∥ y z} → {f0 f1 : ∥ hom ∥ x y} →
             (g0∼g1 : let open Setoid (hom y z) in g0 ∼ g1) →
             (f0∼f1 : let open Setoid (hom x y) in f0 ∼ f1) →
             let open Setoid (hom x z) in comp g0 f0 ∼ comp g1 f1
    associativity∼ : {w x y z : object} →
      (f : ∥ hom ∥ y z) → (g : ∥ hom ∥ x y) → (h : ∥ hom ∥ w x) →
      let open Setoid (hom w z) in comp (comp f g) h ∼ comp f (comp g h)
    left-identity∼ : {x y : object} → (f : ∥ hom ∥ x y) →
      let open Setoid (hom x y) in comp (identity y) f ∼ f
    right-identity∼ : {x y : object} → (f : ∥ hom ∥ x y) →
      let open Setoid (hom x y) in comp f (identity x) ∼ f

ob : ∀ {a b c} → Cat a b c → Set a
ob C = Cat.object C

_〈_,_〉 : ∀ {a b c} → (C : Cat a b c) → ob C → ob C → Set b
C 〈 X , Y 〉 = ∥ Cat.hom C ∥ X Y
_⟪_,_⟫ : ∀ {a b c} → (C : Cat a b c) → ob C → ob C → Setoid b c
C ⟪ X , Y ⟫ = Cat.hom C X Y

_!_∼_ :
  ∀ {a b c} → (C : Cat a b c) → {X Y : ob C} → C 〈 X , Y 〉 → C 〈 X , Y 〉 → Set c
_!_∼_ C {X} {Y} f g = Setoid._∼_ (Cat.hom C X Y) f g

id : ∀ {a b c} → (C : Cat a b c) → (x : ob C) → C 〈 x , x 〉
id C x = Cat.identity C x

_!_∘_ : ∀ {a b c} → (C : Cat a b c) → {x y z : ob C } →
        C 〈 y , z 〉 → C 〈 x , y 〉 → C 〈 x , z 〉
C ! g ∘ f = Cat.comp C g f
_!!_∘_ : ∀ {a b c} (C : Cat a b c) {x y z : ob C} →
             {g0 g1 : C 〈 y , z 〉} → {f0 f1 : C 〈 x , y 〉} →
             (g0∼g1 : let open Setoid (C ⟪ y , z ⟫) in g0 ∼ g1) →
             (f0∼f1 : let open Setoid (C ⟪ x , y ⟫) in f0 ∼ f1) →
             let open Cat C in let open Setoid (hom x z) in
             comp g0 f0 ∼ comp g1 f1
_!!_∘_ C {g0 = g0} {g1 = g1} {f0 = f0} {f1 = f1} g0∼g1 f0∼f1 =
  Cat.comp∼ C g0∼g1 f0∼f1

-- SETOID a is the category of Setoids of level a b;
-- the homsetoid from X to Y is FunSetoid X Y.
SETOID : (a b : Level) → Cat (suc (a ⊔ b)) (a ⊔ b) (a ⊔ b)
SETOID a b = record
  { object = Setoid a b
  ; hom = λ (X Y : Setoid a b) → FunSetoid X Y
  ; identity = λ X →
      record { function = λ x → x
             ; respects∼ = λ x0∼x1 → x0∼x1
             }
  ; comp = λ G → λ F →
      record { function = let open Fun∼ in function G ∘ function F
             ; respects∼ = let open Fun∼ in respects∼ G ∘ respects∼ F
             }
  ; comp∼ = λ{_ _ Z} {g0 g1} {f0 f1} g0∼g1 f0∼f1 x → 
      let open Setoid Z in let open Fun∼ in
        trans∼ (g0∼g1 (function f1 x)) (respects∼ g0 (f0∼f1 x))
  ; associativity∼ = λ{_ _ _ Z} _ _ _ _ → Setoid.refl∼ Z
  ; left-identity∼ = λ {_ Y} _ _ → Setoid.refl∼ Y
  ; right-identity∼ = λ {_ Y} _ _ → Setoid.refl∼ Y
  }

_op : ∀ {a b c} → Cat a b c → Cat a b c
C op =
  record { object = ob C 
         ; hom = λ x → λ y → C ⟪ y , x ⟫
         ; identity = id C
         ; comp = λ f → λ g → C ! g ∘ f
         ; comp∼ = λ {x y z g0 g1 f0 f1} g0∼g1 f0∼f1 → C !! f0∼f1 ∘ g0∼g1
         ; associativity∼ = λ {w _ _ z} f g h →
             Setoid.sym∼ (C ⟪ z , w ⟫) (Cat.associativity∼ C h g f)
         ; left-identity∼ = Cat.right-identity∼ C
         ; right-identity∼ = Cat.left-identity∼ C
         }
