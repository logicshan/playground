{-# OPTIONS --universe-polymorphism #-}
module Functor where
open import Level
open import Setoids
open import Category

{- functors -}
record _=>_ {a b c a' b' c'}
  (C : Cat a b c) (D : Cat a' b' c') : Set (a ⊔ a' ⊔ b ⊔ b' ⊔ c ⊔ c') where
  field
    object : ob C  → ob D 
    hom : {X Y : ob C} →
      C 〈 X , Y 〉 → D 〈 object X , object Y 〉
    hom∼ : {X Y : ob C} → (f g : C 〈 X , Y 〉) →
      (f∼g : C ! f ∼ g) → D ! hom f ∼ hom g
    identity∼ : {X : ob C} →
      D ! hom (id C X) ∼ id D (object X)
    comp∼ : {X Y Z : ob C} → (f : C 〈 Y , Z 〉) → (g : C 〈 X , Y 〉) →
      D ! hom (C ! f ∘ g) ∼ (D ! hom f ∘ hom g)


_`_ : ∀ {a b c a' b' c'} {X : Cat a b c} → {Y : Cat a' b' c'} →
  X => Y → ob X → ob Y
F ` x = _=>_.object F x

_``_ : ∀ {a b c a' b' c'} {X : Cat a b c} → {Y : Cat a' b' c'} →
  {x0 x1 : ob X} → (F : X => Y) → X 〈 x0 , x1 〉 → Y 〈 F ` x0 , F ` x1 〉
F `` f = _=>_.hom F f

{- contravariant hom functor -}
_〈-,_〉 : ∀ {a b c} → (C : Cat a b c) → (X : ob C) → (C op) => SETOID b c
C 〈-, X 〉 =
  record { object = λ U → C ⟪ U , X ⟫
         ; hom = λ {U V} (h : C 〈 V , U 〉) →
           record { function  = λ (f : C 〈 U , X 〉) → C ! f ∘ h
                  ; respects∼ = λ x0∼x1 →
                    C !! x0∼x1 ∘ (Setoid.refl∼ (C ⟪ V , U ⟫))
                  }
         ; hom∼ = λ {Z} f g f∼g x →
           C !! (Setoid.refl∼ (C ⟪ Z , X ⟫)) ∘ f∼g
         ; identity∼ = Cat.left-identity∼ (C op)
         ; comp∼ = λ {_ _ Z} f g h →
           Setoid.sym∼ (C ⟪ Z , X ⟫) (Cat.associativity∼ C h g f)
         }
