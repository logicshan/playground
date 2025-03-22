{-# OPTIONS --universe-polymorphism #-}
module Yoneda where
open import Level
open import Setoids
open import Category
open import Functor
open import NaturalTransformation

{- isomorphisms for Yoneda lemma -}
Φ : {a b c : Level} {C : Cat a b c} {x y : ob C} →
  [ C op , SETOID b c ] 〈 C 〈-, x 〉 , C 〈-, y 〉 〉 → C 〈 x , y 〉
Φ {a} {b} {c} {C} {x} {y} δ = Fun∼.function (δ ↓ x) (id C x)
Ψ : {a b c : Level} {C : Cat a b c} {x y : ob C} →
  C 〈 x , y 〉 → [ C op , SETOID b c ] 〈 C 〈-, x 〉 , C 〈-, y 〉 〉
Ψ {a} {b} {c} {C} {x} {y} f =
  record { object = λ (u : ob C) →
             record { function = λ (h : C 〈 u , x 〉) → C ! f ∘ h
                    ; respects∼ = λ {h k : C 〈 u , x 〉} (h∼k : C ! h ∼ k) →
                        Cat.comp∼ C (Setoid.refl∼ (C ⟪ x , y ⟫)) h∼k
                    }
         ; naturality =
             λ {u v : ob C} (g : (C op) 〈 u , v 〉) (h : (C op) 〈 x , u 〉) →
             Cat.associativity∼ C f h g
         }

{- Yoneda lemma -}
Lemma1 : {a b c : Level} {C : Cat a b c} {x y : ob C} →
  (δ : [ C op , SETOID b c ] 〈 C 〈-, x 〉 , C 〈-, y 〉 〉) →
  [ C op , SETOID b c ] ! δ ∼ (Ψ (Φ δ))
Lemma1 {C = C} {x = x} {y = y} δ =
  λ (u : ob C) (h : C 〈 u , x 〉) →
  let open Setoid (C ⟪ u , y ⟫) in
  sym∼ (trans∼ (Fun∼.respects∼ (δ ↓ u) (Cat.left-identity∼ C h))
                (_≐>_.naturality δ h (id C x)))
Lemma2 : {a b c : Level} {C : Cat a b c} {x y : ob C} →
  (f : C 〈 x , y 〉) → C ! f ∼ (Φ (Ψ {C = C} f))
Lemma2 {a} {b} {c} {C} {x} {y} f =
  let open Setoid (C ⟪ x , y ⟫) in sym∼ (Cat.right-identity∼ C f)

{- Yoneda embedding -}
¥ : ∀ {a b c} → (C : Cat a b c) → C => ([ C op , SETOID b c ])
¥ C = record { object = λ (X : ob C) → C 〈-, X 〉
             ; hom = λ {X Y} (f : C 〈 X , Y 〉) → C 〈-,, f 〉
             ; hom∼ = λ {X Y : ob C} (f g : C 〈 X , Y 〉) f∼g →
               (λ (U : ob C) (_ : C 〈 U , X 〉) →
                    C !! f∼g ∘ let open Setoid (C ⟪ U , X ⟫) in refl∼)
             ; identity∼ = λ {X : ob C} →
               (λ (U : ob C) (f : C 〈 U , X 〉) → Cat.left-identity∼ C f)
             ; comp∼ = λ {X Y Z : ob C} (f : C 〈 Y , Z 〉) (g : C 〈 X , Y 〉) →
               (λ (U : ob C) (h : C 〈 U , X 〉) → Cat.associativity∼ C f g h)
             }
