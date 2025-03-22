{-# OPTIONS --universe-polymorphism #-}
module NaturalTransformation where
open import Level
open import Setoids
open import Category
open import Functor
import SetoidEqReasoning as EQ

{- natural transformations -}
record _≐>_ {a b c a' b' c'} {C : Cat a b c} {D : Cat a' b' c'}
  (F G : C => D) : Set (a ⊔ b ⊔ b' ⊔ c') where
  field
    object : (x : ob C) → D 〈 F ` x , G ` x 〉
    naturality : {x y : ob C} →
                   (f : C 〈 x , y 〉) →
                   D ! D ! G `` f ∘ object x ∼ (D ! object y ∘ (F `` f)) 

{- application of a natural transformation to an object -}
_↓_ : ∀ {a b c a' b' c'} {C : Cat a b c} {D : Cat a' b' c'} {F G : C => D} → 
  F ≐> G → (x : ob C) → D 〈 F ` x , G ` x 〉
α ↓ x = _≐>_.object α x

{- hom natural transformation -}
_〈-,,_〉 : ∀ {a b c} → (C : Cat a b c) → {X Y : ob C} → (f : C 〈 X , Y 〉) → (C 〈-, X 〉) ≐> (C 〈-, Y 〉)
_〈-,,_〉 C {X = X} {Y = Y} f =
  record { object = λ (x : ob C) →
           record { function = λ h → C ! f ∘ h
                  ; respects∼ = λ {x0} {x1} x0∼x1 →
                    C !! (Setoid.refl∼ (C ⟪ X , Y ⟫)) ∘ x0∼x1
                  } 
         ; naturality = λ {V} {U} → λ (p : C 〈 U , V 〉) (q : C 〈 V , X 〉) →
           Cat.associativity∼ C f q p
         }

{- identity natural transformation -}
Id : ∀ {a b c a' b' c'} {C : Cat a b c} {D : Cat a' b' c'} (F : C => D) → F ≐> F
Id {C = C} {D = D} F =
  record { object = λ x → id D (F ` x)
         ; naturality = λ {X} {Y} → λ (f : C 〈 X , Y 〉) →
           let open Setoid (D ⟪ F ` X , F ` Y ⟫) in
           let open Cat D in
           trans∼ (sym∼ (left-identity∼ (F `` f)))
                   (right-identity∼ (F `` f))
         }

eqNT : ∀ {a b c a' b' c'} {C : Cat a b c} {D : Cat a' b' c'} {F G : C => D}
  (α β : F ≐> G) → Set (a {-⊔ b ⊔ c ⊔ a' ⊔ b'-} ⊔ c')
eqNT {a} {b} {c} {a'} {b'} {c'} {C} {D} α β = (x : ob C) → D ! α ↓ x ∼ (β ↓ x)

{- setoid of natural transformations -}
{- this is the hom setoid of functor categories -}
NTSetoid : ∀ {a b c a' b' c'} {C : Cat a b c} {D : Cat a' b' c'} (F G : C => D) →
  Setoid (a ⊔ b ⊔ b' ⊔ c') (a ⊔ c')
NTSetoid {a} {b} {c} {a'} {b'} {c'} {C = C} {D = D} F G =
  record { object = F ≐> G
         ; _∼_ = eqNT
         ; refl∼ = λ X →
           Setoid.refl∼ (D ⟪ F ` X , G ` X ⟫)
         ; sym∼ = λ α∼β → λ X →
           Setoid.sym∼ (D ⟪ F ` X , G ` X ⟫) (α∼β X)
         ; trans∼ = λ β∼γ α∼β → λ X →
           Setoid.trans∼ (D ⟪ F ` X , G ` X ⟫) (β∼γ X) (α∼β X)
         }

{- vertical composition of natural transformations -}
_∙_ : ∀ {a b c a' b' c'} {C : Cat a b c} {D : Cat a' b' c'} {F G H : C => D}
         (β : G ≐> H) (α : F ≐> G) → F ≐> H
_∙_ {C = C} {D = D} {F = F} {G = G} {H = H} β α =
  record { object = λ (x : ob C) → D ! (β ↓ x) ∘ (α ↓ x)
         ; naturality =
           λ {x y : ob C} (f : C 〈 x , y 〉) →
           let open EQ (D ⟪ F ` x , H ` y ⟫) in
           let open Cat D in
           ∵ D ! H `` f ∘ (D ! β ↓ x ∘ (α ↓ x))
           ∼ D ! (D ! H `` f ∘ (β ↓ x)) ∘ (α ↓ x)
             yb associativity∼ (H `` f) (β ↓ x) (α ↓ x)
           ∼ D ! (D ! (β ↓ y) ∘ (G `` f)) ∘ (α ↓ x)
             by comp∼ (_≐>_.naturality β f)
                (let open Setoid (D ⟪ F ` x , G ` x ⟫) in refl∼)
           ∼ D ! (β ↓ y) ∘ (D ! G `` f ∘ (α ↓ x))
             by associativity∼ (β ↓ y) (G `` f) (α ↓ x)
           ∼ D ! (β ↓ y) ∘ (D ! (α ↓ y) ∘ (F `` f))
             by comp∼ (let open Setoid (D ⟪ G ` y , H ` y ⟫) in refl∼)
                (_≐>_.naturality α f)
           ∼ D ! (D ! β ↓ y ∘ (α ↓ y)) ∘ (F `` f)
             yb associativity∼ (β ↓ y) (α ↓ y) (F `` f)
         }

{- functor categories -}
[_,_] : ∀ {a b c a' b' c'} → Cat a b c → Cat a' b' c' → Cat (a ⊔ b ⊔ c ⊔ a' ⊔ b' ⊔ c') (a ⊔ b ⊔ b' ⊔ c') (a ⊔ c')
[ C , D ] =
  let open Cat D in
  record { object = C => D
         ; hom = λ F → λ G → NTSetoid F G
         ; identity = Id
         ; comp = _∙_
         ; comp∼ =
             λ α∼β γ∼δ (x : ob C) → comp∼ (α∼β x) (γ∼δ x)
         ; associativity∼ =
             λ {F : C => D} {G : C => D} {H : C => D} {K : C => D}
             (α : H ≐> K) (β : G ≐> H) (γ : F ≐> G)
             (x : ob C) →
             associativity∼ (α ↓ x) (β ↓ x) (γ ↓ x)
         ; left-identity∼ =
             λ {F : C => D} {G : C => D} (α : F ≐> G) (x : ob C) →
             left-identity∼ (α ↓ x)
         ; right-identity∼ =
             λ {F : C => D} {G : C => D} (α : F ≐> G) (x : ob C) →
             right-identity∼ (α ↓ x)
         }
