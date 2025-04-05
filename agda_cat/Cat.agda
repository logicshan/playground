{-# OPTIONS --type-in-type #-}

open import Relation.Binary.PropositionalEquality

record Category : Set where
  eta-equality

  field
    Obj : Set
    Hom : Obj -> Obj -> Set

  field
    id  : ∀ {A} → Hom A A
    comp : ∀ {A B C} → Hom A B → Hom B C → Hom A C

  field -- laws
    assoc     : ∀ {A B C D} {f : Hom A B} {g : Hom B C}{h : Hom C D} →
                comp f (comp g h) ≡ (comp (comp f g) h)
    identityˡ : ∀ {A B} {f : Hom A B} → comp id f ≡ f
    identityʳ : ∀ {A B} {f : Hom A B} → comp f id ≡ f
open Category

---------------------------------------------------------------------------
-- A toy category
---------------------------------------------------------------------------

module Toy where

  -- We can make our own small categories, like on a whiteboard. (We
  -- do this in a module so that we don't pollute the namespace with
  -- A, B, C, f, g, h etc.)

  data MyObj : Set where
    A B C : MyObj

  data MyHom : MyObj → MyObj → Set where
    idA : MyHom A A
    idB : MyHom B B
    idC : MyHom C C
    f : MyHom A B
    g : MyHom B C
    h : MyHom A C

  myComp : {A B C : MyObj} → MyHom A B → MyHom B C → MyHom A C
  myComp idA t = t
  myComp idB t = t
  myComp idC t = t
  myComp f idB = f
  myComp f g = h
  myComp g idC = g
  myComp h idC = h

  MyCat : Category
  MyCat .Obj = MyObj
  MyCat .Hom = MyHom
  MyCat .id {A} = idA
  MyCat .id {B} = idB
  MyCat .id {C} = idC
  MyCat .comp = myComp
  MyCat .assoc {f = idA} {t} {u} = refl
  MyCat .assoc {f = idB} {t} {u} = refl
  MyCat .assoc {f = idC} {t} {u} = refl
  MyCat .assoc {f = f} {idB} {u} = refl
  MyCat .assoc {f = f} {g} {idC} = refl
  MyCat .assoc {f = g} {idC} {idC} = refl
  MyCat .assoc {f = h} {idC} {idC} = refl
  MyCat .identityˡ {f = idA} = refl
  MyCat .identityˡ {f = idB} = refl
  MyCat .identityˡ {f = idC} = refl
  MyCat .identityˡ {f = f} = refl
  MyCat .identityˡ {f = g} = refl
  MyCat .identityˡ {f = h} = refl
  MyCat .identityʳ {f = idA} = refl
  MyCat .identityʳ {f = idB} = refl
  MyCat .identityʳ {f = idC} = refl
  MyCat .identityʳ {f = f} = refl
  MyCat .identityʳ {f = g} = refl
  MyCat .identityʳ {f = h} = refl
