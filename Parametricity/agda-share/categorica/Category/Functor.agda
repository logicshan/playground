{-# OPTIONS --universe-polymorphism #-}

module Category.Functor where

open import Basics

open import Category

open import Equality

record Functor {i j k l}
               (C : Category {i} {j}) (D : Category {k} {l})
             : Set ((i ⊔ j ⊔ k ⊔ l)) where
  open Cat C renaming ( Obj to C-Obj
                      ; _⇒_ to _C-⇒_
                      ; id  to C-id
                      ; _∘_ to _C-∘_
                      )

  open Cat D renaming ( Obj to D-Obj
                      ; _⇒_ to _D-⇒_
                      ; id  to D-id
                      ; _∘_ to _D-∘_
                      )

  field
    O-map  : C-Obj → D-Obj
    map    : ∀{A B} → (A C-⇒ B) → (O-map A D-⇒ O-map B)

    map-id : ∀{A} → map (C-id {A}) ≡ D-id
    map-∘  : ∀{A B C} {f : A C-⇒ B} {g : B C-⇒ C}
           → map (g C-∘ f) ≡ map g D-∘ map f

{-
_Endofunctor : Category → Set
C Endofunctor = Functor C C

I : ∀{C} → C Endofunctor
I = record { O-map = λ A → A
           ; map   = λ f → f

           ; map-id = refl
           ; map-∘  = refl
           }

_○_ : ∀{C D E} → Functor D E → Functor C D → Functor C E
G ○ F = record { O-map  = λ A → O-map G (O-map F A)
               ; map    = λ f → map G (map F f)

               ; map-id = trans (cong (map G) (map-id F)) (map-id G)
               ; map-∘  = trans (cong (map G) (map-∘ F)) (map-∘ G)
               }
 where
 open Functor

Cats : Category
Cats = record { Obj = Category
              ; _⇒_ = Functor

              ; id  = I
              ; _∘_ = _○_

              ; ident₁ = {!!}
              ; ident₂ = {!!}
              ; assoc  = {!!}
              }
-}
