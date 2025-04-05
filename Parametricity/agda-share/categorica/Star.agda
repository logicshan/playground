{-# OPTIONS --universe-polymorphism #-}

-- Agda's Set is a category!

module Star where

open import Equality

open import Category
-- open import Category.Product
-- open import Category.Coproduct

Star : Category
Star = record { Obj = Set
              ; _⇒_ = λ A B → A → B

              ; id  = λ x → x
              ; _∘_ = λ g f x → g (f x)

              ; ident₁ = refl
              ; ident₂ = refl
              ; assoc  = refl
              }

{-
module Prod where
  open Cat Star

  record _×_ (A B : Set) : Set where
    field
      fst : A
      snd : B

  open _×_ public

  _*_ : ∀{A B Z} → (Z → A) → (Z → B) → Z → A × B
  (f * g) x = record { fst = f x ; snd = g x }

  u : ∀{A B Z} (f : Z → A) (g : Z → B) (i : Z → A × B)
      → Commutes i fst f → Commutes i snd g
      → (f * g) ≡ i
  u .(λ x → fst (i x)) .(λ x → snd (i x)) i refl refl = ext u-lemma
   where
   u-lemma : ∀ x → (fst ∘ i * snd ∘ i) x ≡ i x
   u-lemma x = refl

  ×-is-product : ∀{A B} → (Star Product) A B
  ×-is-product {A} {B} = record { A×B = A × B
                                ; π₁  = fst
                                ; π₂  = snd
                                ; ⟨_,_⟩ = _*_
                                ; universal = u
                                ; commute₁ = λ f → refl
                                ; commute₂ = λ f → refl
                                }

×-Star : Star Has-Products
×-Star = record { has-product = Prod.×-is-product }
-}

{-
module Sum where
  open Cat Star

  data _⊎_ (A B : Set) : Set where
    inl : A → A ⊎ B
    inr : B → A ⊎ B

  _||_ : ∀{A B C} → (A → C) → (B → C) → A ⊎ B → C
  (f || _) (inl x) = f x
  (_ || g) (inr y) = g y

  u : ∀{A B C} (f : A → C) (g : B → C) (o : A ⊎ B → C)
      → o ∘ inl ≡ f → o ∘ inr ≡ g
      → (f || g) ≡ o
  u .(λ x → o (inl x)) .(λ x → o (inr x)) o refl refl = ext lemma
   where
   lemma : ∀ s → (o ∘ inl || o ∘ inr) s ≡ o s
   lemma (inl x) = refl
   lemma (inr y) = refl

+-Star : Star Coproduct
+-Star = record { _+_   = Sum._⊎_

                ; ι₁    = Sum.inl
                ; ι₂    = Sum.inr
                ; [_,_] = Sum._||_

                ; universal = Sum.u
                ; commute₁  = λ f → refl
                ; commute₂  = λ g → refl
                }
-}

{-
module Top where
  record ⊤ : Set where

!-Star : Star Terminal
!-Star = record { ⊤ = Top.⊤
                ; ! = λ _ → _
                ; universal = λ f → ext (λ _ → refl)
                }

module Bottom where
  data ⊥ : Set where

¡-Star : Star Initial
¡-Star = record { ⊥ = Bottom.⊥
                ; ¡ = λ ()
                ; universal = λ f → ext (λ ())
                }
-}


