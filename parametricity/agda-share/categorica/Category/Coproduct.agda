{-# OPTIONS --type-in-type #-}

module Category.Coproduct where

open import Equality

open import Category

record _Coproduct (C : Category) : Set where
  open Cat C

  infixr 60 _+_
  field
    _+_   : Obj → Obj → Obj

    ι₁    : ∀{A B}   → A ⇒ A + B
    ι₂    : ∀{A B}   → B ⇒ A + B
    [_,_] : ∀{A B C} → (A ⇒ C) → (B ⇒ C) → (A + B ⇒ C)

    commute₁  : ∀{A B C} (f : A ⇒ C) {g : B ⇒ C} → Commutes ι₁ [ f , g ] f
    commute₂  : ∀{A B C} {f : A ⇒ C} (g : B ⇒ C) → Commutes ι₂ [ f , g ] g
    universal : ∀{A B C} (f : A ⇒ C) (g : B ⇒ C) (o : A + B ⇒ C)
                → Commutes ι₁ o f → Commutes ι₂ o g
                → [ f , g ] ≡ o

  _-+-_ : ∀{A B C D} → (A ⇒ C) → (B ⇒ D) → (A + B ⇒ C + D)
  f -+- g = [ ι₁ ∘ f , ι₂ ∘ g ]

  [ι₁,ι₂] : ∀{A B C} (o : A + B ⇒ C) → [ o ∘ ι₁ , o ∘ ι₂ ] ≡ o
  [ι₁,ι₂] o = universal (o ∘ ι₁) (o ∘ ι₂) o refl refl

record _Initial (C : Category) : Set where
  open Cat C

  field
    ⊥ : Obj

    ¡ : ∀{A} → ⊥ ⇒ A

    universal : ∀{A} → (f : ⊥ ⇒ A) → ¡ ≡ f
