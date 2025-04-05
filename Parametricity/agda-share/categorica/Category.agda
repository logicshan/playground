{-# OPTIONS --universe-polymorphism #-}

-- Formalization of category theory.
-- --type-in-type is used to crush everything into Set,
-- so we don't have to rewrite everything for all SetN
module Category where

open import Basics

open import Equality

open import Arithmetic

record Category {i j} : Set (suc (i ⊔ j)) where
  infixr 20 _⇒_
  infixl 85 _∘_

  field
    Obj : Set i
    _⇒_ : Obj → Obj → Set j

    id  : ∀{A} → A ⇒ A
    _∘_ : ∀{A B C} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C)

    ident₁ : ∀{A B : Obj} {f : A ⇒ B} → id ∘ f ≡ f
    ident₂ : ∀{A B : Obj} {g : A ⇒ B} → g ∘ id ≡ g
    assoc  : ∀{A B C D : Obj}
              {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D}
             → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f

module Cat {i j} (C : Category {i} {j}) where
  open Category C public

  -- forward composition
  infixr 25 _⟫_
  _⟫_ : ∀{A B C} → (A ⇒ B) → (B ⇒ C) → (A ⇒ C)
  f ⟫ g = g ∘ f

  Commutes : {A B C : Obj} → (A ⇒ B) → (B ⇒ C) → (A ⇒ C) → Set j
  Commutes f g h = g ∘ f ≡ h

  Monic : ∀{B C} → (B ⇒ C) → Set (i ⊔ j)
  Monic {B} f = ∀{A} (g h : A ⇒ B) → f ∘ g ≡ f ∘ h → g ≡ h

  Epic  : ∀{A B} → (A ⇒ B) → Set (i ⊔ j)
  Epic {B = B} f = ∀{C} (g h : B ⇒ C) → g ∘ f ≡ h ∘ f → g ≡ h

  record Retract (X A : Obj) : Set (i ⊔ j) where
    field
      section    : A ⇒ X
      retraction : X ⇒ A

      inverse : retraction ∘ section ≡ id

    epi  : Epic retraction
    epi {C} g h g∘r≡h∘r =
      begin
        g
      ≡⟨ symm ident₂ ⟩
        g ∘ id
      ≡⟨ cong (_∘_ g) (symm inverse) ⟩
        g ∘ (retraction ∘ section)
      ≡⟨ assoc ⟩
        (g ∘ retraction) ∘ section
      ≡⟨ cong (λ f → f ∘ section) g∘r≡h∘r ⟩
        (h ∘ retraction) ∘ section
      ≡⟨ symm assoc ⟩
        h ∘ (retraction ∘ section)
      ≡⟨ cong (_∘_ h) inverse ⟩
        h ∘ id
      ≡⟨ ident₂ ⟩
        h
      ∎
     where open Reasoning (A ⇒ C)

    mono : Monic section
    mono {C} g h s∘g≡s∘h =
      begin
        g
      ≡⟨ symm ident₁ ⟩
        id ∘ g
      ≡⟨ cong (λ f → f ∘ g) (symm inverse) ⟩
        (retraction ∘ section) ∘ g
      ≡⟨ symm assoc ⟩
        retraction ∘ (section ∘ g)
      ≡⟨ cong (_∘_ retraction) s∘g≡s∘h ⟩
        retraction ∘ (section ∘ h)
      ≡⟨ assoc ⟩
        (retraction ∘ section) ∘ h
      ≡⟨ cong (λ f → f ∘ h) inverse ⟩
        id ∘ h
      ≡⟨ ident₁ ⟩
        h
      ∎
     where open Reasoning (C ⇒ A)

  record _≅_ (A B : Obj) : Set (i ⊔ j) where
    field
      iso⇒ : A ⇒ B
      iso⇐ : B ⇒ A

      inverse⇐ : iso⇒ ∘ iso⇐ ≡ id
      inverse⇒ : iso⇐ ∘ iso⇒ ≡ id

    retract⇐ : Retract A B
    retract⇐ = record { section    = iso⇐
                      ; retraction = iso⇒
                      ; inverse    = inverse⇐
                      }

    retract⇒ : Retract B A
    retract⇒ = record { section    = iso⇒
                      ; retraction = iso⇐
                      ; inverse    = inverse⇒
                      }

    open Retract retract⇐ public using ()
      renaming (epi to epic-iso⇒ ; mono to monic-iso⇐)

    open Retract retract⇒ public using ()
      renaming (epi to epic-iso⇐ ; mono to monic-iso⇒)

{-
  Slice : (X : Obj) → Category
  Slice X = record { Obj    = O
                   ; _⇒_    = _S⇒_

                   ; id     = Sid
                   ; _∘_    = _S∘_

                   ; ident₁ = {!!}
                   ; ident₂ = {!!}
                   ; assoc  = {!!}
                   }
   where
   O                  = Σ Obj λ A → A ⇒ X
   _S⇒_ : O → O → Set
   (A , f) S⇒ (B , g) = Σ (A ⇒ B) λ h → Commutes h g f
   Sid : {A : O} → A S⇒ A
   Sid {B , f} = (id , ident₂)

   _S∘_ : ∀{A B C} → (B S⇒ C) → (A S⇒ B) → (A S⇒ C)
   _S∘_ {A₁ , f₁} {A₂ , f₂} {A₃ , f₃} (h₂ , c₂) (h₁ , c₁)
     = (h₂ ∘ h₁ , lemma)
    where
    lemma : Commutes (h₂ ∘ h₁) f₃ f₁
    lemma = begin
              f₃ ∘ (h₂ ∘ h₁)
            ≡⟨ assoc ⟩
              (f₃ ∘ h₂) ∘ h₁
            ≡⟨ cong (λ f → f ∘ h₁) c₂ ⟩
              f₂ ∘ h₁
            ≡⟨ c₁ ⟩
              f₁
            ∎
     where open Reasoning (A₁ ⇒ X)
-}


Finite : Natural.ℕ → Category
Finite n = record { Obj = Finite.Fin n
                  ; _⇒_ = Finite._≤_

                  ; id  = Finite.≤-refl
                  ; _∘_ = λ g f → Finite.≤-trans f g

                  ; ident₁ = Finite.≤-unique _ _
                  ; ident₂ = Finite.≤-unique _ _
                  ; assoc  = Finite.≤-unique _ _
                  }

Zero : Category
Zero = Finite 0

One : Category
One = Finite 1

_op : ∀{i j} → Category {i} {j} → Category {i} {j}
C op = record { Obj    = Cat.Obj C
              ; _⇒_    = λ A B → Cat._⇒_ C B A

              ; id     = Cat.id C
              ; _∘_    = λ g f → Cat._∘_ C f g

              ; ident₁ = Cat.ident₂ C
              ; ident₂ = Cat.ident₁ C
              ; assoc  = symm (Cat.assoc C)
              }

