{-# OPTIONS --universe-polymorphism #-}

module Category.Product where

open import Basics

open import Arithmetic

open import Equality

open import Category

record _Product {i j} (C : Category {i} {j}) (A B : Cat.Obj C) : Set (i ⊔ j) where
  open Cat C

  field
    A×B   : Obj

    π₁    : A×B ⇒ A
    π₂    : A×B ⇒ B
    ⟨_,_⟩ : ∀{Z} → (Z ⇒ A) → (Z ⇒ B) → (Z ⇒ A×B)

    commute₁  : ∀{Z} (f : Z ⇒ A) {g : Z ⇒ B} → Commutes ⟨ f , g ⟩ π₁ f
    commute₂  : ∀{Z} {f : Z ⇒ A} (g : Z ⇒ B) → Commutes ⟨ f , g ⟩ π₂ g
    universal : ∀{Z} (f : Z ⇒ A) (g : Z ⇒ B) (i : Z ⇒ A×B)
              → Commutes i π₁ f → Commutes i π₂ g
              → ⟨ f , g ⟩ ≡ i

  g-η : ∀{Z} → (i : Z ⇒ A×B) → ⟨ π₁ ∘ i , π₂ ∘ i ⟩ ≡ i
  g-η i = universal (π₁ ∘ i) (π₂ ∘ i) i refl refl

  η : ⟨ π₁ , π₂ ⟩ ≡ id
  η = begin
        ⟨ π₁ , π₂ ⟩
      ≡⟨ cong (λ f → ⟨ f , π₂ ⟩) (symm ident₂) ⟩
        ⟨ π₁ ∘ id , π₂ ⟩
      ≡⟨ cong (λ g → ⟨ π₁ ∘ id , g ⟩) (symm ident₂) ⟩
        ⟨ π₁ ∘ id , π₂ ∘ id ⟩
      ≡⟨ g-η id ⟩
        id
      ∎
   where open Reasoning (A×B ⇒ A×B)

record _Has-Products {i j} (C : Category {i} {j}) : Set (i ⊔ j) where
  open Cat C

  field
    has-product : ∀{A B} → (C Product) A B

  infixr 65 _×_
  _×_ : Obj → Obj → Obj
  A × B = _Product.A×B (has-product {A} {B})

  private
    module Local {A B : Obj} where
      open _Product (has-product {A} {B}) public

  open Local public
    using ( π₁ ; π₂ ; ⟨_,_⟩ ; commute₁ ; commute₂ ; universal ; g-η ; η )

  Δ : ∀{A} → A ⇒ A × A
  Δ = ⟨ id , id ⟩

  _-×-_ : ∀{A B C D} → (A ⇒ C) → (B ⇒ D) → (A × B ⇒ C × D)
  f -×- g = ⟨ f ∘ π₁ , g ∘ π₂ ⟩

  ×-swap : ∀{A B} → A × B ≅ B × A
  ×-swap {A} {B} = record { iso⇒     = ⟨ π₂ , π₁ ⟩
                          ; iso⇐     = ⟨ π₂ , π₁ ⟩
                          ; inverse⇒ = iso-lemma
                          ; inverse⇐ = iso-lemma
                          }
   where
   id' : ∀{A B} → A × B ⇒ A × B
   id' = ⟨ π₂ , π₁ ⟩ ∘ ⟨ π₂ , π₁ ⟩

   lemma₁ : ∀{A B} → Commutes (id' {A} {B}) π₁ π₁
   lemma₁ {A} {B} = begin
                      π₁ ∘ (⟨ π₂ , π₁ ⟩ ∘ ⟨ π₂ , π₁ ⟩)
                    ≡⟨ assoc ⟩
                      (π₁ ∘ ⟨ π₂ , π₁ ⟩) ∘ ⟨ π₂ , π₁ ⟩
                    ≡⟨ cong (λ f → f ∘ ⟨ π₂ , π₁ ⟩) (commute₁ π₂) ⟩
                      π₂ ∘ ⟨ π₂ , π₁ ⟩
                    ≡⟨ commute₂ π₁ ⟩
                      π₁
                    ∎
    where open Reasoning (A × B ⇒ A)

   lemma₂ : ∀{A B} → Commutes (id' {A} {B}) π₂ π₂
   lemma₂ {A} {B} = begin
                      π₂ ∘ (⟨ π₂ , π₁ ⟩ ∘ ⟨ π₂ , π₁ ⟩)
                    ≡⟨ assoc ⟩
                      (π₂ ∘ ⟨ π₂ , π₁ ⟩) ∘ ⟨ π₂ , π₁ ⟩
                    ≡⟨ cong (λ f → f ∘ ⟨ π₂ , π₁ ⟩) (commute₂ π₁) ⟩
                      π₁ ∘ ⟨ π₂ , π₁ ⟩
                    ≡⟨ commute₁ π₂ ⟩
                      π₂
                    ∎
    where open Reasoning (A × B ⇒ B)

   iso-lemma : ∀{A B} → id' {A} {B} ≡ id
   iso-lemma {A} {B} = begin
                         id'
                       ≡⟨ symm (universal π₁ π₂ id' lemma₁ lemma₂) ⟩
                         ⟨ π₁ , π₂ ⟩
                       ≡⟨ η ⟩
                         id
                       ∎
    where open Reasoning (A × B ⇒ A × B)


  ×-assoc : ∀{A B C} → A × (B × C) ≅ (A × B) × C
  ×-assoc {A} {B} {C} = record { iso⇒     = i₁
                               ; iso⇐     = i₂
                               ; inverse⇒ = iso⇒
                               ; inverse⇐ = iso⇐
                               }
   where
   i₁ : A × (B × C) ⇒ (A × B) × C
   i₁ = ⟨ ⟨ π₁ , π₁ ∘ π₂ ⟩ , π₂ ∘ π₂ ⟩

   i₂ : (A × B) × C ⇒ A × (B × C)
   i₂ = ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩

   id⇒ : A × (B × C) ⇒ A × (B × C)
   id⇒ = i₂ ∘ i₁

   id⇐ : (A × B) × C ⇒ (A × B) × C
   id⇐ = i₁ ∘ i₂

   cm⇒₁ : π₁ ∘ id⇒ ≡ π₁
   cm⇒₁ = begin
            π₁ ∘ id⇒
          ≡⟨ assoc ⟩
            (π₁ ∘ i₂) ∘ i₁
          ≡⟨ cong (λ g → g ∘ i₁) (commute₁ (π₁ ∘ π₁)) ⟩
            (π₁ ∘ π₁) ∘ i₁
          ≡⟨ symm assoc ⟩
            π₁ ∘ (π₁ ∘ i₁)
          ≡⟨ cong (_∘_ π₁) (commute₁ ⟨ π₁ , π₁ ∘ π₂ ⟩) ⟩
            π₁ ∘ ⟨ π₁ , π₁ ∘ π₂ ⟩
          ≡⟨ commute₁ π₁ ⟩
            π₁
          ∎
    where open Reasoning (A × (B × C) ⇒ A)

   cm⇒₂₁ : π₁ ∘ (⟨ π₂ ∘ π₁ , π₂ ⟩ ∘ i₁) ≡ π₁ ∘ π₂
   cm⇒₂₁ = begin
             π₁ ∘ (⟨ π₂ ∘ π₁ , π₂ ⟩ ∘ i₁)
           ≡⟨ assoc ⟩
             (π₁ ∘ ⟨ π₂ ∘ π₁ , π₂ ⟩) ∘ i₁
           ≡⟨ cong (λ g → g ∘ i₁) (commute₁ (π₂ ∘ π₁)) ⟩
             (π₂ ∘ π₁) ∘ i₁
           ≡⟨ symm assoc ⟩
             π₂ ∘ (π₁ ∘ i₁)
           ≡⟨ cong (_∘_ π₂) (commute₁ ⟨ π₁ , π₁ ∘ π₂ ⟩) ⟩
             π₂ ∘ ⟨ π₁ , π₁ ∘ π₂ ⟩
           ≡⟨ commute₂ (π₁ ∘ π₂) ⟩
             π₁ ∘ π₂
           ∎
    where open Reasoning (A × (B × C) ⇒ B)

   cm⇒₂₂ : π₂ ∘ (⟨ π₂ ∘ π₁ , π₂ ⟩ ∘ i₁) ≡ π₂ ∘ π₂
   cm⇒₂₂ = begin
             π₂ ∘ (⟨ π₂ ∘ π₁ , π₂ ⟩ ∘ i₁)
           ≡⟨ assoc ⟩
             (π₂ ∘ ⟨ π₂ ∘ π₁ , π₂ ⟩) ∘ i₁
           ≡⟨ cong (λ f → f ∘ i₁) (commute₂ π₂) ⟩
             π₂ ∘ i₁
           ≡⟨ commute₂ (π₂ ∘ π₂) ⟩
             π₂ ∘ π₂
           ∎
    where open Reasoning (A × (B × C) ⇒ C)

   cm⇒₂ : π₂ ∘ id⇒ ≡ π₂
   cm⇒₂ = begin
            π₂ ∘ id⇒
          ≡⟨ assoc ⟩
            (π₂ ∘ i₂) ∘ i₁
          ≡⟨ cong (λ g → g ∘ i₁) (commute₂ ⟨ π₂ ∘ π₁ , π₂ ⟩) ⟩
            ⟨ π₂ ∘ π₁ , π₂ ⟩ ∘ i₁
          ≡⟨ symm (universal (π₁ ∘ π₂) (π₂ ∘ π₂) (⟨ π₂ ∘ π₁ , π₂ ⟩ ∘ i₁)
                       cm⇒₂₁ cm⇒₂₂) ⟩
            ⟨ π₁ ∘ π₂ , π₂ ∘ π₂ ⟩
          ≡⟨ g-η π₂ ⟩
            π₂
          ∎
    where open Reasoning (A × (B × C) ⇒ B × C)

   iso⇒ : id⇒ ≡ id
   iso⇒ = begin
            id⇒
          ≡⟨ symm (universal π₁ π₂ id⇒ cm⇒₁ cm⇒₂) ⟩
            ⟨ π₁ , π₂ ⟩
          ≡⟨ η ⟩
            id
          ∎
    where open Reasoning (A × (B × C) ⇒ A × (B × C))


   cm⇐₁₁ : π₁ ∘ (⟨ π₁ , π₁ ∘ π₂ ⟩ ∘ i₂) ≡ π₁ ∘ π₁
   cm⇐₁₁ = begin
             π₁ ∘ (⟨ π₁ , π₁ ∘ π₂ ⟩ ∘ i₂)
           ≡⟨ assoc ⟩
             (π₁ ∘ ⟨ π₁ , π₁ ∘ π₂ ⟩) ∘ i₂
           ≡⟨ cong (λ g → g ∘ i₂) (commute₁ π₁) ⟩
             π₁ ∘ i₂
           ≡⟨ commute₁ (π₁ ∘ π₁) ⟩
             π₁ ∘ π₁
           ∎
    where open Reasoning ((A × B) × C ⇒ A)

   cm⇐₁₂ : π₂ ∘ (⟨ π₁ , π₁ ∘ π₂ ⟩ ∘ i₂) ≡ π₂ ∘ π₁
   cm⇐₁₂ = begin
             π₂ ∘ (⟨ π₁ , π₁ ∘ π₂ ⟩ ∘ i₂)
           ≡⟨ assoc ⟩
             (π₂ ∘ ⟨ π₁ , π₁ ∘ π₂ ⟩) ∘ i₂
           ≡⟨ cong (λ g → g ∘ i₂) (commute₂ (π₁ ∘ π₂)) ⟩
             (π₁ ∘ π₂) ∘ i₂
           ≡⟨ symm assoc ⟩
             π₁ ∘ (π₂ ∘ i₂)
           ≡⟨ cong (_∘_ π₁) (commute₂ ⟨ π₂ ∘ π₁ , π₂ ⟩) ⟩
             π₁ ∘ ⟨ π₂ ∘ π₁ , π₂ ⟩
           ≡⟨ commute₁ (π₂ ∘ π₁) ⟩
             π₂ ∘ π₁
           ∎
    where open Reasoning ((A × B) × C ⇒ B)

   cm⇐₁ : π₁ ∘ id⇐ ≡ π₁
   cm⇐₁ = begin
            π₁ ∘ id⇐
          ≡⟨ assoc ⟩
            (π₁ ∘ i₁) ∘ i₂
          ≡⟨ cong (λ g → g ∘ i₂) (commute₁ ⟨ π₁ , π₁ ∘ π₂ ⟩) ⟩
            ⟨ π₁ , π₁ ∘ π₂ ⟩ ∘ i₂
          ≡⟨ symm (universal (π₁ ∘ π₁) (π₂ ∘ π₁) (⟨ π₁ , π₁ ∘ π₂ ⟩ ∘ i₂)
                       cm⇐₁₁ cm⇐₁₂) ⟩
            ⟨ π₁ ∘ π₁ , π₂ ∘ π₁ ⟩
          ≡⟨ g-η π₁ ⟩
            π₁
          ∎
    where open Reasoning ((A × B) × C ⇒ A × B)

   cm⇐₂ : π₂ ∘ id⇐ ≡ π₂
   cm⇐₂ = begin
            π₂ ∘ id⇐
          ≡⟨ assoc ⟩
            (π₂ ∘ i₁) ∘ i₂
          ≡⟨ cong (λ g → g ∘ i₂) (commute₂ (π₂ ∘ π₂)) ⟩
            (π₂ ∘ π₂) ∘ i₂
          ≡⟨ symm assoc ⟩
            π₂ ∘ (π₂ ∘ i₂)
          ≡⟨ cong (λ g → π₂ ∘ g) (commute₂ ⟨ π₂ ∘ π₁ , π₂ ⟩) ⟩
            π₂ ∘ ⟨ π₂ ∘ π₁ , π₂ ⟩
          ≡⟨ commute₂ π₂ ⟩
            π₂
          ∎
    where open Reasoning ((A × B) × C ⇒ C)

   iso⇐ : id⇐ ≡ id
   iso⇐ = begin
            id⇐
          ≡⟨ symm (universal π₁ π₂ id⇐ cm⇐₁ cm⇐₂) ⟩
            ⟨ π₁ , π₂ ⟩
          ≡⟨ η ⟩
            id
          ∎
    where open Reasoning ((A × B) × C ⇒ (A × B) × C)


record _Terminal {i j} (C : Category {i} {j}) : Set (i ⊔ j) where
  open Cat C

  field
    ⊤ : Obj

    ! : ∀{A} → A ⇒ ⊤

    universal : ∀{A} → (f : A ⇒ ⊤) → ! ≡ f

