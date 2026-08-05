{-# OPTIONS --universe-polymorphism #-}

module FinalAlgebra where

open import Level

open import Relation.Binary.PropositionalEquality

record Category : Set₁ where
  infixr 10 _⇒_
  infixr 90 _∘_
  field
    Obj : Set
    _⇒_ : Obj → Obj → Set

    id  : ∀{A} → A ⇒ A
    _∘_ : ∀{A B C} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C)

    identˡ : ∀{A B} → (f : A ⇒ B) → id ∘ f ≡ f
    identʳ : ∀{A B} → (f : A ⇒ B) → f ∘ id ≡ f
    assoc  : ∀{A B C D} → (f : A ⇒ B) (g : B ⇒ C) (h : C ⇒ D)
           → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f

record Endofunctor (C : Category) : Set where
  open Category C

  infixl 90 _∙_
  field
    _∙_ : Obj → Obj
    map : ∀{A B} → (A ⇒ B) → (_∙_ A ⇒ _∙_ B)

    map-id : ∀{A} → map (id {A}) ≡ id
    map-∘  : ∀{A B C} → (f : A ⇒ B) (g : B ⇒ C) → map (g ∘ f) ≡ map g ∘ map f

open Endofunctor using (_∙_)

record Algebra {C : Category} (F : Endofunctor C) : Set where
  open Category C
  open Endofunctor F hiding (_∙_)
  field
    Carrier : Obj
    action  : F ∙ Carrier ⇒ Carrier

record _⟶_ {C : Category} {F : Endofunctor C} (A B : Algebra F) : Set where
  open Category C
  open Endofunctor F hiding (_∙_)
  open Algebra
  field
    arr : Carrier A ⇒ Carrier B

    coh : arr ∘ action A ≡ action B ∘ map arr

record Final (C : Category) : Set where
  open Category C
  field
    ⊤ : Obj
    ! : ∀{A} → A ⇒ ⊤

    universal : ∀{A} → (f : A ⇒ ⊤) → f ≡ !

module Func (C : Category)
            (F : Endofunctor C)
            (X : Final C) where
  open Category C
  open Endofunctor F
  open Final X

  -- The proposed final algebra
  Term : Algebra F
  Term = record { Carrier = ⊤; action = ! }

  -- The algebra morphism to the final algebra.
  !! : {A : Algebra F} → A ⟶ Term
  !! {A} = record { arr = !
                  ; coh = begin
                            ! ∘ action
                          ≡⟨ universal (! ∘ action) ⟩
                            !
                          ≡⟨ sym (universal (! ∘ map !)) ⟩
                            ! ∘ map !
                          ∎
                  }
   where
   open Algebra A
   open ≡-Reasoning

  -- !! is universal.
  Universal : ∀{A} → (h : A ⟶ Term) → _⟶_.arr h ≡ !
  Universal h = universal (_⟶_.arr h)

  -- So, for a category C, an endofunctor F : C → C, and
  -- a final object ⊤ of C, ⊤ is a final F-algebra.

record Monad (C : Category) : Set where
  open Category C
  field
    Endo : Endofunctor C

  open Endofunctor Endo hiding (_∙_)

  field
    η : ∀{A} → A ⇒ Endo ∙ A
    μ : ∀{A} → Endo ∙ (Endo ∙ A) ⇒ Endo ∙ A

    -- Hopefully, naturality of η and μ is unnecessary here.

    m-ident₁ : ∀{A} → μ ∘     η ≡ id {Endo ∙ A}
    m-ident₂ : ∀{A} → μ ∘ map η ≡ id {Endo ∙ A}
    m-assoc  : ∀{A} → μ {A} ∘ μ ≡ μ ∘ map μ

  open Endofunctor Endo public

record MAlgebra {C : Category} (M : Monad C) : Set where
  open Category C
  open Monad M
  field
    alg : Algebra Endo
    
  open Algebra alg

  field
    η-coh : action ∘ η ≡ id
    μ-coh : action ∘ μ ≡ action ∘ map action

module Mon (C : Category)
           (M : Monad C)
           (X : Final C) where
  open Category C
  open Monad M
  open Final X

  open ≡-Reasoning

  -- The final algebra for the underlying endofunctor is also
  -- a monad algebra.
  Term : MAlgebra M
  Term = record { alg   = Func.Term C Endo X
                ; η-coh = begin
                            ! ∘ η
                          ≡⟨ universal (! ∘ η) ⟩
                            !
                          ≡⟨ sym (universal id) ⟩
                            id
                          ∎
                ; μ-coh = begin
                            ! ∘ μ
                          ≡⟨ universal (! ∘ μ) ⟩
                            !
                          ≡⟨ sym (universal (! ∘ map !)) ⟩
                            ! ∘ map !
                          ∎
                }

  -- Since monad algebra homomorphisms are defined the same way as
  -- morphisms for algebras of the underlying functor, the previous
  -- proofs that the above algebra is final should suffice.

  -- So, if C is a category with a terminal object X, and M is any
  -- monad, (X, !) is a final M-algebra.
