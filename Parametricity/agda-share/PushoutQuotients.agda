{-# OPTIONS --universe-polymorphism #-}

-- Given pushouts we get quotients

module PushoutQuotients where

open import Function

open import Relation.Binary.PropositionalEquality

Rel : Set → Set₁
Rel A = A → A → Set

record Pushout {A B C : Set}
               (f : A → B) (g : A → C) : Set₁ where
  field
    D : Set
    inj₁ : B → D
    inj₂ : C → D

    comm : ∀ x → inj₁ (f x) ≡ inj₂ (g x)

    out : ∀{E : Set} (i₁ : B → E) (i₂ : C → E)
        → (∀ x → i₁ (f x) ≡ i₂ (g x))
        → (D → E)

    factor₁ : ∀{E} {i₁ : B → E} {i₂ : C → E}
            → (c : ∀ x → i₁ (f x) ≡ i₂ (g x))
            → ∀ y → i₁ y ≡ out i₁ i₂ c (inj₁ y)

    factor₂ : ∀{E} {i₁ : B → E} {i₂ : C → E}
            → (c : ∀ x → i₁ (f x) ≡ i₂ (g x))
            → ∀ z → i₂ z ≡ out i₁ i₂ c (inj₂ z)

    unique : ∀{E} {i₁ : B → E} {i₂ : C → E}
           → (c : ∀ x → i₁ (f x) ≡ i₂ (g x))
           → (o : D → E)
           → (∀ y → i₁ y ≡ o (inj₁ y))
           → (∀ z → i₂ z ≡ o (inj₂ z))
           → ∀ w → out i₁ i₂ c w ≡ o w

module HasPushout (mk : ∀{A B C} (f : A → B) (g : A → C) → Pushout f g) where
  -- A handy container for two values that are related
  record Eqv (A : Set) (R : Rel A) : Set where
    field
      π₁ : A
      π₂ : A
      pf : R π₁ π₂

  open Eqv

  module MkQuotient (A : Set)
                    (R : Rel A)
                    -- quotients are built using equivalence relations
                    -- although we don't use most of their features
                    (reflexive : ∀ x → R x x)
                    (symmetric : ∀ x y → R x y → R y x)
                    (transitive : ∀ x y z → R x y → R y z → R x z) where
    push : Pushout {Eqv A R} π₁ π₂
    push = mk π₁ π₂

    -- Q is the quotient type
    open Pushout push renaming (D to Q)

    diag : A → Eqv A R
    diag x = record { π₁ = x ; π₂ = x ; pf = reflexive x }

    -- The two ways of injecting into the quotient set are the same...
    lemma₀ : ∀ x → inj₁ x ≡ inj₂ x
    lemma₀ x = comm $ diag x

    -- so we arbitrarily pick the first for our official inclusion into
    -- equivalence classes
    [_] : A → Q
    [ x ] = inj₁ x

    -- Related values are taken to the same equivalence class.
    lemma₁ : ∀ x y → R x y → [ x ] ≡ [ y ]
    lemma₁ x y xRy = subst (λ z → [ x ] ≡ z) (sym $ lemma₀ y) (comm eqv)
      where
      eqv : Eqv A R
      eqv = record { π₁ = x ; π₂ = y ; pf = xRy }

    -- If we have a function that respects the relation, we can use it
    -- to eliminate the quotient type.
    elim : ∀{Z} → (f : A → Z) → (∀ x y → R x y → f x ≡ f y) → Q → Z
    elim f resp = out f f (λ eqv → resp (π₁ eqv) (π₂ eqv) (pf eqv))

    -- Inclusion into the quotient followed by elimination by f is the same
    -- as f.
    lemma₂ : ∀{Z} (f : A → Z) (resp : ∀ x y → R x y → f x ≡ f y)
           → ∀ x → f x ≡ elim f resp [ x ]
    lemma₂ f resp = factor₁ (λ eqv → resp (π₁ eqv) (π₂ eqv) (pf eqv))

    -- Eliminating with the inclusion is the identity (this is an eta rule).
    lemma₃ : ∀ q → elim [_] lemma₁ q ≡ q
    lemma₃ = unique (λ eqv → lemma₁ (π₁ eqv) (π₂ eqv) (pf eqv))
                    id (λ y → refl) lemma₀
