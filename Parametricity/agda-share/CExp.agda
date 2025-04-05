{-# OPTIONS --universe-polymorphism #-}

-- A proof (of arguably completeness) that the functor
--
--   (─)A : Sets^C → Sets
--   (F)A = FA
--
-- has a right adjoint if C is a discrete category

-- A discrete category can be regarded as a set. Objects of C are the
-- elements, and the fact that there exist only identity morphisms
-- is rougly equivalent to equality of elements, in that
--
--  Hom(A,B) is empty if A ≠ B, and is {id_A} if A = B
--
-- Thus, here, C is taken as a type, and the built-in equality A ≡ B is
-- used instead of Hom(A,B)

module CExp (C : Set) where

open import Level

data _≡_ {i} {A : Set i} (x : A) : A → Set where
  refl : x ≡ x

-- Assume that equality of functions is extensional─if f and g agree on
-- all arguments, then they are equal. This is not given in Agda, but
-- is true in set theory.
postulate
  ext : ∀{F : C → Set} {A} {B : Set} → {f g : (X : C) → F X → X ≡ A → B}
      → (∀ X FX eq → f X FX eq ≡ g X FX eq) → f ≡ g

-- The (─)A functor, F ↦ FA
─ : C → (C → Set) → Set
(─)A F = F A

-- Natural transformations between two C → Set functors. Technically
-- we should include some naturality conditions, but we'll dispense with
-- that extra work.
_⇒_ : (C → Set) → (C → Set) → Set
F ⇒ G = ∀ X → F X → G X

-- The proposed right adjoint to (─)A
--
--   G A : Sets → Sets^C
--   G A B X = Hom(Hom(X,A),B)
--
-- Here we use X ≡ A instead of Hom(X,A), because the category is
-- discrete, and thus:
--
--   G A B A = Hom({⋆}, B)
--   G A B X = Hom({} , B) for A ≠ X
G : C → Set → (C → Set)
G A B X = X ≡ A → B

-- This is a helper function for the left-to-right part of the
-- adjunction. It takes the morphism f : FA → B and returns the
-- natural transformation φ : F ⇒ G A B. All the components of
-- the transformation except for the A component simply produce
-- the empty function, while the A component produces f.
--
-- In category theory, this would be something like
--
--  blip A F B f X FX g = (f ∘ Fg) FX
--
-- since
--
--  g : X → A
--  f : FA → B
--  f ∘ Fg : FX → B
--
-- And then the proof in aux would of course be different.
blip : ∀ A F (B : Set) (f : (─)A F → B) → (F ⇒ G A B)
blip A F B f .A FA refl = f FA

-- isomorphisms of sets
record _≅_ (A B : Set) : Set where
  field
    ♯ : A → B
    ♭ : B → A

    iso⇒ : ∀ x → ♭ (♯ x) ≡ x
    iso⇐ : ∀ y → ♯ (♭ y) ≡ y

-- Adjunctions (specialized to the types we care about in this example
-- for simplicity).
_⊣_ : ((C → Set) → Set) → (Set → (C → Set)) → Set₁
G ⊣ H = ∀ F B → (G F → B) ≅ (F ⇒ H B)

-- The isomorphism component of the adjunction proof. Technically again
-- we should show that the isomorphism is natural in F and B, but that's
-- a lot of extra modeling work.
adj : ∀ A → (─)A ⊣ G A
adj A F B = record { ♯ = λ f → blip A F B f
                   ; ♭ = λ φ FA → φ A FA refl
                   ; iso⇒ = λ _ → refl
                   ; iso⇐ = λ φ → ext (aux φ)
                   }
 where
 -- Here we observe that the only non-empty case for X ≡ A is refl : A ≡ A,
 -- and so our isomorphism preserves 'natural transformations'. In the
 -- category theoretic version, this would correspond (I believe) to
 -- observing that Hom(X,A) is either empty or contains only an identity.
 -- So, when X = A
 --
 --    φ_A : FA → G A B A = FA → Hom({id_A},B)
 --
 -- and when X ≠ A
 --
 --    φ_X : FX → Hom({},B)
 --
 -- So, φ is fully determined by its value at A, because all other cases
 -- are trivial. Further, B^{id_A} is isomorphic to B, so φ_A must be
 -- equivalent to a morphism FA → B, which is what we have on the other
 -- side of the isomorphism. Thus, with some hand waving, a round trip
 -- through our isomorphism preserves the only non-trivial pieces of
 -- information we have, probably making use of the fact that:
 --
 --    φ_A ∘ Fid_A = φ_A ∘ id_FA = φ_A
 --
 -- and id_A is the only thing inhabiting Hom(A,A).
 aux : ∀(φ : ∀ X → F X → X ≡ A → B) X (FX : F X) (eq : X ≡ A)
     → blip A F B (λ FA → φ A FA refl) X FX eq ≡ φ X FX eq
 aux φ .A FA refl = refl

