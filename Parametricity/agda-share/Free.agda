
-- The code herein is based on the blog post here:
--
--     http://gelisam.blogspot.com/2009/09/samuels-really-straightforward-proof-of.html
module Free where

infixl 80 _∘_
_∘_ : ∀{A B C : Set} → (B → C) → (A → B) → A → C
(g ∘ f) x = g (f x)

infix 30 _≡_
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

data ⊥ : Set where

record ⊤ : Set where

record Set# : Set₁ where
  field
    A  : Set
    A' : Set
    A~ : A → A' → Set

record value# (A# : Set#) : Set where
  open Set# A#
  field
    x  : A
    x' : A'
    x~ : A~ x x'

∀A,A→A# : Set₁
∀A,A→A# = (A# : Set#) → value# A# → value# A#

postulate
  param : ∀{B C} {x : B} {y : C} 
           (_~_ : B → C → Set)
        → (id : (A : Set) → A → A)
        → x ~ y → id B x ~ id C y

parametricity : (∀(A : Set) → A → A) → ∀A,A→A#
parametricity id A# x# = record { x  = id (Set#.A A#) (value#.x x#)
                                ; x' = id (Set#.A' A#) (value#.x' x#) 
                                ; x~ = param (Set#.A~ A#) id (value#.x~ x#) }


Rel : ∀{A B : Set} → (f : A → B) → A → B → Set
Rel f x y = f x ≡ y

infix 40 _#
_# : ∀{A B} → (A → B) → Set#
_# {A} {B} f = record { A = A ; A' = B ; A~ = Rel f }

_#'_ : ∀{A B} (f : A → B) → A → value# (f #)
f #' x = record { x = x ; x' = f x ; x~ = refl }

module Free-id {A B : Set} (id# : ∀A,A→A#) (f : A → B) where
  -- (id,id') ∈ ∀α. α ⟶ α
  -- (x,y) ∈ f : A → B           f x ≡ y
  -- (id A x, id' B y) ∈ f       f (id x) ≡ id' (f x)

  -- id#          = (id,id')
  -- f #' x       = (x, y)
  -- id# (f #' x) = (id A x, id' B y)
  
  free : A → value# (f #)
  free x = id# (f #) (f #' x)

  free' : (x : A) → _
  free' x = value#.x~ (free x)

free : ∀{B C}
        (f : B → C) (id : ∀ A → A → A) → (x : B)
     → f (id B x) ≡ id C (f x)
free f id x = Free-id.free' id# f x
  where
  id# : ∀A,A→A#
  id# = parametricity id
