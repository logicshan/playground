
-- Deciding equality via retraction from decidable sets.

module DecEq where

open import Data.Nat
open import Data.Nat using (_≟_)

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

import Relation.Binary.EqReasoning as EqReasoning

record Retract (A B : Set) : Set where
  field
    section    : A → B
    retraction : B → A

    inverse : ∀ x → retraction (section x) ≡ x


module RetractDec {A B} (_≟_ : Decidable {A = B} _≡_)
                        (retr : Retract A B) where
  open Retract retr

  open EqReasoning (setoid A)

  dec : Decidable {A = A} _≡_
  dec x y with section x ≟ section y
  ... | yes sx≡sy = yes (begin
                           x
                         ≡⟨ sym (inverse x) ⟩
                           retraction (section x)
                         ≡⟨ cong retraction sx≡sy ⟩
                           retraction (section y)
                         ≡⟨ inverse y ⟩
                           y 
                         ∎)
  ... | no  sx≢sy = no (λ x≡y → sx≢sy (cong section x≡y))

data Foo : Set where
  one two three four : Foo

-- Line 45
_≟-Foo_ : Decidable {A = Foo} _≡_
_≟-Foo_ = RetractDec.dec _≟_ (record { section    = map→
                                     ; retraction = map←
                                     ; inverse = id₁ })
 where
 map→ : Foo → ℕ
 map→ one   = 0
 map→ two   = 1
 map→ three = 2
 map→ four  = 3

 map← : ℕ → Foo
 map← 0 = one
 map← 1 = two
 map← 2 = three
 map← 3 = four
 map← _ = one

 id₁ : ∀ x → map← (map→ x) ≡ x
 id₁ one   = refl
 id₁ two   = refl
 id₁ three = refl
 id₁ four  = refl
-- Line 69
-- 69 - 45 = 24 lines

