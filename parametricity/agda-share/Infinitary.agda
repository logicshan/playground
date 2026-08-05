{-# OPTIONS --safe #-}

module Infinitary where

open import Function
open import Data.Empty
open import Data.List
  hiding (_─_)
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.Any
  hiding (map)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product hiding (map)
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; subst; sym )

variable A B : Set

-- A set is (Kuratowski) finite if we can list all its values.
is-finite : Set → Set
is-finite A = Σ[ xs ∈ List A ] ∀(x : A) → x ∈ xs

not-finite : Set → Set
not-finite A = ¬ is-finite A

-- A set is infinite if the natural numbers embed in it
is-infinite : Set → Set
is-infinite A = ℕ ↣ A

-- A set avoids lists if there is a function from lists of
-- values to values that the list doesn't contain.
avoids-lists : Set → Set
avoids-lists A = ∀(xs : List A) → Σ[ x ∈ A ] x ∉ xs

-- Every list-avoiding type is infinite
avoids-lists⇒is-infinite : avoids-lists A → is-infinite A
avoids-lists⇒is-infinite av = λ where
    .to → enumerate
    .cong refl → refl
    .injective → enumerate-inj _ _
  where
  open Injection
  -- `listed` builds a list of the first `n` elements of the
  -- enumeration. `enumerate` yields the next element that
  -- avoids the list of the given size.
  listed : ℕ → List _
  enumerate : ℕ → _

  enumerate n = av (listed n) .proj₁

  listed 0 = []
  listed (suc n) = enumerate n ∷ listed n

  -- Every earlier value occurs in the listing.
  lemma : ∀{m n} → m < n → enumerate m ∈ listed n
  lemma = search ∘ <⇒<′
    where
    search : ∀{m n} → m <′ n → enumerate m ∈ listed n
    search <′-base = here refl
    search (≤′-step m<′n) = there (search m<′n)

  -- The enumerate function is injective.
  enumerate-inj
    : ∀(m n : ℕ) → enumerate m ≡ enumerate n → m ≡ n
  -- Test the relative ordering of m and n
  enumerate-inj m n e with <-cmp m n
  -- If they are equal, we are done.
  ... | tri≈ _ m≡n _ = m≡n
  -- If m < n, then we know that enumerate m ∈ listed n, but
  -- then enumerate n ∈ listed n, which we were told is not
  -- the case by list avoidance.
  ... | tri< m<n _ _ = ⊥-elim (av (listed n) .proj₂ enum-n∈list-n)
    where
    enum-n∈list-n : enumerate n ∈ listed n
    enum-n∈list-n rewrite sym e = lemma m<n
  -- The same argument, but with the opposite ordering.
  ... | tri> _ _ n<m = ⊥-elim (av (listed m) .proj₂ enum-m∈list-m)
    where
    enum-m∈list-m : enumerate m ∈ listed m
    enum-m∈list-m rewrite e = lemma n<m

-- Every infinite type is not finite
--
-- From agda-stdlib
is-infinite⇒not-finite : is-infinite A → not-finite A
is-infinite⇒not-finite inf (xs , axs) =
  finite inf xs (axs ∘ to inf)
  where open Injection
