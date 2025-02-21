{-# OPTIONS --cubical --allow-unsolved-meta #-}

open import Cubical.Core.Primitives
-- open import Cubical.Foundations.Prelude

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

data UnorderedPair (X : Set) : Set where
  pair : (a b : X) → UnorderedPair X
  swap : (a b : X) → pair a b ≡ pair b a

data ⊥ : Set where

-- EXERCISE: Implement "cong". Because the name "cong" is already
-- exported from the standard library, we use a different name.
cong' : {X Y : Set} {a b : X} → (f : X → Y) → a ≡ b → f a ≡ f b
cong' = {!!}

-- EXERCISE: Show that zero is not succ zero.
--
-- With the inductive definition of _≡_ we used before, this required
-- an empty pattern. Now that _≡_ is no longer inductively defined,
-- but an in-built notion, we cannot case split on equality witnesses.
--
-- Instead, proceed as follows:
-- 1. Define a function "disambig : ℕ → Set" which maps zero to ⊥
--    and everything else to some inhabited type.
-- 2. Assuming that there is a path "zero ≡ succ zero", combine
--    "transport" from the standard library and "disambig":
--        transport : {A B : Set} → A ≡ B → A → B
--
-- Note that "symm" is spelt "sym" in the cubical standard library
-- and "trans" is written as the binary operator "∙" (\.).
lemma-nontrivial : zero ≡ succ zero → ⊥
lemma-nontrivial p = {!!}

-- EXERCISE: Show that the unordered pair abstraction
-- is not leaky, in the sense that there cannot be a
-- function which would extract the first component
-- of an unordered pair.
lemma-not-leaky : (f : UnorderedPair ℕ → ℕ) (p : (a b : ℕ) → f (pair a b) ≡ a) → ⊥
lemma-not-leaky = {!!}

-- EXERCISE: Show that negations are propositions, in the following sense.
isProp' : Set → Set
isProp' X = (a b : X) → a ≡ b

lemma-negations-are-props : (X : Set) → isProp' (X → ⊥)
lemma-negations-are-props = {!!}

-- EXERCISE: Show that 𝟙 and Interval are the same, in the following sense.
data 𝟙 : Set where
  * : 𝟙

data Interval : Set where
  left  : Interval
  right : Interval
  path  : left ≡ right

toInterval : 𝟙 → Interval
toInterval * = left

fromInterval : Interval → 𝟙
fromInterval _ = *

is-iso₁ : (x : 𝟙) → fromInterval (toInterval x) ≡ x
is-iso₁ = {!!}

is-iso₂ : (x : Interval) → toInterval (fromInterval x) ≡ x
is-iso₂ = {!!}


-- EXERCISE: Show that ℕ is discrete, in the following sense.
isDiscrete : Set → Set
isDiscrete X = (a b : X) → isProp' (a ≡ b)

Code : ℕ → ℕ → Set
Code zero     zero     = 𝟙
Code zero     (succ y) = ⊥
Code (succ x) zero     = ⊥
Code (succ x) (succ y) = Code x y

fromCode : (a b : ℕ) → Code a b → a ≡ b
fromCode a b p = {!!}

ref : (a : ℕ) → Code a a
ref a = {!!}

-- Hint: Use "J" or "transport"!
toCode : (a b : ℕ) → a ≡ b → Code a b
toCode = {!!}

lemma-ℕ-discrete : isDiscrete ℕ
lemma-ℕ-discrete = {!!}
