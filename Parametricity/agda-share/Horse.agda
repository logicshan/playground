
-- An encoding of the classic proof by induction that all horses
-- are the same color.

module Horse where

data ∃ {A : Set} (T : A → Set) : Set where
  _,_ : (x : A) (w : T x) → ∃ T

-- Natural numbers, starting at 1 instead of the usual 0
data ℕ : Set where
  one : ℕ
  suc : ℕ → ℕ

-- Induction on the naturals
induction : (P : ℕ → Set) → P one → (∀ n → P n → P (suc n)) → ∀ n → P n
induction P P1 Pn one     = P1
induction P P1 Pn (suc n) = Pn n (induction P P1 Pn n)

-- Finite sets with natural numbers of elements. We'll assume that we
-- always have a finite number of horses.
data Fin : ℕ → Set where
  zero : ∀{n} → Fin n
  suc  : ∀{n} → Fin n → Fin (suc n)

-- An injection from smaller finite sets to larger ones not using the
-- successor operation. 0 -> 0, 1 -> 1, etc.
lift : ∀{n} → Fin n → Fin (suc n)
lift zero     = zero
lift (suc fn) = suc (lift fn)

-- Horse colors
data Color : Set where
  black : Color
  brown : Color
  white : Color

-- Value equality
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

symm : ∀{A} {x y : A} → x ≡ y → y ≡ x
symm refl = refl

trans : ∀{A} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

-- Representations of the colors of finite sets of horses.
Coloring : ℕ → Set
Coloring n = Fin n → Color

-- Given a set of n+1 horses and their colors, gives a set of
-- n horses and their colors by removing the 'last' horse from the set.
init : ∀{n} → Coloring (suc n) → Coloring n
init c n = c (lift n)

-- Like the above, only removing the 'first' horse.
tail : ∀{n} → Coloring (suc n) → Coloring n
tail c n = c (suc n)

-- Fin n → A is an encoding of vectors of As of size n. All represents
-- a proof that a predicate holds for all elements of the vector.
All : ∀{n} {A : Set} → (P : A → Set) → (Fin n → A) → Set
All P v = ∀ i → P (v i)

-- A proof that all horses in a given set are the same color.
Uniform : ∀{n} → Coloring n → Set
Uniform C = ∃ (λ c → All (_≡_ c) C)

-- This module assumes the flawed part of the reasoning for the
-- induction proof. The inductive case of the proof requires that
-- for a set of n+1 horses, if we remove a horse in two different ways,
-- and the resulting sets all have horses of the same color, then
-- the original set has horses of all the same color.
--
-- However, this fact would itself have to be proved by induction, and
-- the base case of that proof does not hold, as two horses are not the
-- same color given that each is the same color as itself.
module Trick (wrong : ∀{n} → (C : Coloring (suc n))
                           → Uniform (init C)
                           → Uniform (tail C)
                           → Uniform C) where

  same : ∀{n} → (C : Coloring n) → Uniform C
  same {n} C = induction P base ind n C
   where
   P : ℕ → Set
   P n = (C : Coloring n) → Uniform C

   ind : ∀ n → P n → P (suc n)
   ind n Pn C = wrong C (Pn (init C)) (Pn (tail C))

   base : P one
   base C = C zero , pf
    where pf : All (_≡_ (C zero)) C
          pf zero = refl
