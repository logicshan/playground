{-# OPTIONS --cubical --allow-unsolved-metas #-}

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude

data ⊥ : Set where

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero   + b = b
succ a + b = succ (a + b)

one = succ zero
two = succ (succ zero)

-- the type of ordered pairs of natural numbers
data Pair : Set where
  mk : ℕ → ℕ → Pair

-- the type of unordered pairs of natural numbers
data UnorderedPair : Set where
  mk   : ℕ → ℕ → UnorderedPair
  swap : {a b : ℕ} → mk a b ≡ mk b a

ex : Pair
ex = mk one two

ex' : Pair
ex' = mk two one

unordered-ex : UnorderedPair
unordered-ex = mk one two

unordered-ex' : UnorderedPair
unordered-ex' = mk two one

_ : unordered-ex ≡ unordered-ex'
_ = swap 
{-
+comm : {x y : ℕ} → (x + y) ≡ (y + x)
+comm {zero} {zero} = refl
+comm {zero} {succ y} = cong succ (symm (+zero {y})) 
+comm {succ x} {zero} = cong succ (+zero {x})
+comm {succ x} {succ y} rewrite lemma-+-succ x y | lemma-+-succ y x
  = cong (λ z → succ (succ z)) (+comm {x} {y})
-}
{-
cong : {A B : Set} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
cong f p = λ i → f (p i)
-}
+zero : {x : ℕ} → x + zero ≡ x
+zero {zero} = λ i → zero
+zero {succ x} = cong succ (+zero {x})

+succ : {x y : ℕ} → x + (succ y) ≡ succ (x + y)
+succ {zero} {y} = refl
+succ {succ x} {y} = cong succ (+succ {x} {y})

+comm : {x y : ℕ} → (x + y) ≡ (y + x)
+comm {zero} {zero} = λ i → zero
+comm {zero} {succ y} = cong succ (sym (+zero {y}))
+comm {succ x} {zero} = cong succ (+zero {x})
+comm {succ x} {succ y} =
  succ (x + succ y)
    ≡⟨ cong succ (+succ {x} {y}) ⟩
  succ (succ (x + y))
    ≡⟨ cong (λ a → succ (succ a)) (+comm {x} {y}) ⟩
  succ (succ (y + x))
    ≡⟨ cong succ (sym (+succ {y} {x})) ⟩
  succ (y + succ x) ∎


unordered-sum : UnorderedPair → ℕ
unordered-sum (mk a b) = a + b
unordered-sum (swap {a} {b} i) = +comm {a} {b} i

-- with unordered pairs, the following function should NOT be implementable, and indeed, it isn't
first : UnorderedPair → ℕ
first (mk a b) = a
first (swap i) = {!!}

-- In standard Agda, we picture data types as collections of points.
-- In Cubical Agda, we picture data types as spaces.
data ℤmod4 : Set where
  zer  : ℤmod4
  suc  : ℤmod4 → ℤmod4
  loop : zer ≡ suc (suc (suc (suc zer)))
-- A picture of ℤmod4:
-- *    *    *    *    *    *    *   ...
-- v    |              ^    ^
-- +-->--->---->---->--+    |
--      | loop              ^
--      |                   |
--      v                   |
--      +--->---->--->--->--+


_ : suc zer ≡ suc (suc (suc (suc (suc zer))))
_ = cong suc loop

data Circle : Set where
  north : Circle
  loop  : north ≡ north

{-
  cubical/homotopy type theory unlocks a Rosetta stone between
  - logic
  - computation
  - homotopy theory

              logic                                       computation                      homotopy theory
  --------------------------------------------------------------------------------------------------------------------------------
  p : x ≡ y   proof of the statement that x equals y      witness that x equals y          path from x to y
  f : X → Y   function                                    algorithm                        map between the space X and the space Y
  ⊥           falsity                                     the empty data type              the empty space
  X           set                                         type                             space (up to deformation)
-}

data ℤ : Set where
  _⊝_ : ℕ → ℕ → ℤ     -- \o- \ominus
  -- interpretation: 2 ⊝ 5 means: I have 2 €, but I owe 5 €. (So, in total, I have -3 €.)
  --                 3 ⊝ 6 menas: I have 3 €, but I owe 6 €. (So, in total, I have -3 €.)
  cancel : (a b : ℕ) → a ⊝ b ≡ succ a ⊝ succ b

succℤ : ℤ → ℤ
succℤ (a ⊝ b) = succ a ⊝ b
succℤ (cancel a b i) = cancel (succ a) b i

_+ℤ_ : ℤ → ℤ → ℤ
(a ⊝ b) +ℤ (a' ⊝ b') = (a + a') ⊝ (b + b')
(a ⊝ b) +ℤ cancel a' b' i  = p i
  where
  p : (a + a') ⊝ (b + b') ≡ (a + succ a') ⊝ (b + succ b')
  p =
    (a + a') ⊝ (b + b')
      ≡⟨ cancel (a + a') (b + b') ⟩
    succ (a + a') ⊝ succ (b + b')
      ≡⟨ cong₂ _⊝_ (sym (+succ {a} {a'})) (sym (+succ {b} {b'})) ⟩
    (a + succ a') ⊝ (b + succ b') ∎
cancel a b i +ℤ (a' ⊝ b') = cancel (a + a') (b + b') i
cancel a b i +ℤ cancel a' b' j = {!!}
{-
cancel a b i +ℤ cancel a' b' j = hcomp (λ k → λ { (i = i0) (j = i0) → (a + a') ⊝ (b + b')
                                        ; (i = i1) (j = i1) → (succ a + succ a') ⊝ (succ b + succ b')
                                        ; (i = i0) (j = i1) → (a + succ a') ⊝ (b + succ b')
                                        ; (i = i1) (j = i0) → (succ a + a') ⊝ (succ b + b') })
                                       ?
--                                       (cancel (a + a') (b + b') i)
-}
-- Indeed, in Cubical Agda, the type "x ≡ y" can not only (as usual) be read
-- as the type of witnesses that x and y are the same, but it can also be read
-- as the type of paths from x to y.

-- Figure 8:
--     +---+   +---+
--    /     \ /     \
--   +       +       +
--    \     / \     /
--     +---+   +---+
data Figure8 : Set where
  center : Figure8
  loop₁  : center ≡ center
  loop₂  : center ≡ center

-- +---+
-- |###|
-- |###|
-- +---+
data FilledSquare : Set where
  upper-left-corner  : FilledSquare
  lower-right-corner : FilledSquare
  {- with just these constructors, the type looks as follows:
     *   

         *
  -}
  path₁ : upper-left-corner ≡ lower-right-corner
  {- with just these constructors, the type looks as follows:
     *->-+
         v
         *
  -}
  path₂ : upper-left-corner ≡ lower-right-corner
  {- with just these constructors, the type looks as follows:
     *->-+
     v   v
     +->-*
  -}
  filling : path₁ ≡ path₂

-- logical reading: for any set/type X, for any element x : X, it is the case that x equals x.
-- computational reading: "refl" is a function which inputs a set/type X and an element x : X, and outputs a witness that x equals x.
-- homotopical reading: for any space X, for any point x : X, there is a path from x to x.
{-
refl : (X : Set) (x : X) → x ≡ x
refl X x = λ i → x
-}
symm : (X : Set) (x y : X) → x ≡ y → y ≡ x
symm X x y p = λ i → p (~ i)   -- in blackboard mathematics: p (1 - i)

-- A path γ in a type X is, internally in Cubical Agda, formalized as a function from I to X, where I is the unit interval.
--
--  * γ 0              * γ 1
--   \                 ^ γ 0.9
--    +---+ γ 0.3      |
--         \           |
--          +-->-->-->-+
--           γ 0.5

{-
open import Padova2024.EquationalReasoning

-- ex and ex' are NOT the same:
lemma : ex ≡ ex' → ⊥
lemma ()
-}

-- How can we define the type of unordered pairs of natural numbers?
-- Then ex and ex' would be the same.

-- Option 1: just reuse the type Pair of ordered pairs, and promise
-- to ourselves that we will never make us of the accidental ordering

-- Option 2: use sorted pairs
data _≤_ : ℕ → ℕ → Set where
  base : {b : ℕ}   → zero ≤ b
  step : {a b : ℕ} → a ≤ b → succ a ≤ succ b

data OrderedPair : Set where
  mk : (a b : ℕ) → a ≤ b → OrderedPair

data _⊎_ (X Y : Set) : Set where
  left  : X → X ⊎ Y
  right : Y → X ⊎ Y

_≤?_ : (a b : ℕ) → (a ≤ b) ⊎ (b ≤ a)
zero ≤? zero = left base
zero ≤? succ y = left base
succ x ≤? zero = right base
succ x ≤? succ y with x ≤? y
... | left x≤y = left (step x≤y)
... | right y≤x = right (step y≤x)

-- a "smart constructor"
mk' : ℕ → ℕ → OrderedPair
mk' a b with a ≤? b
... | left  a≤b = mk a b a≤b
... | right b≤a = mk b a b≤a

{-
_ : mk' one two ≡ mk' two one
_ = refl
-}

-- Option 3: setoid hell
data _×_ (X Y : Set) : Set where
  _,_ : X → Y → X × Y

{-
_≈_ : Pair → Pair → Set
mk a b ≈ mk a' b' = ((a ≡ a') × (b ≡ b')) ⊎ ((a ≡ b') × (b ≡ a'))

_ : ex ≈ ex'
_ = right (refl , refl)
-}

-- A setoid is a type together with a custom equivalence relation on it
-- (like Pair together with _≈_). We then promise that we never use _≡_
-- on elements of type Pair, but instead only ever _≈_.

sum : Pair → ℕ
sum (mk a b) = a + b

-- additional proof obligation (coming from the promise, not enforced by Agda):
{-
lemma-sum-invariant : (z z' : Pair) → z ≈ z' → sum z ≡ sum z'
lemma-sum-invariant = {!!}

twice-sum : Pair → ℕ
twice-sum z = sum z + sum z

lemma-twice-sum-invariant : (z z' : Pair) → z ≈ z' → twice-sum z ≡ twice-sum z'
lemma-twice-sum-invariant = {!!}
-}

-- How can we define the type of unordered lists of natural numbers? ("multisets")

-- How can we define the type ℤmod4 of "integers modulo 4"
-- (where 0 ≡ 4, 1 ≡ 5, 2 ≡ 6, ...)?


{- more generally:
data Pair (X : Set) : Set where
  mk : X → X → Pair

ex : Pair ℕ
ex = mk one two
-}
