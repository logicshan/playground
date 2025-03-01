{-# OPTIONS --cubical --allow-unsolved-metas #-}

open import Cubical.Core.Primitives

{-
  ROSETTA STONE for TRANSLATING between THREE SUBJECTS:
  1. logic
  2. computer science
  3. homotopy theory (dealing with shapes)

  x ≡ y    1. "the values x and y are the same"
           2. "the type of witnesses that x and y are the same"
           3. "the space of paths from x to y"

  x ≡ y → y ≡ x
           1. "if x is the same as y, then also y is the same as x"
           2. "there is a function transforming witnesses that x ≡ y
               into witnesses that y ≡ x"
           3. ???

  ⊥        1. "contradiction"
           2. "the empty type"
           3. "the empty space"

  In Cubical Agda, we picture types to be spaces.
  Every value of a type is then pictured as a point of the associated space.

  Here is a picture of the space associated to ℕ:
    0   1   2   3   4   5   ...
  In this space, there is no path between 0 and 1.

  Here is a picture of another space:
    +----+
    |####|
    |####|
    +----+
  In this space, there is a path from every point to every other point.

  Here is a picture of yet another space:
    A----B     C
    |####|    /#\
    |####|   +---+
    +----+
  In this space, there is a path from A to B, but
  there is no path from A to C.

  In logic, if a ≡ b and b ≡ c, then we may conclude that a ≡ c.
  In homotopy theory, if we have a path from a to b and
  if we have a path from b to c, then we may concatenate those
  two paths to obtain a path from a to c.
-}

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero   + b = b
succ a + b = succ (a + b)

-- "Pair X" is the type of (ordered) pairs of values of X.
data Pair (X : Set) : Set where
  mk : X → X → Pair X

first : {X : Set} → Pair X → X
first (mk a b) = a
 
-- "UnorderedPair X" is the type of unordered pairs of values of X.
data UnorderedPair (X : Set) : Set where
  mk : X → X → UnorderedPair X
  swap : (a b : X) → mk a b ≡ mk b a

first' : {X : Set} → UnorderedPair X → X
first' (mk a b)     = a
first' (swap a b i) = {!!}
-- We are happy that this hole cannot be filled in.

sum' : UnorderedPair ℕ → ℕ
sum' (mk a b)     = a + b
sum' (swap a b i) = {!!}
-- We are happy that this hole can be filled in.

-- In Cubical Agda, there can be more witnesses of equality than
-- just provided by "refl". For instance, "swap" provides additional
-- witnesses.

-- Let's define the type of numbers modulo 4:
-- -4=0, -3=1, -2=2, -1=3, 0, 1, 2, 3, 4=0, 5=1, 6=2, 7=3, 8=4, ...

data ℤmod4 : Set where
  zer : ℤmod4
  suc : ℤmod4 → ℤmod4
  wrap : (x : ℤmod4) → x ≡ suc (suc (suc (suc x)))

data ℤmod4' : Set where
  zer'  : ℤmod4'
  suc'  : ℤmod4' → ℤmod4'
  wrap' : zer' ≡ suc' (suc' (suc' (suc' zer')))
-- Here is a picture of ℤmod4':
--             +----------------+
--             |                |
--   0    1    2    3   4   5   6   7   8   9   10  ...
--   |    |             |   |
--   +------------------+   |
--        |                 |
--        +-----------------+

data S¹ : Set where
  base : S¹
  loop : base ≡ base
-- Here is a picture of the circle (just the boundary, not filled in):
--            *
--           / \
--           \_A

base' : S¹ 
base' = loop i1
-- If p is any path in Cubical Agda, then p i0 is its beginning
-- and p i1 is its end. And "p i0.5" would be its midpoint.
-- And "p i0.25" would be its first-quarter-point.

refl : {X : Set} {x : X} → x ≡ x
refl {X} {x} i = x
-- refl {X} {x} = λ i → x

symm : {X : Set} {a b : X} → a ≡ b → b ≡ a
symm {X} {a} {b} p i = p (~ i)
-- symm {X} {a} {b} p = λ i → p (~ i)

cong : {X Y : Set} {a b : X} → (f : X → Y) → a ≡ b → f a ≡ f b
cong = {!!}

-- The following principle is called "function extensionality".
-- It is often expected by blackboard mathematicians.
-- It is available (by a one-line proof) in Cubical Agda.
-- It is not available in standard Agda.
funext : {X Y : Set} {f g : X → Y} → ((x : X) → f x ≡ g x) → f ≡ g
funext = {!!}

-- How many paths are there from base to base?
-- How many values does the same "base ≡ base" have?
-- refl, loop, loop · loop, loop · loop · loop, ...,
-- symm loop, symm loop · symm loop, ...

-- We will also have the path loop · refl · loop,
-- however this path will be the SAME as loop · loop.

-- The path loop · symm loop will be the SAME as refl.

data Interval : Set where
  left  : Interval
  right : Interval
  seg   : left ≡ right
-- Here is a picture of the interval:
--       +--------+

-- Here is a picture of yet another space:
data Foo : Set where
  left  : Foo
  right : Foo
  seg₁  : left ≡ right
  seg₂  : left ≡ right
--         +----+
--        /      \
--       +        +
--        \      /
--         +----+

-- +---+
-- |###|
-- |###|
-- +---+
data FilledSquare : Set where
  upper-left-corner : FilledSquare
  lower-right-corner : FilledSquare
  path₁ : upper-left-corner ≡ lower-right-corner
  path₂ : upper-left-corner ≡ lower-right-corner
  body : path₁ ≡ path₂

toℕ : ℤmod4' → ℕ
toℕ zer'      = zero
toℕ (suc' x)  = succ (toℕ x)
toℕ (wrap' i) = {!!}                  -- cong toℕ wrap' i

-- Note: toℕ (suc' zer') will be succ zero.
--       toℕ (suc' (suc' (suc' (suc' (suc' zer'))))) will be 5.
--       And (suc' zer') is the same as (suc' (suc' (suc' (suc' (suc' zer'))))).
--       So, by congruence, also 1 should be the same as 5 in ℕ.

_ : suc zer ≡ suc (suc (suc (suc (suc zer))))
_ = wrap (suc zer)

_ : suc' zer' ≡ suc' (suc' (suc' (suc' (suc' zer'))))
_ = {!cong suc' wrap'!}

example : UnorderedPair ℕ
example = mk (succ zero) (succ (succ zero))

example' : UnorderedPair ℕ
example' = mk (succ (succ zero)) (succ zero)

dream : example ≡ example'
dream = swap (succ zero) (succ (succ zero))


-- How can we define the type of unordered pairs of values of X?
-- One answer: Use sorted ordered pairs to represent
-- unordered pairs. For instance, the unordered pair
-- of the numbers 20 and 5 would be represented by
-- (5 , 20). The unordered pair of the numbers 5 and 20
-- would be the SAME unordered pair and it would be
-- represented by the same ordered pair (5 , 20).

-- This is a good approach, HOWEVER it requires some
-- ordering on X.

-- Second answer: Just promise to never use ≡.
-- Instead only use a custom-tailored approximate
-- equality ≈.
_≈_ : {X : Set} → Pair X → Pair X → Set
(mk a b) ≈ (mk a' b') = {!(a ≡ a' × b ≡ b') ⊎ (a ≡ b' × b ≡ a')!}

-- This is called the "setoid hell".

