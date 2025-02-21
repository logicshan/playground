{-# OPTIONS --allow-unsolved-metas #-}
-- {-# OPTIONS --safe #-}
-- In classical mathematics, we have:
-- Every statement A is either true or not true.

data _⊎_ (X Y : Set) : Set where
  left  : X → X ⊎ Y
  right : Y → X ⊎ Y

data ⊥ : Set where

postulate
  law-of-excluded-middle : {A : Set} → A ⊎ (A → ⊥)
  -- law-of-excluded-middle = {!!}

  contradiction : ⊥

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

data _≡_ {X : Set} : X → X → Set where
  refl : {x : X} → x ≡ x

-- Logical reading: "From a contradiction, everything follows."
-- Computational reading: "principle-of-explosion is a function
-- which reads as input a hypothetical value of ⊥ and outputs
-- a value of type A."
principle-of-explosion : {A : Set} → ⊥ → A
principle-of-explosion ()

theorem : zero ≡ succ zero
theorem = principle-of-explosion contradiction

module Foo
  (law-of-double-negation-elimination : {A : Set} → ((A → ⊥) → ⊥) → A) where
                                                  -- ^^^^^^^^^^^^
                                                  --  not not A
  lemma : zero ≡ zero
  lemma = {!!}

-- Let A be the statement: "There is a position x where the keys
-- to my apartment are." Constructively, if we do not know where
-- the keys are, we cannot defend the statement A. However,
-- as the keys couldn't simply vanish, the we can constructively
-- defend ¬¬A.

-- law-of-excluded-middle (...4....)

-- In constructive mathematics, the law of excluded middle
-- is not generally available; only in special cases.
-- Because Agda is a constructive system, there is no
-- way to fill in this hole.


-- Plan for today:
-- 1. About the exam
-- 2. Termination and wellfounded recursion :-)

-- Mode 1: Focus on Milly's type theory part, just a small Agda exercise.
-- Agda part: very short, 10 to 25 minutes

-- First question: "Please define the type of natural numbers."
{-
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ
-}

-- Second question: "Please define addition."
_+_ : ℕ → ℕ → ℕ
zero   + b = b
succ a + b = succ (a + b)

-- Third question: "Fill in the following hole."
lemma : (x : ℕ) → (zero + x) ≡ x
lemma x = {!!}


-- Second option: Small type theory exercises, then an Agda project.
-- Requirements:
-- 1. it takes a couple of afternoons
-- 2. it's interesting to you
-- 3. it contains at least one proof

{-
  Possible examples for projects:

  - detailed solutions to interesting exercises,
    for instance regarding ordinals

  - implement some algorithm and verify its correctness
    (merge sort, some other sorting algorithm, Euclidean algorithm,
    ...)

  - formalize some piece of mathematics/compsci/physics

  - who wins at Tic Tac Toe?

  - Graham's Number
     + * ^ ↑↑ ↑↑↑ ↑↑↑↑

    4 * 2 = 2 + 2 + 2 + 2
    2 ^ 4 = 2 * 2 * 2 * 2
    2 ↑↑ 4 = 2 ^ (2 ^ (2 ^ 2))
    2 ↑↑↑ 4 = 2 ↑↑ (2 ↑↑ (2 ↑↑ 2))

    G₁ = 3 ↑↑↑↑ 3

    G₂ = 3 ↑↑↑...↑↑↑ 3
           ^^^^^^^^^
            G₁ many

    G₃ = 3 ↑↑↑...↑↑↑ 3
           ^^^^^^^^^
            G₂ many

    ...

    G₆₄ = Graham's number.
    The last digit of Graham's number is a 7.
-}


half : ℕ → ℕ
half zero            = zero
half (succ zero)     = zero
half (succ (succ n)) = succ (half n)

example : half (succ (succ (succ zero))) ≡ succ zero
example = refl

-- "digits n" should be the number of binary digits of the number "n".
-- For instance: Recall that the number 5 is written in binary as 101.
-- So "digits 5" should be "3". "number 7" should also be "3".
-- "digits 8" should be "4". The number 8 can be written in binary
-- as 00000000001000, but still "digits 8" should be "4".
{-
digits : ℕ → ℕ
digits zero     = zero
digits (succ n) = succ (digits (half (succ n)))
-}
-- Issue: Agda does not realize that this recursion is wellfounded.
-- This function definition does make sense, but Agda doesn't realize
-- that. To be on the safe side, Agda rejects this definition, out of
-- fear that this function might be trapped in an infinite viscious loop.

{-
loop : ℕ → ℕ
loop n = loop (succ n)
-}


module Option-1 where
  {-# TERMINATING #-}
  digits : ℕ → ℕ
  digits zero     = zero
  digits (succ n) = succ (digits (half (succ n)))

  {-# TERMINATING #-}
  loop : ℕ → ℕ
  loop n = loop (succ n)
  -- dangerous!

module Option-2 where
  {-# NON_TERMINATING #-}
  digits : ℕ → ℕ
  digits zero     = zero
  digits (succ n) = succ (digits (half (succ n)))

  -- The following hole can NOT be filled:
  new-lemma : (n : ℕ) → digits (succ n) ≡ succ (digits (half (succ n)))
  new-lemma n = {!!}

module Option-3 where
  -- employ a totally different algorithm

module Option-4 where
  -- employ gas
  digits : ℕ → ℕ
  digits n = go (n + n) n
    where
    go : ℕ → ℕ → ℕ
    go zero       n        = zero  -- bailout!
    go (succ gas) zero     = zero
    go (succ gas) (succ n) = succ (go gas (half (succ n)))
    -- Agda recognizes this definition to be wellfounded,
    -- because in the recursive call on the right-hand side,
    -- the argument "gas" is strictly structurally smaller than
    -- the argument "succ gas" on the left-hand side.

module Option-5 where
  -- use a generalized kind of gas which is not brittle
  -- and not ad hoc, but fundamental to the nature of
  -- natural numbers
