{-# OPTIONS --allow-unsolved-metas #-}
-- AGDA IN PADOVA 2023
-- Exercise sheet 1


--------------------
----[ BOOLEANS ]----
--------------------

data Bool : Set where
  false : Bool
  true  : Bool

_&&_ : Bool → Bool → Bool
false && b     = false
true  && false = false
true  && true  = true

-- EXERCISE: Implement boolean "or".
-- "false || true" should evaluate to "true".
-- "true  || true" should evaluate to "true".
_||_ : Bool → Bool → Bool
a || b = {!!}

-- EXERCISE: Implement a function "is-tautology₁?" which checks whether
-- a given input function is constantly true. For instance, if f x = x,
-- then "is-tautology₁ f" should evaluate to "false".
is-tautology₁ : (Bool → Bool) → Bool
is-tautology₁ f = {!!}

-- EXERCISE: Implement a function "is-tautology₂?" which checks whether
-- a given input function of two arguments is constantly true. For
-- instance, if f x y = true, then "is-tautology₂ f" should evaluate to "true".
is-tautology₂ : (Bool → Bool → Bool) → Bool
is-tautology₂ f = {!!}


---------------------------
----[ NATURAL NUMBERS ]----
---------------------------

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero   + b = b
succ a + b = succ (a + b)

-- EXERCISE: Define the function "half" which divides its input by two.
-- For instance "half (succ (succ (succ (succ zero))))" should be "succ (succ zero)"
-- and "half (succ (succ (succ zero)))" should be "succ zero" (so we round down).
half : ℕ → ℕ
half n = {!!}

-- EXERCISE: Define (cut-off) subtraction. For instance "succ zero - succ zero"
-- and "succ zero - succ (succ zero)" should both be "zero".
_-_ : ℕ → ℕ → ℕ
a - b = {!!}

-- EXERCISE: Define multiplication and exponentiation.

-- EXERCISE: Define a function "eq?" which determines whether its two
-- input numbers are equal. For instance, "eq? zero zero" should evaluate
-- to "true" while "eq? zero (succ zero)" should evaluate to "false".
eq? : ℕ → ℕ → Bool
eq? a b = {!!}

-- EXERCISE: Define a function "≤?" which determines whether its first
-- argument is less than or equal to its second. For instance, "≤?
-- zero zero" should evaluate to "true" while "≤? (succ zero) zero"
-- should evaluate to "false".
≤? : ℕ → ℕ → Bool
≤? a b = {!!}

-- EXERCISE: Define a function "even?" which determines whether its input is even.
-- For instance, "even? zero" and "even? (succ (succ zero))" should both evaluate to "true",
-- while "even? (succ zero)" should evaluate to "false".
even? : ℕ → Bool
even? n = {!!}

-- EXERCISE: Describe the following type in simple terms. What are its values?
data Weird : Set where
  foo : Weird → Weird
