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
false || b = b
true  || b = true

-- EXERCISE: Implement a function "is-tautology₁?" which checks whether
-- a given input function is constantly true. For instance, if f x = x,
-- then "is-tautology₁ f" should evaluate to "false".
is-tautology₁ : (Bool → Bool) → Bool
is-tautology₁ f = f false && f true

-- EXERCISE: Implement a function "is-tautology₂?" which checks whether
-- a given input function of two arguments is constantly true. For
-- instance, if f x y = true, then "is-tautology₂ f" should evaluate to "true".
is-tautology₂ : (Bool → Bool → Bool) → Bool
-- is-tautology₂ f =
--   f false false && (f false true && (f true false && f true true))
is-tautology₂ f = is-tautology₁ (f false) && is-tautology₁ (f true)


---------------------------
----[ NATURAL NUMBERS ]----
---------------------------

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero   + b = b
succ a + b = succ (a + b)
-- Informally:
-- succ a + b = (1+a) + b = 1 + a + b = 1+(a+b) = succ (a + b)

data ListOfNats : Set where
  []  : ListOfNats
  _∷_ : ℕ → ListOfNats → ListOfNats

exampleList : ListOfNats
exampleList = zero ∷ (succ (succ zero) ∷ (succ zero ∷ []))  -- \:: "cons"
-- Haskell notation: [zero, succ (succ zero), succ zero]

data ListOfBooleans : Set where
  []  : ListOfBooleans
  _∷_ : Bool → ListOfBooleans → ListOfBooleans


-- The following type introduces, for each type "X", a new type "List X".
data List (X : Set) : Set where
  []  : List X
  _∷_ : X → List X → List X

exampleListOfBooleans : List Bool
exampleListOfBooleans = false ∷ (true ∷ (false ∷ (false ∷ [])))

exampleListOfLists : List (List Bool)
exampleListOfLists = exampleListOfBooleans ∷ (exampleListOfBooleans ∷ [])

-- EXERCISE: Define the function "half" which divides its input by two.
-- For instance "half (succ (succ (succ (succ zero))))" should be "succ (succ zero)"
-- and "half (succ (succ (succ zero)))" should be "succ zero" (so we round down).
half : ℕ → ℕ
half zero = zero
half (succ zero) = zero
half (succ (succ n)) = succ (half n)

-- EXERCISE: Define (cut-off) subtraction. For instance "succ zero - succ zero"
-- and "succ zero - succ (succ zero)" should both be "zero".
_-_ : ℕ → ℕ → ℕ
zero - b = zero
succ a - zero = succ a
succ a - succ b = a - b

-- EXERCISE: Define multiplication and exponentiation.
_×_ : ℕ → ℕ → ℕ
zero × n = zero
succ m × n = n + (m × n)

_^_ : ℕ → ℕ → ℕ
zero ^ zero = succ zero
zero ^ _ = zero
_ ^ zero = succ zero
m ^ succ n = m × (m ^ n)

-- EXERCISE: Define a function "eq?" which determines whether its two
-- input numbers are equal. For instance, "eq? zero zero" should evaluate
-- to "true" while "eq? zero (succ zero)" should evaluate to "false".
eq? : ℕ → ℕ → Bool
eq? zero zero = true
eq? zero (succ _) = false
eq? (succ _) zero = false
eq? (succ a) (succ b) = eq? a b

-- EXERCISE: Define a function "≤?" which determines whether its first
-- argument is less than or equal to its second. For instance, "≤?
-- zero zero" should evaluate to "true" while "≤? (succ zero) zero"
-- should evaluate to "false".
≤? : ℕ → ℕ → Bool
≤? zero zero = true
≤? zero (succ _) = true
≤? (succ _) zero = false
≤? (succ a) (succ b) = ≤? a b

-- EXERCISE: Define a function "even?" which determines whether its input is even.
-- For instance, "even? zero" and "even? (succ (succ zero))" should both evaluate to "true",
-- while "even? (succ zero)" should evaluate to "false".
even? : ℕ → Bool
even? zero = true
even? (succ zero) = false
even? (succ (succ n)) = even? n

-- EXERCISE: Describe the following type in simple terms. What are its values?
-- This type is empty. It does not have any inhabitants.
-- The constructor "foo" is not applicable, because we can only
-- use it in case we already have a value of type "Weird" at hand,
-- which we don't.
data Weird : Set where
  foo : Weird → Weird

data Empty : Set where
-- This type is manifestly empty.

-- The following hole can NOT be filled:
f : ℕ → Empty
f n = {!!}

g : Empty → Empty
g x = x
-- There is a function from X to Empty only in the case that
-- X itself is an empty type.

h : Weird → Empty
h (foo x) = h x

{-
data Lol : Set where
  bar : {!(Empty → Lol) → Lol!}
-}

data Bar : Set where
  hello : Empty → Bar
