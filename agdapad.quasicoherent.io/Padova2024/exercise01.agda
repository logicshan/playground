{-# OPTIONS --allow-unsolved-metas #-}
{-
  AGDA IN PADOVA 2024
  Exercise sheet 1

  ┌─ SHORTCUTS ───────────────────────┐    ┌─ BACKSLASH CHARACTERS ─┐
  │ C-c C-l   = load file             │    │ \bN    = ℕ             │
  │ C-c C-c   = case split            │    │ \alpha = α             │
  │ C-c C-SPC = check hole            │    │ \to    = →             │
  │ C-c C-,   = see context           │    │ \cdot  = ·             │
  │ C-c C-.   = see context and goal  │    │ \::    = ∷             │
  │ C-c C-d   = display type          │    │ \==    = ≡             │
  │ C-c C-v   = evaluate expression   │    └────────────────────────┘
  │ C-z       = enable Vi keybindings │    Use M-x describe-char to
  │ C-x C-+   = increase font size    │    lookup input method for
  └───────────────────────────────────┘    symbol under cursor.

  You can open this file in an Agdapad session by pressing C-x C-f ("find file")
  and then entering the path to this file: ~/Padova2024/exercise01.agda.
  As this file is read-only, you can then save a copy of this file to your personal
  directory and edit that one: File > Save As... For instance, you can save this file
  as ~/solutions01.agda.
-}


-- ────────────────────
-- ────[ BOOLEANS ]────
-- ────────────────────

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
true || b = true

infixr 10 _&&_
infixr 9  _||_

-- EXERCISE: Implement a function "is-tautology₁?" which checks whether
-- a given input function is constantly true. For instance, if f x = x,
-- then "is-tautology₁ f" should evaluate to "false".
is-tautology₁ : (Bool → Bool) → Bool
is-tautology₁ f = f true && f false

-- EXERCISE: Implement a function "is-tautology₂?" which checks whether
-- a given input function of two arguments is constantly true. For
-- instance, if f x y = true, then "is-tautology₂ f" should evaluate to "true".
is-tautology₂ : (Bool → Bool → Bool) → Bool
is-tautology₂ f = f true true && f true false && f false true && f false false


-- ───────────────────────────────────────
-- ────[ NATURAL NUMBERS PROGRAMMING ]────
-- ───────────────────────────────────────

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

-- EXERCISE: Define a function "max" which returns the maximum of two inputs.
-- For instance "max (succ zero) zero" should be "succ zero".
max : ℕ → ℕ → ℕ
max a b with a - b
... | zero = b
... | succ _ = a

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

-- EXERCISE: Define a function "odd?" which determines whether its input is odd.
-- You may use the "even?" function from before.
odd? : ℕ → Bool
odd? n with even? n
... | false = true
... | true = false


-- ─────────────────
-- ────[ TYPES ]────
-- ─────────────────

-- EXERCISE: Describe the following type in simple terms. What are its values?
data Weird : Set where
  foo : Weird → Weird

-- EXERCISE: Define a manifestly empty type called "Empty".
-- Can you define a function Empty → ℕ?
-- Can you define a function in the other direction, so ℕ → Empty?
data Empty : Set where

_ : Empty → ℕ
_ = λ ()

_ : (ℕ → Empty) → Empty
_ = λ f → f zero


-- EXERCISE: Write a function "Endo" which takes as input a type X and returns
-- as output the type of functions X → X.
Endo : Set → Set
Endo X = X → X


-- ─────────────────────────────────────────────
-- ────[ FIRST PROOFS WITH NATURAL NUMBERS ]────
-- ─────────────────────────────────────────────

data IsZero : ℕ → Set where
  case-zero : IsZero zero

data IsNonzero : ℕ → Set where
  case-succ : (n : ℕ) → IsNonzero (succ n)

-- EXERCISE: Prove that the sum of two numbers, both of which are zero, is zero again.
sum-zero : (x y : ℕ) → IsZero x → IsZero y → IsZero (x + y)
sum-zero zero zero _ _ = case-zero

-- EXERCISE: State and prove: The sum of two numbers, the first of which is nonzero, is nonzero.
sum-nonzero : (x y : ℕ) → IsNonzero x → IsNonzero (x + y)
sum-nonzero _ y (case-succ n) = case-succ (n + y)

-- EXERCISE: Prove that the (contradictory) assumption that zero is nonzero implies
-- the (also contradictory) statement that succ zero is zero.
zero-is-not-nonzero : IsNonzero zero → IsZero (succ zero)
zero-is-not-nonzero ()
