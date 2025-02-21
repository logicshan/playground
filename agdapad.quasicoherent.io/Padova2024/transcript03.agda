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
a || b = {!!}

-- EXERCISE: Implement a function "is-tautology₁?" which checks whether
-- a given input function is constantly true. For instance, if f x = x,
-- then "is-tautology₁? f" should evaluate to "false".
is-tautology₁? : (Bool → Bool) → Bool
is-tautology₁? f = f false && f true

-- EXERCISE: Implement a function "is-tautology₂?" which checks whether
-- a given input function of two arguments is constantly true. For
-- instance, if f x y = true, then "is-tautology₂ f" should evaluate to "true".
is-tautology₂ : (Bool → Bool → Bool) → Bool
is-tautology₂ f = {!!}


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
half zero            = zero
half (succ zero)     = zero
half (succ (succ n)) = succ (half n)

-- EXERCISE: Define (cut-off) subtraction. For instance "succ zero - succ zero"
-- and "succ zero - succ (succ zero)" should both be "zero".
_-_ : ℕ → ℕ → ℕ
a - b = {!!}

-- EXERCISE: Define multiplication and exponentiation.

-- EXERCISE: Define a function "max" which returns the maximum of two inputs.
-- For instance "max (succ zero) zero" should be "succ zero".

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

{-
-- EXERCISE: Define a function "even?" which determines whether its input is even.
-- For instance, "even? zero" and "even? (succ (succ zero))" should both evaluate to "true",
-- while "even? (succ zero)" should evaluate to "false".
even? : ℕ → Bool
even? n = {!!}
-}

-- EXERCISE: Define a function "odd?" which determines whether its input is odd.
-- You may use the "even?" function from before.
odd? : ℕ → Bool
odd? n = {!!}


-- ─────────────────
-- ────[ TYPES ]────
-- ─────────────────

-- EXERCISE: Describe the following type in simple terms. What are its values?
data Weird : Set where
  foo : Weird → Weird
-- This type doesn't have any inhabitants at all, because the only
-- constructor, "foo", is not useful.

ex : Weird
ex = foo (foo (foo (foo (foo {!!}))))

{-
loop : Weird
loop = foo loop
-}

id : Weird → Weird
id x = x

-- EXERCISE: Define a manifestly empty type called "Empty".
data Empty : Set where
-- No constructors, so no ways to construct inhabitants of type "Empty",
-- so the type "Empty" does not contain any inhabitants.

-- Can you define a function Empty → ℕ?

from-empty : Empty → ℕ
from-empty x = zero

from-empty' : Empty → ℕ
from-empty' x = succ (succ zero)

from-empty'' : Empty → ℕ
from-empty'' ()

-- Can you define a function in the other direction, so ℕ → Empty?

to-empty : ℕ → Empty
to-empty x = {!!}  -- this hole cannot be filled

to-empty' : ℕ → Empty
to-empty' zero     = {!()!}
to-empty' (succ x) = {!()!}

unicorn : Empty → Empty
unicorn x = x

{-
  To summarize: There is a function of type X → Empty only in the case that X doesn't
  contain any inhabitants.
-}

riddle : Weird → Empty
riddle (foo x) = riddle x

-- EXERCISE: Write a function "Endo" which takes as input a type X and returns
-- as output the type of functions X → X.
Endo : Set → Set
Endo X = X → X

Bar : Set → Set
Bar X = ℕ

Baz : ℕ → Set
Baz zero            = Bool
Baz (succ zero)     = ℕ
Baz (succ (succ n)) = Bool → ℕ

grtz : Baz (succ zero)
grtz = succ (succ (succ (succ (succ zero))))


-- ─────────────────────────────────────────────
-- ────[ FIRST PROOFS WITH NATURAL NUMBERS ]────
-- ─────────────────────────────────────────────

-- The following function determines whether a given number is zero.
is-zero? : ℕ → Bool
is-zero? zero     = true
is-zero? (succ n) = false

-- For every natural number "n", there should be a type "IsZero n"
-- of witnesses that "n" is zero. For instance, the type "IsZero (succ zero)"
-- should be empty, because there shouldn't be any witnesses that "succ zero"
-- is zero. But the type "IsZero zero" should be inhabited.
data IsZero : ℕ → Set where
  case-zero : IsZero zero
-- In contrast, the function IsZero : ℕ → Set does not carry out any (nontrivial) computation.
-- Instead, the function IsZero reads a number "n" as input and outputs the type
-- of witnesses that "n" is zero. For most inputs, the resulting output types will be empty.
-- For instance, the type "IsZero (succ zero)" will be empty.

-- For every number "n", the type "IsNonzero n" is the type of witnesses that "n" is nonzero.
data IsNonzero : ℕ → Set where
  case-succ : {n : ℕ} → IsNonzero (succ n)

data ⊥ : Set where

IsNonzero' : ℕ → Set
IsNonzero' n = IsZero n → ⊥
-- logical reading: a number "n" is nonzero if and only if the assumption that it would be zero
-- implies a contradiction.
-- computational reading: a witness of a number "n" being nonzero is a function which
-- reads a witness that "n" is zero as input and outputs a witness of a contradiction.

-- Proposition: The number zero is zero.
proposition : IsZero zero
proposition = case-zero

-- Theorem: If a number "n" is zero, then it is zero.
-- Logical reading: For every number n, if n is zero, then n is zero.
-- Type-theoretic reading: "first-theorem" is a function which reads two inputs,
-- namely a number "n" and a witness that "n" is zero, and outputs a witness that "n" is zero.
first-theorem : (n : ℕ) → IsZero n → IsZero n
first-theorem n p = {!!}

-- EXERCISE: Prove that the sum of two numbers, both of which are zero, is zero again.
-- Computational reading: "sum-zero" is a function which reads as input
-- (1) a natural number "x",
-- (2) a natural number "y",
-- (3) a witness that "x" is zero, and
-- (4) a witness that "y" is zero,
-- and produces as output a witness that "x + y" is zero.
sum-zero : (x : ℕ) → (y : ℕ) → IsZero x → IsZero y → IsZero (x + y)
sum-zero zero zero case-zero case-zero = case-zero
-- sum-zero zero zero case-zero case-zero = proposition
-- sum-zero zero y case-zero q = q

-- EXERCISE: State and prove: The sum of two numbers, the first of which is nonzero, is nonzero.
-- Computational reading: "sum-nonzero" is a function which reads as input
-- (1) a natural number "x",
-- (2) a natural number "y",
-- (3) a witness that "x" is nonzero, and
-- produces as output a witness that "x + y" is nonzero.
sum-nonzero : {x y : ℕ} → IsNonzero x → IsNonzero (x + y)
sum-nonzero case-succ = case-succ

-- EXERCISE: Prove that the (contradictory) assumption that zero is nonzero implies
-- the (also contradictory) statement that succ zero is zero.
zero-is-not-nonzero : IsNonzero zero → IsZero (succ zero)
zero-is-not-nonzero ()

-- computational reading: "absurd" is a function which reads as input a type "A"
-- and a witness of a contradiction and outputs a value of type "A".
-- logical reading: For every A, if contradiction, then A.
absurd : {A : Set} → ⊥ → A
absurd {A} ()

if-isnonzero-zero-then-bot : IsNonzero zero → ⊥
if-isnonzero-zero-then-bot ()

zero-is-not-nonzero' : IsNonzero zero → IsZero (succ zero)
zero-is-not-nonzero' p = absurd (if-isnonzero-zero-then-bot p)

-- For every number "n", the type "Even n" should be the type of witnesses that "n" is even.
data Even : ℕ → Set where
  base : Even zero
  step : {n : ℕ} → Even n → Even (succ (succ n))
  -- logical reading: For every number n, if n is even, then succ (succ n) is even.
  -- computational reading: "step" is a function which reads a number "n" and a witness that "n" is even
  -- as input and outputs a new, freshly-minted witness that "succ (succ n)" is even.

four-is-even : Even (succ (succ (succ (succ zero))))
four-is-even = step {succ (succ zero)} (step {zero} base)
-- four-is-even = step (step base)

even? : ℕ → Bool
even? zero            = true
even? (succ zero)     = false
even? (succ (succ n)) = even? n

!_ : Bool → Bool
! false = true
! true  = false

even?' : ℕ → Bool
even?' zero     = true
even?' (succ n) = ! (even?' n)

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A → Maybe A
-- For every type "A", there is a new type "Maybe A".
-- Its inhabitants are:
-- (1) "nothing"
-- (2) for every value "x" of type "A", we have the inhabitant "just x"

_/_ : ℕ → ℕ → Maybe ℕ
x / zero   = nothing
x / succ y = {!!}

even?'' : (n : ℕ) → Maybe (Even n)
even?'' zero            = just base
even?'' (succ zero)     = nothing
even?'' (succ (succ n)) with even?'' n
... | nothing   = nothing
... | just    p = just (step p)

-- EXERCISE: Show that the sum of even numbers is even.
lemma-sum-even : {a b : ℕ} → Even a → Even b → Even (a + b)
lemma-sum-even base     q = q
lemma-sum-even (step p) q = step (lemma-sum-even p q)

{-
lemma-+-zero : (a : ℕ) → (a + zero) ≡ a
lemma-+-zero a = ?
-}

lemma-sum-even' : {a b : ℕ} → Even a → Even b → Even (a + b)
lemma-sum-even' p base     = {!p!}
lemma-sum-even' p (step q) = {!!}
