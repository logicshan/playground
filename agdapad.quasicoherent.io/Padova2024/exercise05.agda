{-# OPTIONS --allow-unsolved-metas #-}
{-
  AGDA IN PADOVA 2024
  Exercise sheet 5

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
  and then entering the path to this file: ~/Padova2024/exercise05.agda.
  As this file is read-only, you can then save a copy of this file to your personal
  directory and edit that one: File > Save As... For instance, you can save this file
  as ~/solutions05.agda.
-}

open import Padova2024.EquationalReasoning

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

data ⊥ : Set where

half : ℕ → ℕ
half zero            = zero
half (succ zero)     = zero
half (succ (succ n)) = succ (half n)


-- ──────────────────────────────────────────────────────
-- ────[ PROPERTIES OF THE ORDERING OF THE NATURALS ]────
-- ──────────────────────────────────────────────────────

data _<_ : ℕ → ℕ → Set where
  base : {n : ℕ}   → n < succ n
  step : {a b : ℕ} → a < b      → a < succ b

-- EXERCISE: Verify that the successor operation is monotonic.
lemma-succ-monotonic : {a b : ℕ} → a < b → succ a < succ b
lemma-succ-monotonic p = {!!}

-- EXERCISE: Verify that half of a number is (almost) always smaller than the number.
lemma-half< : (a : ℕ) → half (succ a) < succ a
lemma-half< a = {!!}

-- EXERCISE: Verify that the following alternative definition of the less-than relation is equivalent to _<_.
data _<'_ : ℕ → ℕ → Set where
  base : {n : ℕ}   → zero <' succ n
  step : {a b : ℕ} → a <' b → succ a <' succ b

<→<' : {a b : ℕ} → a < b → a <' b
<→<' = {!!}

<'→< : {a b : ℕ} → a < b → a <' b
<'→< = {!!}


-- ────────────────────────────────────────────────────────
-- ────[ INTERLUDE: BINARY REPRESENTATIONS OF NUMBERS ]────
-- ────────────────────────────────────────────────────────

data Bin : Set where
  [] : Bin
  _O : Bin → Bin
  _I : Bin → Bin
-- For instance: The number 6 (binary 110) is encoded as [] I I O.
-- This is a shorthand for _O (_I (_I [])).

double : ℕ → ℕ
double zero = zero
double (succ n) = succ (succ (double n))

-- EXERCISE: Implement the successor operation on binary representations.
-- For instance, succ' ([] I I O) should be [] I I I.
succ' : Bin → Bin
succ' = {!!}

-- EXERCISE: Implement the following function. It should be left inverse to the
-- "encode" function below.
decode : Bin → ℕ
decode = {!!}

encode : ℕ → Bin
encode zero     = []
encode (succ n) = succ' (encode n)

-- EXERCISE: Show that "succ'" is on binary representations what "succ" is on natural numbers.
-- Hint: You will need to use the "cong" function.
lemma-succ-succ' : (xs : Bin) → decode (succ' xs) ≡ succ (decode xs)
lemma-succ-succ' xs = {!!}

-- EXERCISE: Show that "decode" and "encode" are [one-sided] inverses of each other.
lemma-decode-encode : (n : ℕ) → decode (encode n) ≡ n
lemma-decode-encode n = {!!}

-- EXERCISE: Implement binary addition and verify that it works correctly by comparing
-- to the standard addition on natural numbers.


-- ────────────────────────────────────────
-- ────[ USING NATURAL NUMBERS AS GAS ]────
-- ────────────────────────────────────────

module NaiveGas where
  go : ℕ → ℕ → ℕ
  go zero     gas        = zero
  go (succ n) zero       = zero   -- bailout case
  go (succ n) (succ gas) = succ (go (half (succ n)) gas)

  digits : ℕ → ℕ
  digits n = go n n

  -- EXERCISE: Verify this basic statement, certifying that the function meets its contract.
  -- (Not easy, you will need auxiliary lemmas!)
  lemma-digits : (n : ℕ) → digits (succ n) ≡ succ (digits (half (succ n)))
  lemma-digits n = {!!}


-- ───────────────────────────────────────────────────────
-- ────[ WELL_FOUNDED RECURSION WITH NATURAL NUMBERS ]────
-- ───────────────────────────────────────────────────────

module WfNat where
  data Acc : ℕ → Set where
    acc : {x : ℕ} → ((y : ℕ) → y < x → Acc y) → Acc x

  -- EXERCISE: Show that every natural number is accessible.
  theorem-ℕ-well-founded : (n : ℕ) → Acc n
  theorem-ℕ-well-founded n = {!!}

  go : (n : ℕ) → Acc n → ℕ
  go zero     gas     = zero
  go (succ n) (acc f) = succ (go (half (succ n)) (f (half (succ n)) (lemma-half< n)))

  digits : ℕ → ℕ
  digits n = go n (theorem-ℕ-well-founded n)

  -- EXERCISE: Verify this fundamental observation. Not easy!
  lemma-digits : (n : ℕ) → digits (succ n) ≡ succ (digits (half (succ n)))
  lemma-digits n = {!!}

  data G : ℕ → ℕ → Set where
    -- cf. naive definition: "digits zero = zero"
    base : G zero zero

    -- cf. naive definition: "digits (succ n) = succ (digits (half (succ n)))"
    step : {n y : ℕ} → G (half (succ n)) y → G (succ n) (succ y)

  -- EXERCISE: For a change, this is not too hard.
  lemma-G-is-functional : {a b b' : ℕ} → G a b → G a b' → b ≡ b'
  lemma-G-is-functional p q = {!!}

  data Σ (X : Set) (Y : X → Set) : Set where
    _,_ : (x : X) → Y x → Σ X Y

  -- EXERCISE: Fill this in. You will need lemma-digits and more; not easy.
  lemma-G-is-computed-by-digits : (a : ℕ) → G a (digits a)
  lemma-G-is-computed-by-digits = {!!}


-- ─────────────────────────────────────────────
-- ────[ WELL_FOUNDED RECURSION IN GENERAL ]────
-- ─────────────────────────────────────────────

module WfGen (X : Set) (_<_ : X → X → Set) where
  data Acc : X → Set where
    acc : {x : X} → ((y : X) → y < x → Acc y) → Acc x

  invert : {x : X} → Acc x → ((y : X) → y < x → Acc y)
  invert (acc f) = f

  -- EXERCISE: Show that well-founded relations are irreflexive. More
  -- precisely, verify the following local version of this statement:
  lemma-wf-irreflexive : {x : X} → Acc x → x < x → ⊥
  lemma-wf-irreflexive = {!!}

  -- EXERCISE: Show that there are no infinite descending sequences.
  lemma-no-descending-sequences : (α : ℕ → X) → ((n : ℕ) → α (succ n) < α n) → Acc (α zero) → ⊥
  lemma-no-descending-sequences = {!!}

  module _ {A : X → Set} (step : (x : X) → ((y : X) → y < x → A y) → A x) where
    -- This is a very general "go" function like for the particular "digits" example above.
    -- The goal of this development is to define the function "f"
    -- below and verify its recursion property.
    go : (x : X) → Acc x → A x
    go x (acc f) = step x (λ y p → go y (f y p))

    -- EXERCISE: Show that, assuming that the recursion template "step"
    -- doesn't care about the witnesss of accessibility, so does the
    -- "go" function. The extra assumption is required since in
    -- standard Agda we cannot verify that witnesses of accessibility
    -- are unique.
    module _ (extensional : (x : X) (u v : (y : X) → y < x → A y) → ((y : X) (p : y < x) → u y p ≡ v y p) → step x u ≡ step x v) where
      lemma : (x : X) (p q : Acc x) → go x p ≡ go x q
      lemma = {!!}

      -- EXERCISE: Assuming that X is well-founded, we can define the
      -- function "f" below. Verify that this satisfies the desired
      -- recursion equation.
      module _ (wf : (x : X) → Acc x) where
        f : (x : X) → A x
        f x = go x (wf x)

        theorem : (x : X) → f x ≡ step x (λ y p → f y)
        theorem = {!!}
