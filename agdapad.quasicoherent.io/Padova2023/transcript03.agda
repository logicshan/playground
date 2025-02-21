{-# OPTIONS --allow-unsolved-metas #-}

data Bool : Set where
  false : Bool
  true  : Bool

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero   + b = b
succ a + b = succ (a + b)

-- For instance, "eq? zero zero" should yield "true".
-- For instance, "eq? zero (succ zero)" should yield "false".
eq? : ℕ → ℕ → Bool
eq? zero     zero     = true
eq? zero     (succ b) = false
eq? (succ a) zero     = false
eq? (succ a) (succ b) with eq? a b
... | false = false
... | true  = true
-- case split: C-c C-c ("control+c then control+c")

-- For instance, "even? zero" should yield "true".
-- For instance, "even? (succ zero)" should yield "false".
-- For instance, "even? (succ (succ zero))" should yield "true".
! : Bool → Bool
! false = true
! true  = false

even? : ℕ → Bool
even? zero     = true
even? (succ n) = ! (even? n)

even?' : ℕ → Bool
even?' zero            = true
even?' (succ zero)     = false
even?' (succ (succ n)) = even? n

exampleEq? : Bool
exampleEq? = eq? (succ (succ (succ zero))) (succ zero)

exampleEven? : Bool
exampleEven? = even? (succ (succ (succ zero)))


-- Let's define, in Agda, what even and odd numbers are.

-- For this, let's define a type "Even n".
-- This type depends on the number n.
-- The values of type "Even n" should be witnesses that
-- n is even.
-- For instance, the type "Even (succ zero)" should be empty.
-- In contrast, the type "Even zero" should be inhabited.

data Even : ℕ → Set where
  base : Even zero
  step : {n : ℕ} → Even n → Even (succ (succ n))
  -- "step" is a function of two arguments, a number n
  -- and a witness that n is even. In such a situation,
  -- this function will output a freshly-minted witness
  -- of the evenness of "succ (succ n)".

fact-zero-is-even : Even zero
fact-zero-is-even = base

fact-two-is-even : Even (succ (succ zero))
fact-two-is-even = step {zero} base
-- C-c C-r ("refine goal")

fact-six-is-even : Even (succ (succ (succ (succ (succ (succ zero))))))
fact-six-is-even = step (step (step base))

failed-attempt-at-proving-that-one-is-even : Even (succ zero)
failed-attempt-at-proving-that-one-is-even = {!!}

data ⊥ : Set where  -- \bot

-- Let's prove that, if n is even, then n is even.
fact-if-n-is-even-then-n-is-even : {n : ℕ} → Even n → Even n
-- In computing terms: This is a function which reads in
-- a number n and a witness that n is even, and outputs
-- a witness that n is even.
-- In logical terms: For every number n, if n is even,
-- then n is even.
fact-if-n-is-even-then-n-is-even p = p

-- By definition, a claim is not true if and only if
-- assuming it would imply a contradiction.
fact-one-is-not-even : Even (succ zero) → ⊥
fact-one-is-not-even ()

foo : ℕ → Set
foo zero            = ℕ
foo (succ zero)     = Bool
foo (succ (succ n)) = Even (succ zero)
-- Fun fact: The two functions "foo" and "Even" have the same
-- type, namely they are both functions ℕ → Set.

Even' : ℕ → Set
Even' zero     = Unit
  where
  data Unit : Set where
    tt : Unit
Even' (succ zero)     = ⊥
Even' (succ (succ n)) = Even' n

lemma-sum-even : {a b : ℕ} → Even a → Even b → Even (a + b)
lemma-sum-even base     q = q
lemma-sum-even (step p) q = step (lemma-sum-even p q)
