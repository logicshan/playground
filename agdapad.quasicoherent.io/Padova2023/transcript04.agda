data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero   + b = b
succ a + b = succ (a + b)

-- The claim that there is a prime larger than 10
-- has infinitely many witnesses, for instance the
-- following one:
-- The triple consisting of
-- (1) the number 11
-- (2) a witness that 11 > 10
-- (3) a witness that 11 is prime

data Even : ℕ → Set where
  base : Even zero
  -- Logical reading: "By definition, zero is even."
  -- Computational reading: "We have a witness of evenness of zero."

  step : {n : ℕ} → Even n → Even (succ (succ n))
  -- Logical reading: "For every number n, if n is even, then
  -- succ (succ n) is even."
  -- Computational reading: "We have a function, namely 'step',
  -- which reads a number n and a witness that n is even as input,
  -- and outputs a witness that succ (succ n) is even."

-- Let's define the notion of twin numbers,
-- for instance 10 and 12 are twins,
-- or 31 and 33 are twins.

-- In Agda, we introduce a type family Twin:
-- For all numbers "a" and "b", there will be a type "Twin a b"
-- of witnesses that "a" and "b" are twins. For many values of "a"
-- and "b", this type will be empty. For instance, "Twin zero zero"
-- will be empty, because zero and zero are not twins.
data Twin : ℕ → ℕ → Set where
  link : {n : ℕ} → Twin n (succ (succ n))
  -- "link" is a function which takes one argument,
  -- namely a number "n", and outputs a freshly-minted
  -- witness that n and succ (succ n) are twins.
  -- Thanks to the curly braces, we usually do not need to
  -- explicitly specify the first argument. Instead, Agda
  -- will try to infer it.

ex : Twin (succ zero) (succ (succ (succ zero)))
ex = link {succ zero}

data ⊥ : Set where

-- logical reading: Assuming that zero and zero would
-- be twins, we would have a contradiction.
-- computational reading: We can transform hypothetical
-- witnesses of twinness of zero and zero into witnesses
-- of a contradiction.
ex' : Twin zero zero → ⊥
ex' ()

-- Let's define equality! For all numbers "a" and "b",
-- there will be a type "a ≡ b" of witnesses that "a" and "b"
-- are the same. For instance, the type "zero ≡ succ zero"
-- will be empty. In contrast, the type "zero ≡ zero" will
-- be inhabited.
infix 5 _≡_
data _≡_ : ℕ → ℕ → Set where
  refl : {n : ℕ} → n ≡ n

lemma₀ : zero ≡ zero   -- \==
lemma₀ = refl
-- We can use "refl" as a justification that two numbers
-- are the same if and only if this fact is evident to Agda.
-- In blackboard mathematics, "refl" roughly corresponds to
-- stating "By direct computation, we see that the two numbers
-- are the same".

lemma₁ : (succ zero + succ zero) ≡ succ (succ zero)
lemma₁ = refl

-- Logical reading: "For every number b, it is the case that zero + b equals b."
-- Computational reading: "lemma₂ is a function which reads a number b as input
-- and outputs a witness that zero + b equals b."
lemma₂ : (b : ℕ) → (zero + b) ≡ b
lemma₂ b = refl

cong : {x y : ℕ} → (f : ℕ → ℕ) → x ≡ y → f x ≡ f y
cong f refl = refl

lemma-+-zero : (b : ℕ) → b + zero ≡ b
lemma-+-zero zero     = refl
lemma-+-zero (succ b) = cong succ (lemma-+-zero b)
