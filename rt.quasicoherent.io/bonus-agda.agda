{-# OPTIONS --allow-unsolved-metas #-}

data ⊥ : Set where
  -- no witnesses defined here!

¬_ : Set → Set
¬ A = A → ⊥

-- in blackboard mathematics: sin(pi)
-- in Agda:                   sin pi
 
module _ (A B : Set) where
  f : A → A   -- \to
  f x = x

  g : A → B
  g x = {!!}  -- this hole cannot be filled

  h : A → ¬ ¬ A   -- \neg
  h x = λ p → p x   -- in JavaScript: function (p) { ... }
                    -- in Perl:       sub { my $p = shift; ... }
                    -- in Haskell:    \p -> ...
                    -- in Python:     lambda p: ...
  -- In the body of the lambda, p is a witness of ¬ A, so p : A → ⊥.
  -- recall: ¬ (¬ A) is an abbreviation for (A → ⊥) → ⊥

data ℕ : Set where   -- \bN
  zero : ℕ
  succ : ℕ → ℕ
-- The inhabitants of ℕ are:
-- zero, succ zero, succ (succ zero), succ (succ (succ zero)), ...

one : ℕ
one = succ zero

-- For instance, "pred one" should be "zero".
pred : ℕ → ℕ
pred zero     = zero
pred (succ a) = a

-- For instance, "pred one" should be "two".
double : ℕ → ℕ
double zero     = zero
double (succ x) = succ (succ (double x))
-- 2 * (1 + x) = 2 + 2*x = 1 + (1 + 2*x) = succ (succ (double x))

-- For any set A, and for any values u, v : A, there is the proposition "u ≡ v".
-- The only witnesses of such propositions are constructed using the "refl" constructor.
-- The "refl" constructor produces witnesses of propositions of the form "x ≡ x".
data _≡_ {A : Set} : A → A → Set where
  refl : {x : A} → x ≡ x

thm : pred one ≡ zero   -- \==
thm = refl

-- Logical reading: For every number x, x equals x.
-- Computational reading: "theorem" is a function which inputs an arbitrary number x : ℕ
-- and outputs a witness that x equals x.
theorem : (x : ℕ) → x ≡ x
theorem x = refl

_+_ : ℕ → ℕ → ℕ
zero   + b = b
succ a + b = succ (a + b)
-- informally, succ a + b = (1 + a) + b = 1 + (a + b) = succ (a + b)

two : ℕ
two = succ (succ zero)

_ : (one + one) ≡ two
_ = refl

-- Logical reading: For every number x, zero + x equals x.
-- Computational reading: "prop₁" is a function which reads an arbitrary number "x" as input
-- and outputs a witness of the claim that "zero + x" equals "x".
prop₁ : (x : ℕ) → (zero + x) ≡ x
prop₁ x = refl

module _ {A B : Set} (f : A → B) {x y : A} where
  cong : x ≡ y → f x ≡ f y
  cong refl = refl

prop₂ : (x : ℕ) → (x + zero) ≡ x
prop₂ zero     = refl
prop₂ (succ a) = cong succ (prop₂ a)
-- In the body, "prop₂ a" is a witness of "a + zero ≡ a".
-- Applying "cong succ" to this witness results in a witness of the desired equality
-- "succ (a + zero) ≡ succ a".
