{-# OPTIONS --allow-unsolved-metas #-}
open import Level hiding (zero)

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

data IsZero : ℕ → Set where
  case-zero : IsZero zero

-- The type "Is≤2 n" is the type of witnesses that "n" is less than or equal to 2.
data Is≤2 : ℕ → Set where
  case₀ : Is≤2 zero
  case₁ : Is≤2 (succ zero)
  case₂ : Is≤2 (succ (succ zero))

data Eq' : ℕ → ℕ → Set where
  z : Eq' zero zero
  s : {x y : ℕ} → Eq' x y → Eq' (succ x) (succ y)
  -- logical reading: For every number x, for every number y, if x equals y, then
  -- succ x equals succ y.
  -- computational reading: "s" is a function which reads a input a number x,
  -- a number y, a witness that x equals y, and outputs a witness that succ x equals succ y.

-- The type "a ≡ b" is the type of witnesses that "a" equals "b".
data _≡_ {ℓ : Level} {A : Set ℓ} : A → A → Set ℓ where
  refl : {x : A} → x ≡ x
  -- logical reading: For every number x, x equals x.
  -- computational reading: "refl" is a function which reads a number "x" as input
  -- and outputs a new freshly-minted witness that "x" equals "x".
  -- bailout : {x y : A} → x ≡ y

bogus-theorem : zero ≡ succ zero
bogus-theorem = {!!}

_+_ : ℕ → ℕ → ℕ
zero   + b = b
succ a + b = succ (a + b)

-- logical reading: for every number b, zero + b equals b.
-- computational reading: "lemma-zero-+" is a function which reads a number "b"
-- as input and outputs a witness that "zero + b" equals "b".
lemma-zero-+ : (b : ℕ) → (zero + b) ≡ b
lemma-zero-+ b = refl

-- logical reading: for every set X, for every set X, for every elements a, b ∈ X,
-- for every function f : X → Y, if a equals b, then f a equals f b.
-- computational reading: "cong" is a function which inputs
-- (1) a type X
-- (2) a type Y
-- (3) a value a : X
-- (4) a value b : X
-- (5) a function f : X → Y
-- (6) a witness that a equals b
-- and outputs a witness that f a equals f b.
cong : {X Y : Set} {a b : X} → (f : X → Y) → a ≡ b → f a ≡ f b
cong f refl = refl
-- recall: it is NOT the case that Set : Set. Instead, Set : Set₁.

-- "cong" could be generalized to this. Try it!
-- cong' : {ℓ ℓ' : Level} {X : Set ℓ} {Y : Set ℓ'} {a b : X} → (f : X → Y) → a ≡ b → f a ≡ f b

lemma-+-zero : (a : ℕ) → (a + zero) ≡ a
lemma-+-zero zero     = refl
lemma-+-zero (succ a) = cong succ (lemma-+-zero a)

sym : {X : Set} {a b : X} → a ≡ b → b ≡ a
sym refl = refl

{-
trans : a ≡ b → b ≡ c → a ≡ c
trans = ?
-}

lemma-+-succ : (a b : ℕ) → (a + succ b) ≡ succ (a + b)
lemma-+-succ a b = {!!}

lemma-+-commutative : (a b : ℕ) → (a + b) ≡ (b + a)
lemma-+-commutative zero     b = sym (lemma-+-zero b)
lemma-+-commutative (succ a) b = {!!}

two : ℕ
two = succ (succ zero)

four : ℕ
four = succ (succ (succ (succ zero)))

grande-teorema : (two + two) ≡ four   -- \==
grande-teorema = refl

data Bool : Set where
  false true : Bool

_&&_ : Bool → Bool → Bool    -- → \to   α \alpha
false && y = false
true  && y = y

_&&'_ : Bool → Bool → Bool    -- → \to   α \alpha
false &&' y     = false
true  &&' false = false
true  &&' true  = true

lemma : (x y : Bool) → (x && y) ≡ (x &&' y)
lemma false y     = refl
lemma true  false = refl
lemma true  true  = refl
