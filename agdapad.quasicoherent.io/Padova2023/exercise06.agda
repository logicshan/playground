{-# OPTIONS --allow-unsolved-metas #-}
-- AGDA IN PADOVA 2023
-- Exercise sheet 6

-- The usual naturals, the constructor names shortened to "zer" and "suc"
-- to not confuse them with the ordinal zero and ordinal successor
-- (Agda wouldn't mind, but we might).
data ℕ : Set where
  zer : ℕ
  suc : ℕ → ℕ


-----------------------------
----[ BASIC DEFINITIONS ]----
-----------------------------

-- "O" will be the type of (representations of) (countable) ordinal numbers.
data O : Set

-- "x ≤ y" will be the type of witnesses that "x" is smaller or equal to "y".
data _≤_ : O → O → Set

-- "x < y" will be the type of witnesses that "x" is strictly smaller than "y".
_<_ : O → O → Set

-- "Monotonic f" is the type of witnesses that "f" is a strictly increasing sequence
-- of ordinals.
Monotonic : (ℕ → O) → Set
Monotonic f = (a : ℕ) → f a < f (suc a)

-- The following definition expresses the three fundamental convictions regarding
-- (countable) ordinal numbers:
-- 1. zero should exist.
-- 2. Every number should have a successor.
-- 3. Every (strictly increasing) sequence should have a limit.
data O where
  zero : O
  succ : O → O
  lim  : (f : ℕ → O) → Monotonic f → O

data _≤_ where
  ≤-zero     : {x : O}     → zero ≤ x
  ≤-trans    : {x y z : O} → x ≤ y → y ≤ z → x ≤ z
  ≤-succ-mon : {x y : O}   → x ≤ y → succ x ≤ succ y
  ≤-cocone   : {f : ℕ → O} {fmon : Monotonic f} {x : O} {n : ℕ}
             → x ≤ f n → x ≤ lim f fmon
  ≤-limiting : {f : ℕ → O} {fmon : Monotonic f} {x : O}
             → ((n : ℕ) → f n ≤ x) → lim f fmon ≤ x

x < y = succ x ≤ y


----------------------------
----[ BASIC PROPERTIES ]----
----------------------------

-- If the terms of "f" are all smaller than the corresponding term in "g",
-- then the limit of "f" is smaller than the limit of "g".
lim-mon
  : {f g : ℕ → O} {fmon : Monotonic f} {gmon : Monotonic g}
  → ((n : ℕ) → f n ≤ g n)
  → lim f fmon ≤ lim g gmon
lim-mon p = ≤-limiting (λ n → ≤-cocone (p n))

refl : {x : O} → x ≤ x
refl {zero}       = ≤-zero
refl {succ x}     = ≤-succ-mon refl
refl {lim f fmon} = lim-mon (λ a → refl)

id≤succ : {x : O} → x ≤ succ x
id≤succ {zero}    = ≤-zero
id≤succ {succ x}  = ≤-succ-mon id≤succ
id≤succ {lim f x} = ≤-limiting (λ n → ≤-trans id≤succ (≤-succ-mon (≤-cocone refl)))


--------------------------
----[ BASIC EXAMPLES ]----
--------------------------

fromℕ : ℕ → O
fromℕ zer     = zero
fromℕ (suc n) = succ (fromℕ n)

fromℕ-monotonic : Monotonic fromℕ
fromℕ-monotonic n = refl

ω : O
ω = lim fromℕ fromℕ-monotonic

ω' : O
ω' = lim (λ n → fromℕ (suc n)) (λ n → refl)

example₀ : ω ≤ ω'
example₀ = lim-mon (λ n → id≤succ)

example₁ : ω' ≤ ω
example₁ = ≤-limiting (λ n → ≤-cocone {n = suc n} refl)


----------------------------
----[ ORDINAL ADDITION ]----
----------------------------

-- The following two functions are defined in a mutually recursive fashion.
_+_ : O → O → O
+-mon : {x a b : O} → a ≤ b → (x + a) ≤ (x + b)

a + zero       = a
a + succ b     = succ (a + b)
a + lim f fmon = lim (λ n → a + f n) (λ n → +-mon (fmon n))

+-mon {b = zero} ≤-zero       = refl
+-mon {b = succ b} ≤-zero     = ≤-trans id≤succ (≤-succ-mon (+-mon ≤-zero))
+-mon {b = lim f fmon} ≤-zero = ≤-cocone (+-mon (≤-zero {f zer}))
+-mon (≤-trans p q)           = ≤-trans (+-mon p) (+-mon q)
+-mon (≤-succ-mon p)          = ≤-succ-mon (+-mon p)
+-mon (≤-cocone p)            = ≤-cocone (+-mon p)
+-mon (≤-limiting p)          = ≤-limiting (λ b → +-mon (p b))

example₂ : ω < (ω + succ zero)
example₂ = refl

example₃ : (succ zero + ω) ≤ ω
example₃ = ≤-limiting (λ n → ≤-cocone {n = suc n} (lemma n))
  where
  lemma : (n : ℕ) → (succ zero + fromℕ n) ≤ succ (fromℕ n)
  lemma zer = refl
  lemma (suc n) = ≤-succ-mon (lemma n)

-- EXERCISE: Prove this.
+-zero : (a : O) → (zero + a) ≤ a
+-zero = {!!}

-- EXERCISE: Prove this. For some clauses, you may need to case split
-- on the implicit variable a.
+-mon' : {x y a : O} → x ≤ y → (x + a) ≤ (y + a)
+-mon' {a = a} p = {!!}


-----------------------------------
----[ MORE ORDINAL ARITHMETIC ]----
-----------------------------------

-- EXERCISE: Define ordinal multiplication and exponentiation, by
-- implementing the rules listed on the Wikipedia page on ordinal arithmetic.

-- EXERCISE: Define the ordinal number ε₀.

-- EXERCISE: State and prove that ω ^ ε₀ is the same as ε₀.

-- EXERCISE: Define the numbers ε₁, ε₂, ...

-- NOTE: Do not expect these exercises to have short solutions.
-- The monotonicity requirement in the "lim" constructor entails
-- quite a few proof obligations. However, we cannot drop this
-- requirement as else exponentiation is no longer definable:
-- The definition requires a case distinction which is possible
-- only because of the monotonicity requirement.

-- For an extensive discussion, see https://arxiv.org/abs/2208.03844.


----------------------------------
----[ LEMMAS FOR COMPARISONS ]----
----------------------------------

data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (x : A) → (y : B x) → Σ A B

proj₁ : {A : Set} {B : A → Set} → Σ A B → A
proj₁ (x , y) = x

proj₂ : {A : Set} {B : A → Set} → (p : Σ A B) → B (proj₁ p)
proj₂ (x , y) = y

-- "f simulates g" expresses that every term in the sequence "g"
-- is dominated by some term in the sequence "f".
-- For instance, the sequence 0,1,2,… simulates the sequence 0,1,2,4,8,16,…
-- (and vice versa).
_simulates_ : (ℕ → O) → (ℕ → O) → Set
f simulates g = (a : ℕ) → Σ ℕ (λ b → g a ≤ f b)

-- EXERCISE: Prove this.
comparison-lemma
  : {f g : ℕ → O} {fmon : Monotonic f} {gmon : Monotonic g}
  → f simulates g → lim g gmon ≤ lim f fmon
comparison-lemma sim = {!!}

-- EXERCISE: Reprove "lim-mon" from above using "comparison-lemma".
lim-mon'
  : {f g : ℕ → O} {fmon : Monotonic f} {gmon : Monotonic g}
  → ((n : ℕ) → f n ≤ g n)
  → lim f fmon ≤ lim g gmon
lim-mon' p = comparison-lemma (λ n → n , p n)


--------------------------------------
----[ THE FAST-GROWING HIERARCHY ]----
--------------------------------------

-- EXERCISE: Implement the "fast-growing hierarchy" of functions,
-- by following the definition of the respective Wikipedia entry.
