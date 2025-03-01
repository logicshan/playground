{-# OPTIONS --allow-unsolved-metas #-}

{-
  0, 1, 2, 3, 4, ..., ω, ω + 1, ω + 2, ...,
  ^^^^^^^^^^^^^^^^^^  ^
   these are natural   ∞ is not a nat. numb.
       numbers

  ω + ω = ω·2, ..., ω·3, ..., ω·ω = ω², ..., ω³, ...,

  ω^ω, ..., ω^(ω·2), ..., ω^(ω^ω), ..., ω^(ω^(ω^ω)), ...,

  ω^(ω^(ω^…)) = ε₀, ε₀ + 1, ..., ε₀·2, ...,

  ε₀^(ε₀^(ε₀^…)) = ε₁, ..., ε₂, ..., ε_ω, ..., ε_{ω+1}, ...,

  ε_{ε₀}, ..., ε_{ε₁}, ..., ε_{ε₂}, ..., ε_{ε_{ε_…}} = ζ₀, ...

  This is the beginning of the list of ordinal numbers.
  The displayed numbers are still tiny in the sense that
  each number has only countably many predeccesors.
-}

{-
  Picture of ω:
    :-)   I  I  I  I  I  ...
    
  Picture of ω + 1:
         +------------------+ 
    :-)  |I  I  I  I  I  ...|  I
         +------------------+
        
  Picture of ω + ω + 1:
         +-------------+  +-------------+
    :-)  |I  I  I  ... |  |I  I  I  ... |  I
         +-------------+  +-------------+

  Picture of 1 + ω:
    :-)   I  I  I  I  I  I  ...

  What do we know about ω + 1 vs. 1 + ω?
  A: succ ω = ω + 1 > ω;   1 + ω = ω.
-}

{-
  The three fundamental convictions regarding (countable)
  ordinals numbers are:

  1. Zero should exist.
  2. Every number should have a successor.
  3. Every (strictly ascending) sequence should have a limit.

  For instance, ω is the limit of the sequence
    0,   1,   2,  3, ...
    ||   ||   ||
    f 0  f 1  f 2

  Note: ω is also the limit of the sequence
    0,   1,   2,   4,   8,  16,  32, ...
    ||   ||   ||   ||   ||
    g 0  g 1  g 2  g 3  g 4
-}

data ℕ : Set where
  zer : ℕ
  suc : ℕ → ℕ

-- The type "Monotonic f" is the type of witnesses
-- that "f" is a strictly increasing sequence.
data O : Set
Monotonic : (ℕ → O) → Set
_<_ : O → O → Set
data _≤_ : O → O → Set

Monotonic f = (n : ℕ) → f n < f (suc n)

-- O is not precisely the type of ordinals,
-- but the type of representations of ordinals.
-- Many ordinals have more than one representation.
data O where
  zero : O
  succ : O → O
  lim  : (f : ℕ → O) → Monotonic f → O

x < y = succ x ≤ y

data _≤_ where
  ≤-zero     : {x : O} → zero ≤ x
  ≤-succ-mon : {x y : O} → x ≤ y → succ x ≤ succ y
  ≤-trans    : {x y z : O} → x ≤ y → y ≤ z → x ≤ z
  ≤-cocone   : {f : ℕ → O} {fmon : Monotonic f} {x : O} {n : ℕ}
             → x ≤ f n → x ≤ lim f fmon
  ≤-limiting : {f : ℕ → O} {fmon : Monotonic f} {x : O}
             → ((n : ℕ) → f n ≤ x) → lim f fmon ≤ x

fromℕ : ℕ → O
fromℕ zer     = zero
fromℕ (suc n) = succ (fromℕ n)

fromℕ-monotonic : Monotonic fromℕ
fromℕ-monotonic n = {!!}

ω : O
ω = lim fromℕ fromℕ-monotonic
-- "ω is the limit of the sequence 0, 1, 2, ..."

ω' : O
ω' = lim (λ n → fromℕ (suc n)) {!!}
-- "ω' is the limit of the sequence 1, 2, 3, ..."

data ⊥ : Set where
_≡_ = {!!}

example₀ : ω ≡ ω' → ⊥
example₀ = {!!}

example₁ : ω ≤ ω'
example₁ = {!!}

example₂ : ω' ≤ ω
example₂ = {!!}

_+_ : O → O → O
x + zero       = x
x + succ y     = succ (x + y)
x + lim f fmon = lim (λ n → x + f n) {!!}

example₃ : ω < succ ω
example₃ = {!!}

example₄ : (succ zero + ω) ≤ ω
example₄ = {!!}
