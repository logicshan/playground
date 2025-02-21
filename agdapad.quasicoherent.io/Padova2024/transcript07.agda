{-# OPTIONS --allow-unsolved-metas #-}

open import Padova2024.EquationalReasoning

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

data _<_ : ℕ → ℕ → Set where
  base : {n : ℕ}   → n < succ n
  step : {a b : ℕ} → a < b      → a < succ b

_+_ : ℕ → ℕ → ℕ
zero   + b = b
succ a + b = succ (a + b)

half : ℕ → ℕ
half zero            = zero
half (succ zero)     = zero
half (succ (succ n)) = succ (half n)

_ : half (succ (succ (succ zero))) ≡ succ zero
_ = refl

lemma-half< : (a : ℕ) → half (succ a) < succ a
lemma-half< a = {!!}

-- "digits n" should be the number of binary digits of the number "n".
-- For instance: Recall that the number 5 is written in binary as 101.
-- So "digits 5" should be "3". "number 7" should also be "3".
-- "digits 8" should be "4". The number 8 can be written in binary
-- as 00000000001000, but still "digits 8" should be "4".
{-
digits : ℕ → ℕ
digits zero     = zero
digits (succ n) = succ (digits (half (succ n)))
-}
-- Issue: Agda does not realize that this recursion is well-founded.
-- This function definition does make sense, but Agda doesn't realize
-- that. To be on the safe side, Agda rejects this definition, out of
-- fear that this function might be trapped in an infinite viscious loop.

{-
loop : ℕ → ℕ
loop n = loop (succ n)
-}


-- There are five options how to deal with this issue:
-- (1) {-# TERMINATING #-} (this won't work with {-# OPTIONS --safe #-})
-- (2) {-# NON_TERMINATING #-} (this won't work with {-# OPTIONS --safe #-})
-- (3) rewrite function, employ a different algorithm
-- (4) use a poor version of gas
-- (5) use a sophisticated version of gas ("well-founded induction")
--
-- For more complex cases, there is also the "Braga method", perhaps used in conjunction
-- with "well-quasi-orders".

module Option-1 where
  {-# TERMINATING #-}
  digits : ℕ → ℕ
  digits zero     = zero
  digits (succ n) = succ (digits (half (succ n)))

  {-# TERMINATING #-}
  loop : ℕ → ℕ
  loop n = loop (succ n)
  -- dangerous!

module Option-2 where
  {-# NON_TERMINATING #-}
  digits : ℕ → ℕ
  digits zero     = zero
  digits (succ n) = succ (digits (half (succ n)))

  -- The following hole can NOT be filled:
  new-lemma : (n : ℕ) → digits (succ n) ≡ succ (digits (half (succ n)))
  new-lemma n = {!!}

module Option-3 where
  -- employ a totally different algorithm

module Option-4 where
  -- employ gas
  digits : ℕ → ℕ
  digits n = go (n + n) n
    where
    go : ℕ → ℕ → ℕ
    go zero       n        = zero  -- bailout!
    go (succ gas) zero     = zero
    go (succ gas) (succ n) = succ (go gas (half (succ n)))
    -- Agda recognizes this definition to be wellfounded,
    -- because in the recursive call on the right-hand side,
    -- the argument "gas" is strictly structurally smaller than
    -- the argument "succ gas" on the left-hand side.

  lemma : (n : ℕ) → digits (succ n) ≡ succ (digits (half (succ n)))
  lemma n = {!!}

module Option-5 where
  -- use a generalized kind of gas which is not brittle
  -- and not ad hoc, but fundamental to the nature of
  -- natural numbers

  -- "Acc n" expresses that the number "n" is accessible,
  -- where accessibility is the smallest notion with the following property:
  -- A number is accessible iff all its predecessors are.
  data Acc : ℕ → Set where
    acc : {n : ℕ} → (f : (m : ℕ) → (m<n : m < n) → Acc m) → Acc n

  lemma-zero-is-accessible : Acc zero
  lemma-zero-is-accessible = acc (λ { m () })

  lemma-one-is-accessible : Acc (succ zero)
  lemma-one-is-accessible = acc (λ { .zero base → lemma-zero-is-accessible })

  lemma-two-is-accessible : Acc (succ (succ zero))
  lemma-two-is-accessible = acc λ
    { .(succ zero) base → lemma-one-is-accessible
    ; .zero (step base) → lemma-zero-is-accessible
    }

  ℕ-wellfounded : (n : ℕ) → Acc n
  ℕ-wellfounded n = {!!}

  go : (n : ℕ) → Acc n → ℕ
  go zero     p       = zero
  go (succ n) (acc f) = succ (go (half (succ n)) (f (half (succ n)) (lemma-half< n)))

  digits : ℕ → ℕ
  digits n = go n (ℕ-wellfounded n)

  lemma-go-extensional : (n : ℕ) (p q : Acc n) → go n p ≡ go n q
  lemma-go-extensional zero     p       q       = refl
  lemma-go-extensional (succ n) (acc f) (acc g) = cong succ (lemma-go-extensional (half (succ n)) _ _)

  lemma : (n : ℕ) → digits (succ n) ≡ succ (digits (half (succ n)))
  lemma n = begin
    digits (succ n)                                           ≡⟨⟩
    go (succ n) (ℕ-wellfounded (succ n))                      ≡⟨⟩
    succ (go (half (succ n)) _)                               ≡⟨ cong succ (lemma-go-extensional (half (succ n)) _ _) ⟩
    succ (go (half (succ n)) (ℕ-wellfounded (half (succ n)))) ≡⟨⟩
    succ (digits (half (succ n)))                             ∎
