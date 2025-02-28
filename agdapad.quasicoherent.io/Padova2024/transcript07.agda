{-# OPTIONS --allow-unsolved-metas #-}

open import Padova2024.EquationalReasoning
{-# BUILTIN EQUALITY _≡_ #-}

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

ℕ-inj : {x y : ℕ} → succ x ≡ succ y → x ≡ y
ℕ-inj {zero} {zero} refl = refl
ℕ-inj {zero} {succ y} ()
ℕ-inj {succ x} {zero} ()
ℕ-inj {succ x} {succ .x} refl = refl

data _⊎_ (A B : Set) : Set where
  left  : A → A ⊎ B
  right : B → A ⊎ B

record _×_ (A B : Set) : Set where
  eta-equality
  constructor _,_
  field
    proj₁ : A
    proj₂ : B
open _×_


data Bool : Set where
  false : Bool
  true  : Bool

data _<_ : ℕ → ℕ → Set where
  base : {n : ℕ}   → n < succ n
  step : {a b : ℕ} → a < b      → a < succ b

_+_ : ℕ → ℕ → ℕ
zero   + b = b
succ a + b = succ (a + b)

-- Predecessor function.
pred : ℕ → ℕ
pred zero     = zero
pred (succ x) = x

_ : 4 < 8
_ = step (step (step base))

half : ℕ → ℕ
half zero            = zero
half (succ zero)     = zero
half (succ (succ n)) = succ (half n)

_ : half (succ (succ (succ zero))) ≡ succ zero
_ = refl

n-step : {x : ℕ} → (n : ℕ) → x < succ (n + x)
n-step zero = base
n-step (succ n) = step (n-step n)

data Even : ℕ → Set where
  base-even : Even zero
  step-even : {n : ℕ} → Even n → Even (succ (succ n))

-- "Odd n" is the type of witnesses that "n" is odd.
data Odd : ℕ → Set where
  base-odd : Odd (succ zero)
  step-odd : {n : ℕ} → Odd n → Odd (succ (succ n))

even→odd : {n : ℕ} → Even n → Odd (succ n)
even→odd base-even = base-odd
even→odd (step-even p) = step-odd (even→odd p)

odd→even : {n : ℕ} → Odd n → Even (succ n)
odd→even base-odd = step-even base-even
odd→even (step-odd p) = step-even (odd→even p)

parity : (n : ℕ) → Even n ⊎ Odd n
parity zero = left base-even
parity (succ n) with parity n
... | left en = right (even→odd en)
... | right on = left (odd→even on)

lemma-+-succ : (a b : ℕ) → (a + succ b) ≡ succ (a + b)
lemma-+-succ zero b = refl
lemma-+-succ (succ a) b = cong succ (lemma-+-succ a b)

half-even-succ : (n : ℕ) → Even n → (half (succ n)) ≡ half n
half-even-succ zero base-even = refl
half-even-succ (succ (succ n)) (step-even p) = cong succ (half-even-succ n p)

half-odd-succ : (n : ℕ) → Odd n → (half (succ n)) ≡ succ (half n)
half-odd-succ zero ()
half-odd-succ (succ zero) base-odd = refl
half-odd-succ (succ (succ n)) (step-odd p) = cong succ (half-odd-succ n p)

half2n≡n : (n : ℕ) → half (n + n) ≡ n
half2n≡n zero = refl
half2n≡n (succ n) rewrite lemma-+-succ n n = cong succ (half2n≡n n)

half-odd : {n : ℕ} → Odd n → (half n + half (succ n)) ≡ n
half-odd base-odd = refl
half-odd (step-odd {n} p) = begin
  succ (half n + succ (half (succ n)))
    ≡⟨ cong succ (lemma-+-succ (half n) (half (succ n))) ⟩
  succ (succ ((half n) + (half (succ n))))
    ≡⟨ cong (λ x → succ (succ x)) (half-odd {n} p) ⟩
  succ (succ n) ∎

half-even-+ : (n : ℕ) → Even n → ((half n + half n) ≡ n)
half-even-+ zero base-even = refl
half-even-+ (succ (succ n)) (step-even p)
  rewrite lemma-+-succ (half n) (half n) = cong (λ x → succ (succ x)) (half-even-+ n p)

half-odd-+ : (n : ℕ) → Odd n → (succ (half n + half n) ≡ n)
half-odd-+ zero ()
half-odd-+ (succ zero) base-odd = refl
half-odd-+ (succ (succ n)) (step-odd p) 
  rewrite lemma-+-succ (half n) (half n) = cong (λ x → succ (succ x)) (half-odd-+ n p)

succ-pred : (n : ℕ) → Odd n → succ (pred n) ≡ n
succ-pred zero ()
succ-pred (succ zero) base-odd = refl
succ-pred (succ (succ n)) (step-odd p) = refl


half-odd-+' : (n : ℕ) → Odd n → (half n + half n) ≡ (pred n)
half-odd-+' zero ()
half-odd-+' (succ zero) base-odd = refl
half-odd-+' (succ (succ n)) (step-odd p)
  rewrite lemma-+-succ (half n) (half n) | half-odd-+' n p = cong succ (succ-pred n p)

odd-half-succ : (n : ℕ) → Odd n → (half (succ n)) ≡ succ (half n)
odd-half-succ zero ()
odd-half-succ (succ zero) base-odd = refl
odd-half-succ (succ (succ n)) (step-odd p) = cong succ (odd-half-succ n p)

odd-half-pred : (n : ℕ) → Odd n → (half (pred n)) ≡ half n
odd-half-pred zero ()
odd-half-pred (succ zero) base-odd = refl
odd-half-pred (succ (succ n)) (step-odd p) = odd-half-succ n p

odd-pred-+-succ : (n : ℕ) → Odd n → (pred n + succ n) ≡ (n + n)
odd-pred-+-succ zero ()
odd-pred-+-succ (succ zero) base-odd = refl
odd-pred-+-succ (succ (succ n)) (step-odd p)
  rewrite lemma-+-succ n (succ (succ n))
  = refl

half-even : {n : ℕ} → Even n → (half (succ n) + half (succ n)) ≡ n
half-even base-even = refl
half-even (step-even {n} p)
  rewrite lemma-+-succ (half (succ n)) (half (succ n))= cong (λ x → succ (succ x)) (half-even p)

lemma-half< : (a : ℕ) → half (succ a) < succ a
lemma-half< a with parity a
... | left ea = lemmaₑ (n-step {half (succ a)} (half (succ a)))
  where 
    lemmaₑ : half (succ a) < succ (half (succ a) + half (succ a)) → half (succ a) < succ a
    lemmaₑ rewrite half-even ea = λ z → z
... | right oa = lemmaₒ (n-step {half (succ a)} (half a))
  where
    lemmaₒ : (half (succ a) < succ (half a + half (succ a))) → half (succ a) < succ a
    lemmaₒ rewrite half-odd oa = λ z → z

halfsucc-even : (n : ℕ) → Even n → half (succ n) ≡ half n
halfsucc-even zero base-even = refl
halfsucc-even (succ (succ n)) (step-even p) = cong succ (halfsucc-even n p)

halfsucc-odd : (n : ℕ) → Odd n → half (succ n) ≡ succ (half n)
halfsucc-odd zero ()
halfsucc-odd (succ zero) base-odd = refl
halfsucc-odd (succ (succ n)) (step-odd p) = cong succ (halfsucc-odd n p)

lemma-2half : (n : ℕ) → 
  (((Even n) × (((half n) + (half n)) ≡ n)) ⊎ ((Odd n) × ((succ ((half n) + (half n))) ≡ n)))
lemma-2half zero = left (base-even , refl)
lemma-2half (succ n) with lemma-2half n
... | left (en , p) rewrite halfsucc-even n en = right (even→odd en , cong succ p)
... | right (on , p) = left (odd→even on , half-even-+ (succ n) (odd→even on))


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
  go : ℕ → ℕ → ℕ
  go zero       n        = zero  -- bailout!
  go (succ gas) zero     = zero
  go (succ gas) (succ n) = succ (go gas (half (succ n)))


  digits : ℕ → ℕ
  digits n = go n n

    -- Agda recognizes this definition to be wellfounded,
    -- because in the recursive call on the right-hand side,
    -- the argument "gas" is strictly structurally smaller than
    -- the argument "succ gas" on the left-hand side.
{-
  lemma₁ : (n : ℕ) → go (succ (succ ((n + n) + (n + n)))) (half (succ n)) ≡
      go (succ (n + n)) (half (succ n))
  lemma₁ n = {!!}

  lemma₀ : (n : ℕ) → (digits ((succ n) + (succ n))) ≡ succ (digits (succ n))
  lemma₀ n = cong succ little-lemma
    where
    little-lemma : (go ((n + succ n) + succ (n + succ n)) (half (succ (n + succ n)))
      ≡ succ (go (n + succ n) (half (succ n))))
    little-lemma rewrite lemma-+-succ n n | lemma-+-succ (n + n) (succ (n + n)) | lemma-+-succ (n + n) (n + n) | half2n≡n n
      = cong succ (lemma₁ n)

  lemma₂ : (n : ℕ) → (digits ((half (succ (succ n))) + (half (succ (succ n))))) ≡ succ (digits (half (succ (succ n))))
  lemma₂ zero = refl
  lemma₂ (succ n) with lemma-2half n
  ... | left (en , p) rewrite lemma-+-succ (half (succ n)) (half (succ n)) | ℕ-inj (half-odd-+ (succ n) (even→odd en)) | lemma-+-succ n (succ n) | lemma-+-succ n n | half-even-succ n en
             = temp (lemma₂ n)
             where
             temp : ((succ (go ((half n + succ (half n)) + succ (half n + succ (half n))) (half (succ (half n + succ (half n))))))
                    ≡ (succ (succ (go (half n + succ (half n)) (half (succ (half n)))))))     →
                    (succ (succ (go (succ (succ (n + n))) (half (succ (half n)))))
                    ≡ succ (succ (go (succ n) (half (succ (half n))))))
             temp rewrite lemma-+-succ (half (succ n)) (half (succ n)) | lemma-+-succ (half n) (half n) | half-even-+ n en | lemma-+-succ n (succ n) | lemma-+-succ n n
               = λ z → z
  ... | right (on , p) rewrite lemma-+-succ (half (succ n)) (half (succ n)) | half-even-+ (succ n) (odd→even on) | lemma-+-succ n (succ (succ n)) | lemma-+-succ n (succ n) | lemma-+-succ n n | half-odd-succ n on
        = {!temp (lemma₂ n)!}
        where
        temp : (succ (go ((half n + succ (half n)) + succ (half n + succ (half n))) (half (succ (half n + succ (half n)))))
               ≡ succ (succ (go (half n + succ (half n)) (half (succ (half n))))))   →
               (succ (succ (go (n + n) (half (succ (half n))))) ≡
               succ (succ (go n (half (succ (half n))))))
        temp rewrite lemma-+-succ (half n) (half n) | half-odd-+' n on | succ-pred n on | odd-half-pred n on | odd-pred-+-succ n on
          = λ z → z
-}
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
{-
  ℕ-wellfounded : (n : ℕ) → Acc n
  ℕ-wellfounded zero    = lemma-zero-is-accessible
  ℕ-wellfounded (succ n) with ℕ-wellfounded n
  ... | WN@(acc f) = acc λ
    { .n base → WN            -- n < succ n
    ; m (step m<n) → f m m<n  -- m < succ n
    }
-}

  ℕ-wellfounded : (n : ℕ) → Acc n
  ℕ-wellfounded zero    = lemma-zero-is-accessible
  ℕ-wellfounded (succ n) = acc (λ m m<sn → helper m m<sn (ℕ-wellfounded n))
    where
    helper : (m : ℕ) → m < succ n → Acc n → Acc m
    helper .n base (acc f) = acc f
    helper m (step m<n) (acc f) = f m m<n
  

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
