{-# OPTIONS --safe #-}

module Prime where

open import Data.Nat
open import Data.Nat.Divisibility
open import Data.Nat.Primality
open import Data.Nat.Primality.Factorisation hiding (factors)
open import Data.Nat.Properties
open import Data.List as List
open import Data.List.Properties
open import Data.List.Relation.Unary.All as All
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Infinitary

-- The set of prime numbers
Primes : Set
Primes = Σ ℕ Prime

-- Given a list of primes ps, `big ps` is its product.
big : List Primes → ℕ
big ps = product (List.map proj₁ ps)

-- Factorization of `big ps + 1` for use in Euclid's proof.
big-factors : ∀ ps → PrimeFactorisation (big ps + 1)
big-factors ps rewrite +-comm (big ps) 1 = factorise _

module _ where
  open PrimeFactorisation

  -- `big ps + 1` is always at least 2.
  nonTriv-factors
    : ∀ ps → NonTrivial (product (big-factors ps .factors))
  nonTriv-factors ps
    rewrite sym (big-factors ps .isFactorisation)
          | +-comm (big ps) 1
    = n>1⇒nonTrivial (s≤s (>-nonZero⁻¹ _))
    where instance
    nz = product≢0 (All.map prime⇒nonZero (fromList ps))

-- If a number p > 1 (`NonTrivial`) divides P+1, it does
-- not divide P.
--
-- This is because if it did, it would also divide
-- (P+1 - P) = 1, and no number above 1 divides 1.
lemma : ∀{p} P → .⦃ NonTrivial p ⦄ → p ∣ (P + 1) → p ∤ P
lemma {p} P p∣P+1 p∣P
  = >⇒∤ (nonTrivial⇒n>1 p) (∣m+n∣m⇒∣n p∣P+1 p∣P)

-- Prime numbers avoid lists; for every list of primes,
-- there is a prime not on it.
euclid : avoids-lists Primes
euclid ps = build factors factorsPrime isFactorisation
  where
  open PrimeFactorisation (big-factors ps)

  instance
    _ : NonTrivial (product factors)
    _ = nonTriv-factors ps

  -- Extract a number from a prime factorisation and show
  -- that it isn't in the original list.
  build : (qs : List ℕ)
        → All Prime qs
        → big ps + 1 ≡ product qs
        -- ↓ allows us to skip considering empty lists
        → ⦃ NonTrivial (product qs) ⦄
        → Σ[ q ∈ Primes ] q ∉ ps
  build (q ∷ _) (qp ∷ _) big+1≡qs .proj₁ = q , qp
  build (q ∷ _) (qp ∷ _) big+1≡qs .proj₂ q∈ps =
    lemma (big ps) q∣big+1 q∣big
    where
    q∣big+1 : q ∣ big ps + 1
    q∣big+1 rewrite big+1≡qs = m∣m*n _

    q∣big = ∈⇒∣product (∈-map⁺ proj₁ q∈ps)

-- Prime numbers are infinite; there is an injection from
-- ℕ to primes.
infinite : is-infinite Primes
infinite = avoids-lists⇒is-infinite euclid

-- Prime numbers are not finite; every listing of primes
-- does not contain all primes.
unfinite : not-finite Primes
unfinite = is-infinite⇒not-finite infinite
