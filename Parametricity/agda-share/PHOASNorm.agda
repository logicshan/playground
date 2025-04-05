{-# OPTIONS --no-positivity-check #-}

-- Normalizing untyped PHOAS terms. Naturally this isn't normally expressible
-- in Agda.

module PHOASNorm where

open import Data.Nat

-- untyped lambda terms
data Term' (v : Set) : Set where
  bound : v → Term' v
  lam   : (v → Term' v) → Term' v
  ap    : Term' v → Term' v → Term' v

Term : Set₁
Term = ∀ v → Term' v

-- This is the key to implementing normalization. For any non-recursive v, we
-- have a problem, because for:
--
--   (\y -> e) x
--
-- The lambda expression needs type Term' (Term' v) for substitution, while x
-- needs the type Term' v to be substituted. Thus, they can't appear in the
-- same syntax tree. However, if we had an injection Term' v → v, we could use
-- it on x and substitute (pulling it out later). This is exactly what Norm
-- accomplishes.
--
-- This fails the positivity checker, of course, but that doesn't matter if
-- we're implementing in, say, Haskell, where provable termination is already
-- out of the picture (the termination checker isn't happy with us either).
data Norm (v : Set) : Set where
  nz : v → Norm v
  ns : (Term' (Norm v)) → Norm v

norm : ∀{v} → Term' (Norm v) → Term' (Norm v)
norm (bound (nz v)) = bound (nz v)
norm (bound (ns t)) = norm t
norm (ap f       x) with norm f
... | bound (ns f') = norm (ap f' x)
... | lam e         = norm (e (ns x))
... | f'            = ap f' (norm x)
norm (lam e)        = lam (λ v → norm (e v))

cut : ∀{v} → Term' (Norm v) → Term' v
cut (bound (nz v)) = bound v
cut (bound (ns t)) = cut t
cut (ap f       x) = ap (cut f) (cut x)
cut (lam        e) = lam (λ v → cut (e (nz v)))

normalize : Term → Term
normalize t v = cut (norm (t (Norm v)))

-- I don't recommend normalizing this
{-
Ω : Term
Ω v = ap ω ω 
 where
 ω = bind lam (type 0) (λ x → ap (bound x) (bound x))
-}