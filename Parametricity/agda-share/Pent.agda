
-- Defining Church numeral pentation using inductive-recursive universes.
--
-- This is apparently not possible with only ω-many predicative universes,
-- according to Finitely Stratified Polymorphism by Daniel Leivant
--
--    https://www.sciencedirect.com/science/article/pii/0890540191900535

module Pent where

open import Function
open import Level hiding (suc)
open import Data.Unit

import Data.Product
import Data.Nat as N
open N using (ℕ)

-- Set is a Mahlo universe. For every family F = (A : Set, B : A → Set) there
-- is a universe (U : Set, T : U → Set) and a family F' = (A' : U, B' : A → U)
-- that is the restriction of F to U.
--
-- The universes are only assumed to additionally contain Pi types, because
-- that is all we need for Church numerals.
module Mahlo (A : Set) (B : A → Set) where
  data U : Set
  T : U → Set

  data U where
    A' : U
    B' : A → U
    Π : (s : U) (f : T s → U) → U

  syntax Π s (λ x → t) = Π[ x ∈ s ] t

  T A' = A
  T (B' a) = B a
  T (Π s f) = (x : T s) → T (f x)

  -- Plain functions.
  infixr 4 _⇒_
  _⇒_ : U → U → U
  a ⇒ b = Π[ _ ∈ a ] b

  -- Church numerals on U
  CH : Set
  CH = (r : U) → (T r → T r) → T r → T r

  zro : CH
  zro r s z = z

  suc : CH → CH
  suc m r s = s ∘ m r s

  one : CH
  one = suc zro

  infixl 10 _+_
  _+_ : CH → CH → CH
  (m + n) r s = m r s ∘ n r s

  infixl 20 _×_
  _×_ : CH → CH → CH
  (m × n) r = m r ∘ n r

  -- It's easy to get up to exponentiation without doing anything fancy.
  infixr 30 _^_
  _^_ : CH → CH → CH
  (m ^ n) r = n (r ⇒ r) (m r)

-- 'Big' Church numerals in arbitrary Set levels.
CHURCH : (α : Level) → Set (Level.suc α)
CHURCH α = ∀(R : Set α) → (R → R) → (R → R)

-- Tetration of Church numerals on Set.
--
-- Given m, n : CHURCH 0, and R : Set, s : R → R, z : R
--
--   - There exists a universe U : Set that contains R
--   - The Church numerals over U, CH : Set, can iterate R
--   - We can lower from m : CHURCH 0 to CH
--   - We can repeatedly exponentiate CH with a CHURCH 0
--
-- So we can use this universe to do our tetration.
_↑_ : CHURCH zero → CHURCH zero → CHURCH zero
(m ↑ n) R s z = n CH (_^_ m') one R' s z
  where
  open Mahlo R (const ⊤) renaming (A' to R')

  m' : CH
  m' = m CH suc zro

-- With uniform tetration defined, we can do pentation with slightly
-- larger numerals.
_⇈_ : CHURCH zero → CHURCH (Level.suc zero) → CHURCH zero
(m ⇈ n) = n (CHURCH zero) (_↑_ m) (λ R s z → s z)


module Visualize where
  open Data.Product

  toCH : ∀{α} → ℕ → CHURCH α
  toCH 0 R s z = z
  toCH (N.suc n) R s z = s (toCH n R s z)

  fromCH : ∀{α} → CHURCH α → ℕ
  fromCH m = lower $ m (Lift _ ℕ) (lift ∘ N.suc ∘ lower) (lift N.zero)

  lift₀ : (CHURCH zero → CHURCH zero → CHURCH zero) → ℕ → ℕ → ℕ
  lift₀ op m n = fromCH (op (toCH m) (toCH n))

  lift₁ : (CHURCH zero → CHURCH (Level.suc zero) → CHURCH zero) → ℕ → ℕ → ℕ
  lift₁ op m n = fromCH (op (toCH m) (toCH n))

  2↑2 2↑3 2↑4 3↑2 3↑3 : ℕ
  2↑2 = lift₀ _↑_ 2 2
  2↑3 = lift₀ _↑_ 2 3
  2↑4 = lift₀ _↑_ 2 4
  3↑2 = lift₀ _↑_ 3 2
  3↑3 = lift₀ _↑_ 3 3

  2⇈2 2⇈3 : ℕ
  2⇈2 = lift₁ _⇈_ 2 2
  2⇈3 = lift₁ _⇈_ 2 3

  tetr : ℕ
  tetr = 3↑3

  pent : ℕ
  pent = 2⇈3
