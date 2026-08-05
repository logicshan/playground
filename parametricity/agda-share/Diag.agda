
-- A formalization of Cantor's diagonal argument.

module Diag where

open import Data.Bool
open import Data.Empty
open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality

variable
  A B : Set

-- Booleans are not equal to their negation. () is the absurd
-- pattern, which matches if the type checker judges a type to
-- not be inhabited. Here, they match 'false ≡ true' and
-- 'true ≡ false' respectively.
not-≢ : ∀ b → not b ≢ b
not-≢ true  ()
not-≢ false ()

-- Given any function b from the natural numbers to the Cantor space,
-- ℕ → Bool, there exists a sequence α that is not in the image of b.
--
-- One might say that ℕ → Bool isn't 'really' uncountable, because
-- there are countably many Agda-definable functions, when we reason
-- about Agda in some meta-theory (since all Agda functions can be
-- written as finite strings of symbols). But, from the internal
-- perspective, ℕ → Bool looks uncountable. From this perspective, in
-- which `ℕ → Bool` is interpreted as computable functions from
-- naturals to booleans, the proof shows that `ℕ → Bool` is computably
-- uncountable. (you'd have similar oddities doing model theory on,
-- say, ZF, where you can show that it has countable models, but you
-- can prove in ZF that various sets are uncountable.)
--
-- Generally one should not imagine that the type `ℕ → Bool` only
-- contains functions definable as Agda source anyhow, since that is a
-- very limiting perspective. But that is another discussion. See e.g.
--   http://math.andrej.com/2013/08/28/the-elements-of-an-inductive-type/
cantor
  : ∀(b : ℕ → (ℕ → Bool)) -- for all enumerations of the Cantor space
  → Σ[ α ∈ (ℕ → Bool) ]   -- there is a sequence, α
  ∀ n →                   -- such for every index in the enumeration
  Σ[ m ∈ ℕ ]              -- there is a position in the sequences
    α m ≢ b n m           -- at which α disagrees with the enumerated sequence
cantor b = diag , diag≢bn
 where
 diag : ℕ → Bool
 diag n = not (b n n)

 diag≢bn : ∀ n → Σ[ m ∈ ℕ ] diag m ≢ b n m
 diag≢bn n = n , not-≢ (b n n)
