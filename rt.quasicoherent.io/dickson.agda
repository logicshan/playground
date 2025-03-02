{-
  The following infinite sequence of natural numbers
  
      α :  10, 5, 3, 2, 4, 6, 6, 6, 6, 6, 6, ...
           ^   ^     ^^^^
           |    \       α 3 ≤ α 4
           α 0   α 1

  is good because some earlier term in the sequence
  is smaller than some later term.

  Dickson's Lemma (simple version).
  Every infinite sequence of natural numbers is good.
  More precisely: For every infinite sequence α,
  there are indices i < j such that α(i) ≤ α(j).
  In fact, it even holds that: For every infinite sequence α,
  there is an index i such that α(i) ≤ α(i+1).

  Proof. The infinite sequence α attains a minimal value
  somewhere. Let's call this minimal value α(i). Then
  we observe α(i) ≤ α(i+1). Hence α is good.

  Note. The hypothetical generalization of Dickson's Lemma
  to integers is false, as for instance the infinite sequence

      0, -1, -2, -3, ...

  is _not_ good.
-}

{-
  Note: The claim that every infinite sequence of natural numbers
  attains a minimal value is _not_ provable in constructive mathematics.
  Because if there was a constructive proof of this claim,
  then there would also be an algorithm witnessing this claim,
  that is, there would be an algorithm which would be capable of
  determining the minimal value of any infinite sequence of
  natural numbers.

  In other words: In Agda, there is no function

      minimum : (ℕ → ℕ) → ℕ

  worthy of its name.
-}

open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum

Dickson : (ℕ → ℕ) → Set
-- in math: ∃i ∈ ℕ.   α(i) ≤ α(i+1)
Dickson α = Σ[ i ∈ ℕ ] α i ≤ α (suc i)
-- "Dickson α" is the type of pairs (i , p)
-- where i is some value of type ℕ
-- and where p is a value of type α i ≤ α (suc i).

module Classical where
  data ⊥ : Set where

  -- "ex falso quodlibet"
  -- "from a contradiction, anything follows"
  ⊥-elim : {X : Set} → ⊥ → X
  ⊥-elim ()

  postulate
    oracle : (X : Set) → X ⊎ (X → ⊥)
    -- Logical reading: X holds, or not X holds.
    -- (Recall: The negation of X is defined as "X → ⊥".)
    -- Computational reading: "oracle" is a function which
    -- reads an arbitrary X as input and outputs a witness
    -- of either X or of X → ⊥.

  module _ (α : ℕ → ℕ) where
    {-# TERMINATING #-}
    go : ℕ → Σ[ i ∈ ℕ ] ((j : ℕ) → α i ≤ α j)
    go i with oracle (Σ[ j ∈ ℕ ] α j < α i)
    ... | inj₁ (j , p) = go j
    -- In this case, there is some value α j which is strictly smaller (<) than α i.
    -- So α i is not the absolute minimal value. So we need to continue searching
    -- for the minimal value.

    ... | inj₂ q = i , h
    -- In this case, there is no value α j which would be strictly smaller than α i.
    -- So we are done searching for the minimal value.
      where
      h : (j : ℕ) → α i ≤ α j
      h j with ≤-<-connex (α i) (α j)
      ... | inj₁ αi≤αj = αi≤αj
      ... | inj₂ αj<αi = ⊥-elim (q (j , αj<αi))

    -- Logical reading: There is a number i such that for every number j,
    -- it holds that α i ≤ α j.
    -- Computational reading: "minimum" is a pair consisting of a number i
    -- and a function which reads as input a number j and which outputs
    -- a witness that α i ≤ α j.
    minimum : Σ[ i ∈ ℕ ] ((j : ℕ) → α i ≤ α j)
    minimum = go 0

    theorem : Dickson α
    theorem with minimum
    ... | i , p = i , p (suc i)

module Example where
  α : ℕ → ℕ
  α 0 = 50
  α 1 = 30
  α 2 = 7
  α _ = 4

module ConstructiveButUninformative (⊥ : Set) where
  ¬_ : Set → Set
  ¬ X = X → ⊥

  ⊥-elim : {X : Set} → ⊥ → ¬ ¬ X
  ⊥-elim p = λ k → p

  return : {X : Set} → X → ¬ ¬ X
  return p = λ k → k p
  -- Constructively, we do NOT have ¬ ¬ X → X.
  -- That would be the principle of double negation elimination.

  escape : ¬ ¬ ⊥ → ⊥
  escape p = p (λ z → z)

  oracle : (X : Set) → ¬ ¬ (X ⊎ ¬ X)
  oracle X = λ k → k (inj₂ (λ x → k (inj₁ x)))

  _⟫=_ : {A B : Set} → ¬ ¬ A → (A → ¬ ¬ B) → ¬ ¬ B
  m ⟫= f = λ k → m (λ x → f x k)

  module _ (α : ℕ → ℕ) where
    {-# TERMINATING #-}
    go : ℕ → ¬ ¬ (Σ[ i ∈ ℕ ] ((j : ℕ) → ¬ ¬ (α i ≤ α j)))
    go i = oracle (Σ[ j ∈ ℕ ] α j < α i) ⟫= g
      where
      g : ((Σ[ j ∈ ℕ ] α j < α i) ⊎ ((Σ[ j ∈ ℕ ] α j < α i) → ⊥)) →
        ¬ ¬ (Σ[ i ∈ ℕ ] ((j : ℕ) → ¬ ¬ (α i ≤ α j)))
      g (inj₁ (j , p)) = go j
      g (inj₂ q)       = return (i , h)
        where
        h : (j : ℕ) → ¬ ¬ (α i ≤ α j)
        h j with ≤-<-connex (α i) (α j)
        ... | inj₁ αi≤αj = return αi≤αj
        ... | inj₂ αj<αi = ⊥-elim (q (j , αj<αi))

    minimum : ¬ ¬ (Σ[ i ∈ ℕ ] ((j : ℕ) → ¬ ¬ (α i ≤ α j)))
    minimum = go 0

    theorem : ¬ ¬ (Dickson α)
    theorem = minimum ⟫= λ (i , p) → p (suc i) ⟫= λ q → return (i , q)

module Constructive where
  module _ (α : ℕ → ℕ) where
    open ConstructiveButUninformative (Dickson α)
    -- "Use the module ConstructiveButUninformative in the special case ⊥ ≔ Dickson α."

    thm : Dickson α
    thm = escape (theorem α)
    -- The proof uses the minimum function in the double negation monad. But in
    -- the end, we can escape that monad!
