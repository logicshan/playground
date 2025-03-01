{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Nat
open import Data.Sum

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B
-- Computational reading: A × B is the type of all pairs (x , y),
-- where x : A and y : B.
-- Logical reading: A × B is true if and only if both A and B are true.

data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (x : A) → (y : B x) → Σ A B

fst : {A : Set} {B : A → Set} → Σ A B → A
fst (x , y) = x

-- "Dickson's Lemma"
Dickson : (ℕ → ℕ) → Set
Dickson α = Σ ℕ (λ i → α i ≤ α (suc i))
-- For every function α : ℕ → ℕ, there is a number i such that
-- α i ≤ α (suc i).

ex : ℕ → ℕ
ex 0 = 10
ex 1 = 5
ex 2 = 30
ex _ = 4

{-
  Here is an algorithm for proving A ⊎ (¬ A),
  ASSUMING you have a time machine.

  1. We are asked whether A ⊎ (¬ A).
  2. We reply: "That's easy! In fact, ¬ A holds."
     (More precisely, we claim: A → ⊥.)
  3. Perhaps this claim doesn't get challenged. Then we are lucky.
  4. But perhaps our opponent challenges us by presenting a witness x : A
     and expecting from us a witness of ⊥.
  5. In this case, ignore this challenge. Instead jump back in time to
     step 1. In the new timeline, we instead reply: "That's easy! In fact,
     A holds. Here is a witness for A: x."

  Programs of result type ¬ ¬ (...) have access to some kind of time machine.

-}

{-
_ : Dickson ex
_ = 2 , s≤s (s≤s (s≤s z≤n))
-}

module Classical where
  data ⊥ : Set where

  ⊥-elim : {X : Set} → ⊥ → X
  ⊥-elim ()

  ¬_ : Set → Set
  ¬ X = X → ⊥

  postulate
    -- the law of excluded middle
    oracle : (A : Set) → A ⊎ (¬ A)

  double-negation-elimination : {A : Set} → ¬ ¬ A → A
  double-negation-elimination {A} p with oracle A
  ... | inj₁ q = q
  ... | inj₂ q = ⊥-elim (p q)

  -- Logical reading: If it is NOT the case that ¬ A and ¬ B, then
  de-morgan : {A B : Set} → ¬ ((¬ A) × (¬ B)) → A ⊎ B
  de-morgan {A} {B} f with oracle A | oracle B
  ... | inj₁ a  | inj₁ b  = inj₁ a
  ... | inj₁ a  | inj₂ ¬b = inj₁ a
  ... | inj₂ ¬a | inj₁ b  = inj₂ b
  ... | inj₂ ¬a | inj₂ ¬b = ⊥-elim (f (¬a , ¬b))

  -- Logical reading: If it is NOT the case that for all x : A, B x is false,
  -- then B x is true for at least one x.
  de-morgan∞ : {A : Set} {B : A → Set} → ¬ ((x : A) → ¬ (B x)) → Σ A B
  de-morgan∞ {A} {B} P with oracle (Σ A B)
  ... | inj₁ (x , Bx) = x , Bx
  ... | inj₂ ¬xBx = ⊥-elim (P q)
        where
        q : (x : A) → ¬ (B x)
        q x Bx = ¬xBx (x , Bx)

  -- Logical reading: Every function α : ℕ → ℕ attains a minimal value α i,
  -- i.e. there is some number i such that α i ≤ α j for all j.
  module _ (α : ℕ → ℕ) where
    {-# TERMINATING #-}
    go : ℕ → Σ ℕ (λ i → ((j : ℕ) → α i ≤ α j))
    go i with oracle (Σ ℕ (λ j → α j < α i))  -- Is there j such that α j < α i?
    ... | inj₁ (j , αj<αi) = go j             -- Yes; α j has better chances
                                              -- of being the minimal value
    ... | inj₂ p = (i , h)
      where
      h : (j : ℕ) → α i ≤ α j
      h j with ≤-<-connex (α i) (α j)
      ... | inj₁ αi≤αj = αi≤αj
      ... | inj₂ αj<αi = ⊥-elim (p (j , αj<αi))

    minimum : Σ ℕ (λ i → ((j : ℕ) → α i ≤ α j))
    minimum = go 0

  -- Objective: Given a function α : ℕ → ℕ, output a number i such that α i
  -- is the minimal value of α.
  minimum₀ : (α : ℕ → ℕ) → ℕ
  minimum₀ α = fst (minimum α)

  -- Classical proof: The function α attains some minimal value α i.
  -- Then, trivially, α i ≤ α (suc i).
  -- In fact, we would even have (but not need for this proof) that α i ≤ α j
  -- for all j.
  thm : (α : ℕ → ℕ) → Dickson α
  thm α with minimum α
  ... | i , h = i , h (suc i)

module Sarcastic (⊥ : Set) where
  ¬_ : Set → Set
  ¬ X = X → ⊥

  escape : ¬ ¬ ⊥ → ⊥
  escape = λ z → z (λ z₁ → z₁)

  oracle : (A : Set) → ¬ ¬ (A ⊎ (¬ A))
  oracle = λ A z → z (inj₂ (λ x → z (inj₁ x)))

  de-morgan : {A B : Set} → ¬ ((¬ A) × (¬ B)) → ¬ ¬ (A ⊎ B)
  de-morgan = λ z z₁ → z ((λ x → z₁ (inj₁ x)) , (λ x → z₁ (inj₂ x)))

  de-morgan∞ : {A : Set} {B : A → Set} → ¬ ((x : A) → ¬ (B x)) → ¬ ¬ (Σ A B)
  de-morgan∞ = λ z z₁ → z (λ x z₂ → z₁ (x , z₂))

  -- The sarcastic interpretation of classical logic:
  -- Add ¬ ¬ in front of every ⊎, Σ and in front of every atomic statement.

  modus-ponens : {A B : Set} → A → (A → B) → B
  modus-ponens = λ z z₁ → z₁ z

  _>>=_ : {A B : Set} → ¬ ¬ A → (A → ¬ ¬ B) → ¬ ¬ B
  _>>=_ = λ z z₁ z₂ → z (λ z₃ → z₁ z₃ z₂)

  -- "If A actually holds, then it also holds sarcastically."
  return : {A : Set} → A → ¬ ¬ A
  return = λ z z₁ → z₁ z

  ⊥-elim : {A : Set} → ⊥ → ¬ ¬ A
  ⊥-elim = λ z _ → z

  module _ (α : ℕ → ℕ) where
    {-# TERMINATING #-}
    go : ℕ → ¬ ¬ Σ ℕ (λ i → ((j : ℕ) → ¬ ¬ (α i ≤ α j)))
    go i = oracle (Σ ℕ (λ j → α j < α i)) >>= g
      where
      g : (Σ ℕ (λ j → α j < α i)) ⊎ ¬ (Σ ℕ (λ j → α j < α i)) → _
      g (inj₁ (j , αj<αi)) = go j
      g (inj₂ p)           = return (i , h)
        where
        h : (j : ℕ) → ¬ ¬ (α i ≤ α j)
        h j with ≤-<-connex (α i) (α j)
        ... | inj₁ αi≤αj = return αi≤αj
        ... | inj₂ αj<αi = ⊥-elim (p (j , αj<αi))

    minimum : ¬ ¬ Σ ℕ (λ i → ((j : ℕ) → ¬ ¬ (α i ≤ α j)))
    minimum = go 0

  thm : (α : ℕ → ℕ) → ¬ ¬ (Dickson α)
  --thm α = minimum α >>= λ { (i , h) → h (suc i) >>= λ αi≤α1+i → return (i , αi≤α1+i) }
  thm α = do
    (i , h) ← minimum α
    αi≤α1+i ← h (suc i)
    return (i , αi≤α1+i)

  foo : ¬ ¬ ℕ
  foo f = f zero

module Constructive where
  module _ (α : ℕ → ℕ) where
    open Sarcastic (Dickson α)

    theorem : Dickson α
    theorem = escape (thm α)
