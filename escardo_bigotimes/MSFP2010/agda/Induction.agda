module Induction where

open import Logic

data ℕ : Set where 
     O : ℕ              -- Zero (capital letter Oh).
     succ : ℕ → ℕ       -- Successor.

-- {-# BUILTIN NATURAL ℕ #-}
-- {-# BUILTIN ZERO O #-}
-- {-# BUILTIN SUC succ #-}

_+1 : ℕ → ℕ
n +1 = succ n

_+2 : ℕ → ℕ
n +2 = n +1 +1

induction : {A : ℕ → Ω} → 
---------
            A O → (∀(k : ℕ) → A k → A(succ k)) → ∀(n : ℕ) → A n 

induction base step O = base
induction base step (succ n) = step n (induction base step n)

_+_ : ℕ → ℕ → ℕ
n + m = induction m (λ x y → succ y) n


head : {A : ℕ → Ω} → 
----
       (∀(n : ℕ) → A n) → A O

head α = α O



tail : {A : ℕ → Ω} → 
----
       (∀(n : ℕ) → A n) → ∀(n : ℕ) → A(succ n)

tail α n = α(succ n)



cons : {A : ℕ → Ω} → 
----
       A O ∧ (∀(n : ℕ) → A(succ n)) → ∀(n : ℕ) → A n

cons (∧-intro a α) O = a
cons (∧-intro a α) (succ n) = α n


prefix : {R : Ω} {A : ℕ → Ω} → 
------
          A O → ((∀(n : ℕ) → A n) → R) → (∀(n : ℕ) → A(succ n)) → R

prefix α₀ p α' = p(cons (∧-intro α₀ α'))
