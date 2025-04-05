{-# OPTIONS --no-termination-check #-}

module JK-Shifts where

open import Logic
open import LogicalFacts
open import Induction
open import JK-Monads
open import Equality

-- Binary shifts first:

J-∧-shift : {R A₀ A₁ : Ω} → 
---------
            J R A₀ ∧ J R A₁ → J R (A₀ ∧ A₁)

J-∧-shift (∧-intro ε₀ ε₁) = J-extend(λ a₀ → J-strength (∧-intro a₀ ε₁))(ε₀)


-- This was defined in the following alternative way in Escardo's
-- LICS2007 and LMCS2008 papers:

J-∧-shift-lics : {R A₀ A₁ : Ω} → 
--------------
                 J R A₀ ∧ J R A₁ → J R (A₀ ∧ A₁)

J-∧-shift-lics {R} {A₀} {A₁} (∧-intro ε₀ ε₁) r = ∧-intro a₀ a₁
            where a₀ : A₀
                  a₀ = ε₀(λ x₀ → J-K ε₁ (λ x₁ → r (∧-intro x₀ x₁)))
                  a₁ : A₁
                  a₁ = ε₁ (λ x₁ → r (∧-intro a₀ x₁))


observation₁ : {R A₀ A₁ : Ω} → 
------------
               (ε₀ : J R A₀) → (ε₁ : J R A₁) → (r : (A₀ ∧ A₁ → R)) →
               J-∧-shift (∧-intro ε₀ ε₁) r ≡ J-∧-shift-lics (∧-intro ε₀ ε₁) r 

observation₁ ε₀ ε₁ r = reflexivity


K-∧-shift : {R A₀ A₁ : Ω} → 
---------
            K R A₀ ∧ K R A₁ → K R (A₀ ∧ A₁)

K-∧-shift (∧-intro φ₀ φ₁) = K-extend(λ a₀ → K-strength (∧-intro a₀ φ₁))(φ₀)


observation₂ : {R A₀ A₁ : Ω} → 
------------
          (φ₀ : K R A₀) → (φ₁ : K R A₁) → (r : (A₀ ∧ A₁ → R)) →
          K-∧-shift (∧-intro φ₀ φ₁) r ≡ φ₀(λ a₀ → φ₁(λ a₁ → r (∧-intro a₀ a₁)))

observation₂ φ₀ φ₁ r = reflexivity


observation₃ : {R A₀ A₁ : Ω} → 
------------
               (ε₀ : J R A₀) → (ε₁ : J R A₁) →
               J-K (J-∧-shift (∧-intro ε₀ ε₁)) ≡ K-∧-shift (∧-intro (J-K ε₀) (J-K ε₁))

observation₃ ε₀ ε₁ = reflexivity



-- Preliminary lemmas for the countable shifts.
-- The following definitions are the same with a parameter J/K.

J-∧-shift' : {R : Ω} {A : ℕ → Ω} → 
----------
             J R (A O) ∧ J R (∀(n : ℕ) → A(succ n)) → 
             J R (∀(n : ℕ) → A n)

J-∧-shift' = (J-functor cons) ∘ J-∧-shift



K-∧-shift' : {R : Ω} {A : ℕ → Ω} → 
----------
             K R (A O) ∧ K R (∀(n : ℕ) → A(succ n)) → 
             K R (∀(n : ℕ) → A n)

K-∧-shift' = (K-functor cons) ∘ K-∧-shift


---------------------------------------------------------------
--                                                           --
-- The J-∀-shift and derivation of the K-∀-shift from this.  --
--                                                           --
---------------------------------------------------------------

-- Definition given by Escardo and Oliva MSCS2009:

J-∀-shift : {R : Ω} {A : ℕ → Ω} → 
---------
            (∀(n : ℕ) → J R (A n)) → J R (∀(n : ℕ) → A n)

J-∀-shift εs = J-∧-shift' (∧-intro (head εs) (J-∀-shift(tail εs)))


-- So, the J-∀-shift is the infinite iteration of the J-∧-shift'.

-- Definition given in LICS2007 and LMCS2008 (Section 8.1, called Π)

prod : {R : Ω} {A : ℕ → Ω} → 
----
       (∀ (n : ℕ) → J R (A n)) → J R (∀ (n : ℕ) → A n)

prod {R} {A} εs p = cons (∧-intro a₀ ((prod (tail εs)) (prefix a₀ p)))
 where a₀ : A O
       a₀ = head εs (λ a → prefix a p ((prod (tail εs))(prefix a p)))

-- End. Some remarks follow.


{-- Don't try this, unless you want agda to loop for ever:

proposition : {R : Ω} {A : ℕ → Ω} → 
-----------
              J-∀-shift {R} {A} == prod 

proposition = reflexivity 

-- We could try to use Berger's tricks to rewrite the above functionals
-- so that strong normalization is retained. But this wouldn't make
-- the above proposition (which is true) to go through, because the normal
-- forms would be different names for the recursively defined variables,
-- What is true is that a functional satisfies the equation that defines
-- J-∀-shift iff it satisfies the equation that defined prod.

--}

-----------------------
-- Important remark  --
-----------------------
-- 
-- The following similar definition is not good.
--
--
-- It doesn't produce a total functional.
-- It is included only for the sake of illustration,


K-∀-shift-divergent : {R : Ω} {A : ℕ → Ω} → 
-------------------
                       (∀(n : ℕ) → K R (A n)) → K R (∀(n : ℕ) → A n)

K-∀-shift-divergent φs = K-∧-shift' (∧-intro (head φs) (K-∀-shift-divergent(tail φs)))
