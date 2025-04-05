module J-Eliminations where

open import Logic
open import LogicalFacts
open import JK-Monads
open import JK-Algebras
----------------------------------------------------------------
--                                                            --
-- Introduction and elimination rules of the J-translations   --
-- of ∨ and ∃.                                                --
--                                                            --
-- (The other connectives are trivial.)                       --
--                                                            --
----------------------------------------------------------------

J-∨-intro₀ : {R A₀ A₁ : Ω} →
---------- 
             A₀ → J R (A₀ ∨ A₁)

J-∨-intro₀ = ηJ ∘ ∨-intro₀


J-∨-intro₁ : {R A₀ A₁ : Ω} → 
----------
             A₁ → J R (A₀ ∨ A₁)


J-∨-intro₁ = ηJ ∘ ∨-intro₁ 


J-∨-elim : {R A₀ A₁ B : Ω} → 
---------
           J-alg R B →
           (A₀ → B) → (A₁ → B) → J R (A₀ ∨ A₁) → B

J-∨-elim s f₀ f₁ = s ∘ (J-functor (∨-elim  f₀ f₁))


J-∃-intro :  {R : Ω} {X : Set} {A : X → Ω} → 
---------
             (x₀ : X) → A x₀ → J R (∃(\(x : X) → A x))

J-∃-intro x₀ a = ηJ(∃-intro x₀ a)


-- We need a different elimination rule for ∃ first, which
-- generalizes the elimination rule for conjunction:


∃-Elim : {X : Set} {A : X → Ω} {B : Ω} → 
------
         ((x : X) → A x → B) → ∃(\(x : X) → A x) → B

∃-Elim f (∃-intro x a) = f x a



J-∃-Elim : {R : Ω} {X : Set} {A : X → Ω} {B : Ω} → 
--------
         J-alg R B →
         ((x : X) → A x → B) → J R (∃(\(x : X) → A x)) → B

J-∃-Elim s f = s ∘ (J-functor (∃-Elim f))


-- Notice that J R (∃(\(x : X) → A x)) → J R X.  
--
-- But how is J R X to be understood when R is a proposition and X is
-- a set?
