module JK-Algebras where

open import Logic
open import LogicalFacts
open import JK-Monads
open import Equality

-- Now we define what is meant to be an algebra of the monads J R and
-- K R, with proofs ranged over by s (for structure map).


J-alg : Ω → Ω → Ω
-----

J-alg R A = J R A → A


-- Most of the theorems actually hold for algebras in the monad sense,
-- as in the following definition. But we don't account for this at
-- the moment here. We record the official definition, however:


J-algebra : Ω → Ω → Ω
---------

J-algebra R A = ∃(\(s : (J-alg R A)) → s ∘ ηJ ≡ id  ∧  s ∘ μJ ≡ s ∘ (J-functor s))


K-alg : Ω → Ω → Ω
-----

K-alg R A = K R A → A



-- The R can be changed contravariantly:

contravariant-R : {R₀  R₁ A : Ω} →
---------------
                  (R₁ → R₀) → J R₀ A → J R₁ A

contravariant-R f ε = λ p → ε (f ∘ p)

-- For J-algs the R can be changed covariantly:


covariant-R : {R₀ R₁ A : Ω} →
-----------
              (R₀ → R₁) → J-alg R₀ A → J-alg R₁ A

covariant-R f s = s ∘ (contravariant-R f)


-- Corollary:

split-R : {R₀ R₁ A : Ω} →
-------
           J-alg (R₀ ∧ R₁) A → (J-alg R₀ A) ∧ (J-alg R₁ A)

split-R ε = ∧-intro (covariant-R ∧-elim₀ ε) (covariant-R ∧-elim₁ ε)


-- The converse also holds:

glue-R : {R₀ R₁ A : Ω} →
------
      J-alg R₀ A → J-alg R₁ A → J-alg (R₀ ∧ R₁) A

glue-R s₀ s₁ ε = s₀(λ p₀ → s₁(λ p₁ → ε(λ a → ∧-intro (p₀ a) (p₁ a))))


-- Of course there is a symmetric proof:


glue-R' : {R₀ R₁ A : Ω} →
------
      J-alg R₀ A → J-alg R₁ A → J-alg (R₀ ∧ R₁) A

glue-R' s₀ s₁ ε = s₁(λ p₁ → s₀(λ p₀ → ε(λ a → ∧-intro (p₀ a) (p₁ a))))


-- Similar (this generalizes the J-multiplication when f=g=identity):


lemma₁ : {R R₀ R₁ A : Ω} →
------ 
        (R → R₀) → (R → R₁) → J R₀ (J R₁ A) → J R A

lemma₁ f g E p = E(λ ε → (f ∘ p)(ε(g ∘ p)))(g ∘ p)


corollary₁ : {R₀ R₁ A : Ω} →
---------- 
            J R₀ (J R₁ A) → J (R₀ ∧ R₁) A

corollary₁ = lemma₁ ∧-elim₀ ∧-elim₁ 


proposition₁ : {R R₀ R₁ A : Ω} →
------------
               J (R₀ ∧ R₁) A → J R₀ (J R₁ A) 

proposition₁ ε P p =
    ε(λ a → ∧-intro (P(λ p' → ε(\a' → ∧-intro (P(λ _ → a')) (p' a')))) (p a))


-- Notice that the distributivity J R (J S A) → J S (J R A) follows.

-- Several examples and preservation properties follow:
-- (Needed for the J- and K-translations.)


free-J-alg : {R A : Ω} →
----------
                 J-alg R (J R A)

free-J-alg = μJ


free-K-alg : {R A : Ω} →
----------
                 K-alg R (K R A)

free-K-alg = μK


-- Products of algebras (of any monad) are algebras:


∧-J-preservation : {R A₀ A₁ : Ω} → 
----------------
                   J-alg R A₀ → J-alg R A₁ → J-alg R (A₀ ∧ A₁)

∧-J-preservation s₀ s₁ = λ ε → ∧-intro (s₀ (J-functor ∧-elim₀ ε)) 
                                       (s₁ (J-functor ∧-elim₁ ε)) 


∧-K-preservation : {R A₀ A₁ : Ω} → 
----------------
                   K-alg R A₀ → K-alg R A₁ → K-alg R (A₀ ∧ A₁)

∧-K-preservation s₀ s₁ = λ φ → ∧-intro (s₀ (K-functor ∧-elim₀ φ)) 
                                       (s₁ (K-functor ∧-elim₁ φ)) 


-- Algebras (of any monad) are exponential ideals:


ideal-J : {R A B : Ω} →
-------
          J-alg R B → J-alg R (A → B)

ideal-J s = λ ε → λ a → s (J-functor (λ f → f a) ε)



ideal-K : {R A B : Ω} →
-------
          K-alg R B → K-alg R (A → B)

ideal-K s = λ φ → λ a → s (K-functor (λ f → f a) φ)


-- Generalization:


∀-ideal-J : {R : Ω} {A : Set} {B : A → Ω} → 
---------

            (∀(a : A) → J-alg R (B a)) → J-alg R (∀(a : A) → B a)

∀-ideal-J s = λ ε → λ a → s a (J-functor (λ f → f a) ε)



∀-ideal-K : {R : Ω} {A : Set} {B : A → Ω} → 
---------

            (∀(a : A) → K-alg R (B a)) → K-alg R (∀(a : A) → B a)

∀-ideal-K s = λ φ → λ a → s a (K-functor (λ f → f a) φ)

-----------------------------------
--                               --
-- Various things about algebras --  
--                               --
-----------------------------------


-- Any K-J-alg is a J-alg.
-- (Generalizes for any two monads with a monad morphism.)


J-alg-from-K-alg : {R A : Ω} →
----------------
                   K-alg R A → J-alg R A

J-alg-from-K-alg s = s ∘ J-K


-- Notice that because there is a monad morphism J-K, the free
-- K-algebra is a J-algebra, i.e. it satisfies Peirce's Law.
-- This explains call/cc.


-- What shall we call the following family of J-algs? They are
-- canonical in a sense, but do they have a special status?


canonical-J-alg : {R A : Ω} →
---------------
                  (A → R) → J-alg R A


canonical-J-alg p = λ ε → ε p


-- There isn't such a canonical corresponding K-alg.
-- But notice that:

R-negations-are-K-algs : {R A : Ω} →
----------------------
                         K-alg R (A → R)

R-negations-are-K-algs = λ φ → λ p → φ(λ f → f p)

-- Hence they are J-algs too, by a previous lemma.

-- Now, if A is decidable wrt R, then it is a J-alg. 

Decidable : Ω → Ω → Ω
---------

Decidable R A = A ∨ (A → R)


J-alg-from-R-decidable : {R A : Ω} →
----------------------
                          Decidable R A → J-alg R A

J-alg-from-R-decidable (∨-intro₀ a) = λ ε → a
J-alg-from-R-decidable (∨-intro₁ p) = λ ε → ε p


-- It is not possible to do the same for K-algs.
