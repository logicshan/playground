{-# OPTIONS --allow-unsolved-metas #-}

{-
  PEANO ARITHMETIC IN AGDA
-}

open import Padova2024.EquationalReasoning

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

data _⊎_ (X Y : Set) : Set where
  left  : X → X ⊎ Y
  right : Y → X ⊎ Y

data Empty : Set where

-- "Fin n" will be a datatype consisting of exactly n many inhabitants.
data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (succ n)
  succ : {n : ℕ} → Fin n → Fin (succ n)

module _ where private
  example-0 : Fin (succ (succ (succ zero)))
  example-0 = zero

  example-1 : Fin (succ (succ (succ zero)))
  example-1 = succ zero

  example-2 : Fin (succ (succ (succ zero)))
  example-2 = succ (succ zero)

-- The Agda datatype of terms in PA.
-- More precisely: "Term n" is the type of PA-terms with n free variables.
data Term (n : ℕ) : Set where
  Z : Term n
  S : Term n → Term n             -- S (S (S Z))
  _+_ : Term n → Term n → Term n  -- s + t
  _·_ : Term n → Term n → Term n  -- s · t
  var : Fin n → Term n

-- The Agda datatype of formulas in PA
-- More precisely: "Form n" will be the Agda datatype of PA-formulas with n free variables.
data Form (n : ℕ) : Set where
  ⊤    : Form n
  ⊥    : Form n
  _∧_  : Form n → Form n → Form n
  _∨_  : Form n → Form n → Form n
  _⇒_ : Form n → Form n → Form n
  FA   : Form (succ n) → Form n  -- ∀
  TE   : Form (succ n) → Form n  -- ∃
  _≈_  : Term n → Term n → Form n

-- "For every number x, for every number y, x + y = 0."
ex' : Form zero
ex' = FA (FA ((var (succ zero) + var zero) ≈ Z))

Env : ℕ → Set
Env n = Fin n → ℕ

eval₀ : {n : ℕ} → Env n → Term n → ℕ
eval₀ env Z       = zero
eval₀ env (S s)   = succ (eval₀ env s)
eval₀ env (s + t) = {!!}
eval₀ env (s · t) = {!!}
eval₀ env (var x) = env x

-- "eval env φ" should be the Agda proposition that the PA-formula φ is true (wrt the given environment).
eval : {n : ℕ} → Env n → Form n → Set
eval env ⊤        = {!!}
eval env ⊥        = Empty
eval env (φ ∧ ψ)  = {!!}
eval env (φ ∨ ψ)  = eval env φ ⊎ eval env ψ
eval env (φ ⇒ ψ) = eval env φ → eval env ψ
eval env (FA φ)   = (n : ℕ) → eval (λ { zero → n ; (succ i) → env i }) φ
eval env (TE φ)   = {!!}
eval env (s ≈ t)  = eval₀ env s ≡ eval₀ env t
-- "s ≡ t" is NOT what we mean, for instance Z and Z + Z would be deemed NON-equal.

∅ : Env zero
∅ ()

-- "For every number x, x = x."
ex : Form zero
ex = FA (var zero ≈ var zero)

ex-sound : eval ∅ ex
ex-sound = λ n → refl

{-
  Let's introduce the Agda datatype of PA-proofs.

  "x ≈ x ⊢ x ≈ x"
  means: assuming x ≈ x, we have x ≈ x.

  "x ≈ y ⊢ y ≈ x"
  means: assuming x ≈ y, we have y ≈ x.
  more precisely: There is a PA-proof of the claim that y ≈ x under the assumption x ≈ y.

  "x ≈ Z ⊢ x + x ≈ Z"
  "⊢ (x ≈ Z ⇒ x + x ≈ Z)"
-}
data _⊢_ : {n : ℕ} → Form n → Form n → Set where   -- \vdash
  identity : {n : ℕ} {φ : Form n} → φ ⊢ φ
  disj-introₗ : {n : ℕ} {φ ψ : Form n} → φ ⊢ (φ ∨ ψ)
  conj-intro
    : {n : ℕ} {φ ψ χ : Form n}
    → (φ ⊢ ψ)
    → (φ ⊢ χ)
    ---------------
    → (φ ⊢ (ψ ∧ χ))
  add₀ : ⊤ ⊢ FA (((var zero) + Z) ≈ var zero)
  mul₀ : ⊤ ⊢ FA (((var zero) · Z) ≈ Z)
  lem : {n : ℕ} {φ : Form n} → (⊤ ⊢ (φ ∨ (φ ⇒ ⊥)))
                                       -- ^^^^^^^
                                       --   ¬ φ

module _ (law-of-excluded-middle : {X : Set} → X ⊎ (X → Empty)) where
  sound : {n : ℕ} (α β : Form n) (env : Env n) → (α ⊢ β) → (eval env α → eval env β)
  sound α β env p = {!!}
-- Next time we will do better than appealing to the law of excluded middle,
-- by exploring the sarcastic interpretation of Peano Arithmetic.
