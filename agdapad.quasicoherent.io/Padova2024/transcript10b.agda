{-# OPTIONS --allow-unsolved-meta #-}


{-
  SIMPLY-TYPED LAMBDA CALCULUS :-)

  examples for terms in STLC:
  I = λx. x       (in Agda notation: λ x → x, in blackboard: x ↦ x)
  K = λx. λy. x   (in Agda notation: λ x → λ y → x)
  0 = λs. λz. z
  1 = λs. λz. s z
  2 = λs. λz. s (s z)
  3 = λs. λz. s (s (s z))
      λ.  λ.  1 (1 (1 0))   "de Bruijn indices"

  ingredients for terms in STLC:
  - variables
  - application
  - lambda abstraction
  - primitives for zero and successor
-}

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

-- "Ty" will be the Agda type of all the types available to STLC
data Ty : Set where
  *    : Ty             -- denoting the type of natural numbers
  _⇒_ : Ty → Ty → Ty   -- for function types A ⇒ B

⟦_⟧ : Ty → Set   -- \[[...\]]
⟦ * ⟧       = ℕ
⟦ τ ⇒ τ' ⟧ = ⟦ τ ⟧ → ⟦ τ' ⟧

-- "Term" will be the Agda type of all terms in STLC
{- This is more a type of "raw terms":
data Term : Set where
  var : String → Term         -- beware of nonsensical terms: "foo" (can be made
                              -- meaningful by: "λfoo. foo")
  app : Term → Term → Term    -- beware of type errors
  abs : String → Term → Term
-}

-- "Cxt" will be the Agda datatype of possible STLC contexts
data Cxt : Set where
  ε   : Cxt
  _,_ : Cxt → Ty → Cxt

-- "τ ∈ Γ" is the Agda datatype of witnesses that the context Γ
-- somewhere contains a variable of type τ
data _∈_ : Ty → Cxt → Set where
  here  : {Γ : Cxt} {τ : Ty} → τ ∈ (Γ , τ)  -- the de Bruijn index 0
  there : {Γ : Cxt} {τ τ' : Ty} → τ ∈ Γ → τ ∈ (Γ , τ')

-- "Term Γ τ" will be the Agda datatype of STLC terms of type τ in context Γ
data Term : Cxt → Ty → Set where
  Z   : {Γ : Cxt} → Term Γ *
  S   : {Γ : Cxt} → Term Γ (* ⇒ *)
  var : {Γ : Cxt} {τ : Ty} → τ ∈ Γ → Term Γ τ
  app : {Γ : Cxt} {τ τ' : Ty} → Term Γ (τ ⇒ τ') → Term Γ τ → Term Γ τ'
  abs : {Γ : Cxt} {τ τ' : Ty} → Term (Γ , τ) τ' → Term Γ (τ ⇒ τ')

-- "Env Γ" will be the Agda datatype of "environments of shape Γ";
-- these map each variable declaration in Γ to some value
data Env : Cxt → Set where
  ∅   : Env ε
  _∷ʳ_ : {Γ : Cxt} {τ : Ty} → Env Γ → ⟦ τ ⟧ → Env (Γ , τ)

lookup : {Γ : Cxt} {τ : Ty} → Env Γ → τ ∈ Γ → ⟦ τ ⟧
lookup (Γ ∷ʳ x) here      = x
lookup (Γ ∷ʳ x) (there p) = lookup Γ p

eval : {Γ : Cxt} {τ : Ty} → Env Γ → Term Γ τ → ⟦ τ ⟧
eval env Z         = zero
eval env S         = succ
eval env (var v)   = lookup env v
eval env (app f x) = (eval env f) (eval env x)
eval env (abs t)   = λ x → eval (env ∷ʳ x) t

I : Term ε (* ⇒ *)
I = abs (var here)    -- λx. x

open import Padova2024.EquationalReasoning

_ : eval ∅ I ≡ (λ x → x)
_ = refl

K : Term ε (* ⇒ (* ⇒ *))
K = abs (abs (var (there here)))   -- λx. λy. x

_ : eval ∅ (app S (app S (app S Z))) ≡ succ (succ (succ zero))
_ = refl
