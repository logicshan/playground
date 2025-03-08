module Shallow where

open import Data.Nat
open import Data.Product
open import Data.Unit

-- The types of the λ-calculus are Agda's types.
type = Set

-- The typing contexts are sets.
context = Set

-- The empty context is the unit type
∙ : context
∙ = ⊤

-- Extending a context with type is Agda's cartesian product
infixl 5 _⨟_
_⨟_ : context → type → context
Γ ⨟ A = Γ × A

-- The λ-calculus type nat is Agda's type ℕ
nat : type
nat = ℕ

-- The λ-calculus function type is Agda's function type
infixr 7 _⇒_
_⇒_ : type → type → type
A ⇒ B = A → B

-- The λ-calculus typing judgement x : nat, f : nat ⇒ nat, y : nat ⊢ succ (succ x) : nat
example-1 : (∙ ⨟ nat ⨟ nat ⇒ nat ⨟ nat) → nat
example-1 (((_ , x) , f) , y) = suc (suc x)

-- The λ-calculus typing judgement ∙ ⊢ (λ (x y : nat) succ x) (succ (succ 0))
example-2 : ∙ → nat ⇒ nat
example-2 tt = (λ (x y : nat) → suc x) (suc (suc 0))

-- The λ-calculus typing judgement f : A ⇒ A ⊢ λ (x : A) f (f x) : A ⇒ A
example-3 : {A : type} → (∙ ⨟ A ⇒ A) → (A ⇒ A)
example-3 {A} (_ , f) = λ (x : A) → f (f x)
