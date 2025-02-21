{-# OPTIONS --allow-unsolved-metas #-}
open import Padova2024.EquationalReasoning

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero   + b = b
succ a + b = succ (a + b)

data List (X : Set) : Set where
  []  : List X
  _∷_ : X → List X → List X

_++_ : {X : Set} → List X → List X → List X
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

{-
  toy programming language, examples for valid expressions:

  - add (lit zero) (lit zero)                           -- should evaluate to zero
  - add (lit zero) (add (lit (succ zero)) (lit zero))   -- should evaluate to succ zero
-}

data Expr : Set where
  lit : ℕ → Expr             -- literals (constants)
  add : Expr → Expr → Expr   -- addition

example : Expr
example = add (lit zero) (add (lit (succ zero)) (lit zero))   -- should evaluate to succ zero

-- An interpreter for our toy programming language
eval : Expr → ℕ
eval (lit x)   = x
eval (add a b) = eval a + eval b

_ : eval example ≡ succ zero
_ = refl

data Op : Set where    -- type of operations
  PUSH : ℕ → Op
  SUM  : Op

Stack : Set
Stack = List ℕ

Code : Set
Code = List Op
-- for instance, PUSH 3 ∷ PUSH 5 ∷ SUM is a value of type Code.
-- for instance, PUSH 3 ∷ SUM is also a value of type Code; however, running it will fail.

-- A simulator for our virtual machine
run : Code → Stack → Stack
run []           s             = s
run (PUSH x ∷ c) s             = run c (x ∷ s)
run (SUM ∷ c)    (a ∷ (b ∷ s)) = run c ((a + b) ∷ s)
run _            _             = []

-- A compiler for our toy programming language
compile : Expr → Code → Code
compile (lit x)   c = PUSH x ∷ c
compile (add a b) c = compile b (compile a (SUM ∷ c))

theorem : (e : Expr) (c : Code) (s : Stack) → run (compile e c) s ≡ run c (eval e ∷ s)
theorem (lit x)   c s = refl
theorem (add a b) c s = begin
  run (compile (add a b) c) s             ≡⟨⟩
  run (compile b (compile a (SUM ∷ c))) s ≡⟨ theorem b (compile a (SUM ∷ c)) s ⟩
  run (compile a (SUM ∷ c)) (eval b ∷ s)  ≡⟨ theorem a (SUM ∷ c) (eval b ∷ s) ⟩
  run c ((eval a + eval b) ∷ s)           ≡⟨⟩
  run c (eval (add a b) ∷ s)              ∎

compile₀ : Expr → Code
compile₀ e = compile e []

theorem₀ : (e : Expr) → run (compile₀ e) [] ≡ (eval e ∷ [])
theorem₀ e = theorem e [] []

{-
compile : Expr → Code
run     : Code → ℕ
theorem : (e : Expr) → run (compile e) ≡ eval e
-}
