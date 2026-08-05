
-- A well-typed interpreter

module Interp where

infix 20 _,_
infixr 25 _::_
infix 23 _!_
infixr 30 _⇒_

data Bool : Set where
  true  : Bool
  false : Bool

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

{-# BUILTIN NATURAL Nat  #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}

_+_ : Nat -> Nat -> Nat
zero    + n = n
(suc m) + n = suc (m + n)
{-# BUILTIN NATPLUS _+_ #-}

data Fin : Nat → Set where
  fz : ∀{n} → Fin (suc n)
  fs : ∀{n} → Fin n -> Fin (suc n)

data Vec (a : Set) : Nat → Set where
  []   : Vec a 0
  _::_ : ∀{n} → a → Vec a n → Vec a (suc n)

_!_ : ∀{a n} → Vec a n → Fin n -> a
[] ! ()
(x :: _)  ! fz = x
(_ :: xs) ! (fs fn) = xs ! fn

data Σ (a : Set) (P : a → Set) : Set where
  _,_ : (x : a) → (w : P x) → Σ a P

_×_ : Set → Set → Set
a × b = Σ a (λ _ → b)

proj₁ : ∀{a b} → a × b → a
proj₁ (a , _) = a

proj₂ : ∀{a b} → a × b → b
proj₂ (_ , b) = b

data Type : Set where
  bool : Type
  nat  : Type
  _⇒_  : Type → Type → Type
  _*_  : Type → Type → Type

↑ : Type → Set
↑ bool = Bool
↑ nat  = Nat
↑ (a ⇒ b) = ↑ a → ↑ b
↑ (a * b)  = ↑ a × ↑ b

Cxt : Nat → Set
Cxt n = Vec Type n

-- I used a Σ here because when I wrote this ages ago, I didn't
-- realize I could use implicit indices. Now I can't figure out
-- how to move to implicit indices without eval' breaking for
-- reasons I don't really understand. :)
data Env : Σ Nat Cxt → Set where
  empty : Env (0 , [])
  push  : {t : Type}{n : Nat}{ts : Cxt n}
             → ↑ t → Env (n , ts) → Env (suc n , t :: ts)
_!!_ : ∀{n ts} → Env (n , ts) → (i : Fin n) → ↑ (ts ! i)
empty !! ()
(push x _) !! fz = x
(push _ xs) !! (fs fn) = xs !! fn

data Term {n : Nat} : Cxt n → Type -> Set where
  val  : ∀{t ts} → ↑ t → Term ts t
  lam  : ∀{a b ts} → Term (a :: ts) b → Term ts (a ⇒ b)
  ap   : ∀{a b ts} → Term ts (a ⇒ b) → Term ts a → Term ts b
  var  : ∀{ts}     → (i : Fin n) → Term ts (ts ! i)
  pair : ∀{a b ts} → Term ts a → Term ts b → Term ts (a * b)
  fst  : ∀{a b ts} → Term ts (a * b) → Term ts a
  snd  : ∀{a b ts} → Term ts (a * b) → Term ts b
  if_then_else_ : ∀{t ts} → Term ts bool
                          → Term ts t → Term ts t
                          → Term ts t

eval' : forall {n t ts} → Env (n , ts) → Term ts t → ↑ t
eval' env (val v)    = v
eval' env (lam e)    = λ a → eval' (push a env) e
eval' env (ap f e)   = eval' env f (eval' env e)
eval' env (var i)    = env !! i
eval' env (pair a b) = eval' env a , eval' env b
eval' env (fst p)    = proj₁ (eval' env p)
eval' env (snd p)    = proj₂ (eval' env p)
eval' env (if b then t else f) with eval' env b
...                           | true  = eval' env t
...                           | false = eval' env f

eval : ∀{t} → Term [] t → ↑ t
eval = eval' empty

plusOp : ∀{n : Nat} {ts : Cxt n} → Term ts (nat ⇒ nat ⇒ nat)
plusOp = val _+_

fPlus : Term [] (nat ⇒ nat ⇒ nat)
fPlus = lam (lam (ap (ap (val _+_) (var fz)) (var (fs fz))))

fPlus' = lam {_} {_} {_} {[]} (lam (ap (ap plusOp (var fz)) (var (fs fz))))