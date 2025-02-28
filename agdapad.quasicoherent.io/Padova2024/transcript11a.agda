{-# OPTIONS --allow-unsolved-metas #-}

{-
  Plan for today:
  1. mutable state
  2. miniature Agda in Agda
  3. all your questions
-}

open import Padova2024.EquationalReasoning

-- Let's say we want to keep track of mutable state of some type S.

data _×_ (X Y : Set) : Set where
  _,_ : X → Y → X × Y

data ⊤ : Set where
  tt : ⊤

{-
  idea: instead of f : X → Y, have:

  f : X → S → S × Y
  f x s = (new value of state , result of computation)
-}

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero   + b = b
succ a + b = succ (a + b)

module _ where private
  tick : {X : Set} → X → ℕ → ℕ × X
  tick x s = (succ s , x)

-- Idea: Introduce a type "State S X" of computations which result in a value
-- of type X, but require mutable state of type S.
State : Set → Set → Set
State S X = S → S × X

_>>=_ : {S X Y : Set} → State S X → (X → State S Y) → State S Y
(f >>= h) s with f s
... | s' , y = h y s'

_>>_ : {S X Y : Set} → State S X → State S Y → State S Y
f >> g = f >>= λ _ → g

-- "return" reads a value x : X as input and outputs a stateful computation
-- which, without mutating the threaded state, results in the same value x.
-- Note that this function is NOT related to the keyword for
-- prematurely exiting a subroutine from many imperative programming languages.
return : {S X : Set} → X → State S X
return x s = s , x

get : {S : Set} → State S S
get s = s , s

put : {S : Set} → S → State S ⊤
put s' s = s' , tt

modify : {S : Set} → (S → S) → State S ⊤
modify f s = f s , tt

module _ where private
  postulate
    X Y Z : Set
    S : Set

    f : X → State S Y
    g : Y → State S Z

  h : X → State S Z
  h x = f x >>= g

  {-
    y = f x;
    g y
  -}
  h' : X → State S Z
  h' x = do
    y ← f x
    g y
--    return z
  -- "overloading semicolon"

-- The type of binary trees, with leaves labelled with elements of X.
data Tree (X : Set) : Set where
  leaf : X → Tree X
  fork : Tree X → Tree X → Tree X

-- The "sum" function below sums the values at all leaves, while simultaneously
-- keeping track of the total number of leaves in the form of mutable state.

tick : State ℕ ⊤
tick = do
  count ← get
  put (succ count)
-- shorter: tick = modify succ

sum : Tree ℕ → State ℕ ℕ
sum (leaf x) = do
  tick
  return x
sum (fork left right) = do
  leftSum  ← sum left
  rightSum ← sum right
  return (leftSum + rightSum)

exampleTree : Tree ℕ
exampleTree = fork (fork (leaf 4) (leaf 5)) (leaf 6)

_ : sum exampleTree 0 ≡ (3 , 15)
_ = refl
