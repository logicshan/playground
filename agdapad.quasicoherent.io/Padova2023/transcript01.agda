{-# OPTIONS --allow-unsolved-metas #-}

data Bool : Set where
  false true : Bool
{- This creates a new datatype,
   called "Bool". Its only
   inhabitants are "false" and "true". -}

-- We would like to implement the negation function.
-- Example: "neg false" should be "true".
-- Example: "neg true"  should be "false".
neg : Bool → Bool  -- \to \rightarrow
neg false = true
neg true  = false

¬ : Bool → Bool
¬ = neg

id : Bool → Bool  -- \to \rightarrow
id x = x

-- ℕ \bN  α \alpha  \ \\
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ
{- This creates a new datatype, called "ℕ".
   Its inhabitants are:
   zero
   succ zero
   succ (succ zero)
   ... -}

-- one : ℕ : Set : Set₁ : Set₂ : Set₃ : ...
-- \_3

-- at the blackboard: sin(5)
-- in Agda:           sin 5

one : ℕ
one = succ zero

{-
  in Java:
  BufferedInputStreamReader foo = new BufferedInputStreamReader();
-}

-- Let's implement the predecessor function.
-- For instance, the predecessor of four is three.
pred : ℕ → ℕ
pred zero     = zero
pred (succ n) = n

_&&_ : Bool → Bool → Bool
false && y = false
true  && y = y

-- This will not work:
-- loop : ℕ → ℕ
-- loop n = loop n

_+_ : ℕ → ℕ → ℕ
zero + y = y
succ x + y = succ (x + y)

_×_ : ℕ → ℕ → ℕ
zero × n = zero
succ m × n = n + (m × n)

-- 3! = 3 · 2 · 1
_! : ℕ → ℕ
zero ! = one
succ n ! = succ n × (n !)
