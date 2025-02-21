{-# OPTIONS --allow-unsolved-metas #-}

data _≡_ {X : Set} : X → X → Set where
  refl : {x : X} → x ≡ x

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

half : ℕ → ℕ
half zero            = zero
half (succ zero)     = zero
half (succ (succ n)) = succ (half n)
{-                                ^
                                  this argument to "half" is structurally
                                  smaller than the input argument
                                  "succ (succ n)"                      -}

_ : half (succ (succ (succ zero))) ≡ succ zero
_ = refl

data _<_ : ℕ → ℕ → Set where
  base  : {n : ℕ}     → n < succ n
  step  : {a b : ℕ}   → a < b → a < succ b

_ : zero < succ (succ (succ zero))
_ = step (step base)

lemma-succ-mon : {a b : ℕ} → a < b → succ a < succ b
lemma-succ-mon base     = base
lemma-succ-mon (step p) = step (lemma-succ-mon p)

lemma-succ-step : (a : ℕ) → a < succ a
lemma-succ-step a = {!!}

<-trans : {a b c : ℕ} → a < b → b < c → a < c
<-trans p q = {!!}

-- "digits n" should be the number of binary digits of
-- the number "n", with the convention that the number zero
-- consists of no binary digits at all.
-- For instance, "digits 5" should be "3", as 5 is 101 in binary.

half< : (n : ℕ) → half (succ n) < succ n
half< zero            = base
half< (succ zero)     = base
half< (succ (succ n)) = lemma-succ-mon (<-trans (half< n) (lemma-succ-step (succ n)))

-- The type "Acc n" is the type of witnesses that the number "n"
-- is accessible.
data Acc : ℕ → Set where
  -- Logical reading: For every number x,
  -- if every number y smaller than x is accessible,
  -- then x is accessible.
  acc : {x : ℕ} → ({y : ℕ} → y < x → Acc y) → Acc x
-- "Acc x" is the type of trees consisting of a root
-- and as many children as there are numbers smaller than "x".
-- To be more precise: one child for each number y together with a
-- witness that y < x.

data BinaryTree : Set where
  leaf : BinaryTree
  fork : BinaryTree → BinaryTree → BinaryTree
-- When we write "fork s t", then "s" and "t" are each
-- structurally smaller than "fork s t": "s" and "t"
-- are constitutent parts of the new whole, namely of "fork s t".

{-
{-# OPTIONS --no-positivity-check #-}

data V : Set where
  fork : (V → V) → V

absurd : ⊥
absurd = ?
-}

data CountablyBranchingTree : Set where
  leaf : CountablyBranchingTree
  fork : (ℕ → CountablyBranchingTree) → CountablyBranchingTree
-- When we write "fork f", then all the outputs of "f"
-- are each structurally smaller than "fork f": The outputs of "f"
-- are constitutent parts of the new whole, namely of "fork f".

data ExtremelyBranchingTree : Set₁ where
  leaf : ExtremelyBranchingTree
  fork : (Set → ExtremelyBranchingTree) → ExtremelyBranchingTree

open import Agda.Primitive

ex : Setω
ex = (n : Level) → Set n

ex' : Setω₁
ex' = Setω
{-
       *
     /  \
   leaf  *
        / \
     leaf  leaf
-}
exampleTree : BinaryTree
exampleTree = fork leaf (fork leaf leaf)

-- size : BinaryTree → ℕ

lemma-zero-is-accessible : Acc zero
lemma-zero-is-accessible = acc (λ ())

lemma-one-is-accessible : Acc (succ zero)
lemma-one-is-accessible = acc (λ { base → lemma-zero-is-accessible })

-- Logical reading: Every number n is accessible.
ℕ-is-wellfounded : (n : ℕ) → Acc n
ℕ-is-wellfounded n = {!!}

go : (n : ℕ) → Acc n → ℕ
go zero     g       = zero
go (succ n) (acc f) = succ (go (half (succ n)) (f (half< n)))
{-                                              ^^^^^^^^^^^
                                                this argument to "go"
                                                is structurally smaller
                                                than the input argument
                                                "acc f"                  -}

digits : ℕ → ℕ
digits n = go n (ℕ-is-wellfounded n)
