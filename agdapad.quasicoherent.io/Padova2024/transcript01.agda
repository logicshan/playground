-- The following block of code introduces a new
-- datatype, called "Bool". This type has exactly
-- two inhabitants: "false" and "true".
-- in Haskell: data Bool = False | True
data Bool : Set where
  false : Bool
  true  : Bool

-- The following block of code introduces a new type,
-- called "ℕ". This type has infinitely many inhabitants:
-- zero, succ zero, succ (succ zero), ...
-- in Haskell: data Nat = Zero | Succ Nat
data ℕ : Set where    -- \bN ℕ
  zero : ℕ
  succ : ℕ → ℕ
-- in blackboard mathematics: sin(5), f(x)
-- in Agda:                   sin 5,  f x

-- Predecessor function.
pred : ℕ → ℕ
pred zero     = zero
pred (succ x) = x

ex : ℕ
ex = succ (pred (succ (succ (pred zero))))

data Vector (X : Set) : ℕ → Set where
  []  : Vector X zero
  _∷_ : {n : ℕ} → X → Vector X n → Vector X (succ n)

ex' : Vector Bool (succ (succ (succ zero)))
ex' = false ∷ (true ∷ (true ∷ []))

{-
-- Here the result type depends on the input value n.
-- The result type is a so-called "dependent type".
make-zero-list : (n : ℕ) → Vector ℕ n
make-zero-list len = ....
-}

-- Doubling function. For instance, "twice (succ zero)"
-- should be "succ (succ zero)".
-- twice : ℕ → ℕ
twice : (a : ℕ) → ℕ
twice zero     = zero
twice (succ x) = succ (succ (twice x))
-- What should be the definition for "twice (succ x)"?
-- blackboard mathematics: 2 * (1 + x) = 2 + 2x = succ (succ (2x))

{-
lemma : NonZero x → succ (pred x) ≡ x
lemma : pred (succ x) ≡ x
-}

one : ℕ
one = succ(zero)

my-favorite-boolean : Bool
my-favorite-boolean = true

-- Negation function. For instance "neg false"
-- should be "true", and "neg true" should be "false".
neg : Bool → Bool
neg false = true
neg true  = false
-- "Definition by pattern matching"

-- Boolean AND. For instance "and true true"
-- should be "true", but "and true false" should be "false".
_&&_ : Bool → Bool → Bool    -- → \to   α \alpha
false && y = false
true  && y = y

and' : Bool → Bool → Bool    -- → \to   α \alpha
and' false y     = false
and' true  false = false
and' true  true  = true

and'' : Bool → Bool → Bool    -- → \to   α \alpha
and'' true true = true
and'' _    _    = false

{-
lemma : and x y ≡ and' x y
lemma = ?

lemma : and x y ≡ and'' x y
-}

-- "Set" is the type of all small types.
-- "Set" itself is not a small type, but a large type.
-- The type of all large types is called "Set₁".
-- This type is a "very large type".
--
-- true : Bool : Set : Set₁ : Set₂ : Set₃ : ... : Setω

{-
  Today:

  * Teaser how Agda can look like and
    what it's for

  * Your background?

  * Communication platform?
  * Recordings?
  * Exam

  * First steps with Agda
-}

{-
sort : List ℕ → List ℕ
sort = ?
-}

{-
favorite-number : ℕ
favorite-number = 6 * 7
-}

{-
ℕ : Set
ℕ = {!!}
-}

{-
-- Just like ℕ is a type, so is "2 + 2 ≡ 4".
-- This datatype is the type of witnesses that
-- 2 + 2 equals 4.
grande-teorema : 2 + 2 ≡ 4
grande-teorema = ?

-- There is also the type "2 + 2 ≡ 5".
-- That's the type of witnesses that 2 + 2 equals 5.
-- This type is empty!
-}
