{-# OPTIONS --allow-unsolved-metas #-}
-- AGDA IN PADOVA 2023
-- Exercise sheet 2


---------------------------
----[ NATURAL NUMBERS ]----
---------------------------

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero   + b = b
succ a + b = succ (a + b)

_·_ : ℕ → ℕ → ℕ
zero   · b = zero
succ a · b = b + (a · b)

-- Even n is the type of witnesses that n is even.
data Even : ℕ → Set where
  base-even : Even zero
  step-even : {n : ℕ} → Even n → Even (succ (succ n))

data Odd : ℕ → Set where
  base-odd : Odd (succ zero)
  step-odd : {n : ℕ} → Odd n → Odd (succ (succ n))

-- EXERCISE: Show that the sum of even numbers is even
lemma-sum-even : {a b : ℕ} → Even a → Even b → Even (a + b)
lemma-sum-even = {!!}

-- EXERCISE: Show that the successor of an even number is odd and vice versa
lemma-succ-even : {a : ℕ} → Even a → Odd (succ a)
lemma-succ-even = {!!}

lemma-succ-odd : {a : ℕ} → Odd a → Even (succ a)
lemma-succ-odd = {!!}

-- EXERCISE: Show that the sum of odd numbers is even
lemma-sum-odd : {a b : ℕ} → Odd a → Odd b → Even (a + b)
lemma-sum-odd = {!!}

-- EXERCISE: Show that the sum of an odd number with an even number is odd
lemma-sum-mixed : {a b : ℕ} → Odd a → Even b → Odd (a + b)
lemma-sum-mixed = {!!}

-- EXERCISE: Show that every number is even or odd.
data _⊎_ (A B : Set) : Set where
  left  : A → A ⊎ B
  right : B → A ⊎ B
-- For instance, if x : A, then left x : A ⊎ B.

lemma-even-odd : (a : ℕ) → Even a ⊎ Odd a
lemma-even-odd a = {!!}


-----------------
----[ LISTS ]----
-----------------

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

-- EXERCISE: Define a function which sums the numbers of a given list
sum : List ℕ → ℕ
sum []       = {!!}
sum (x ∷ xs) = {!!}

-- EXERCISE: Define the "map" function.
-- For instance, "map f (x ∷ y ∷ z ∷ []) = f x ∷ f y ∷ f z ∷ []".
map : {A B : Set} → (A → B) → List A → List B
map f xs = {!!}


-------------------
----[ VECTORS ]----
-------------------

data Vector (A : Set) : ℕ → Set where
  []  : Vector A zero
  _∷_ : {n : ℕ} → A → Vector A n → Vector A (succ n)

-- EXERCISE: Define a function which computes the length of a given vector.
-- There are two possible implementations, one which runs in constant time
-- and one which runs in linear time.
lengthV : {n : ℕ} {A : Set} → Vector A n → ℕ
lengthV []       = zero
lengthV (x ∷ xs) = succ (lengthV xs)

lengthV' : {n : ℕ} {A : Set} → Vector A n → ℕ
lengthV' {n} {A} xs = n

-- EXERCISE: Define the "map" function for vectors.
-- For instance, "map f (x ∷ y ∷ z ∷ []) = f x ∷ f y ∷ f z ∷ []".
mapV : {n : ℕ} {A B : Set} → (A → B) → Vector A n → Vector B n
mapV f xs = {!!}

-- EXERCISE: Define these vector functions.
-- For instance, "zipWithV f (x ∷ y ∷ []) (a ∷ b ∷ [])" should evaluate to "f x a ∷ f y b ∷ []".
zipWithV : {A B C : Set} {n : ℕ} → (A → B → C) → Vector A n → Vector B n → Vector C n
zipWithV f []       []       = {!!}
zipWithV f (x ∷ xs) (y ∷ ys) = {!!}

-- For instance, "dropV (succ zero) (a ∷ b ∷ c ∷ [])" should evaluate to "b ∷ c ∷ []".
dropV : {A : Set} {n : ℕ} (k : ℕ) → Vector A (k + n) → Vector A n
dropV k xs = {!!}

-- For instance, "takeV (succ zero) (a ∷ b ∷ c ∷ [])" should evaluate to "a ∷ []".
takeV : {A : Set} {n : ℕ} (k : ℕ) → Vector A (k + n) → Vector A k
takeV zero     xs       = []
takeV (succ k) (x ∷ xs) = x ∷ takeV k xs

-- For instance, "(a ∷ b ∷ []) ++ (c ∷ d ∷ [])" should evaluate to "a ∷ b ∷ c ∷ d ∷ []".
_++_ : {A : Set} {n m : ℕ} → Vector A n → Vector A m → Vector A (n + m)
xs ++ ys = {!!}

-- For instance, "snocV (a ∷ b ∷ []) c" should evaluate to "a ∷ b ∷ c ∷ []".
snocV : {A : Set} {n : ℕ} → Vector A n → A → Vector A (succ n)
snocV xs y = {!!}

-- For instance, "reverseV (a ∷ b ∷ c ∷ [])" should evaluate to "c ∷ b ∷ a ∷ []".
reverseV : {A : Set} {n : ℕ} → Vector A n → Vector A n
reverseV xs = {!!}

-- For instance, "concatV ((a ∷ b ∷ []) ∷ (c ∷ d ∷ []) ∷ [])" should evlauate to
-- "a ∷ b ∷ c ∷ d ∷ []".
concatV : {A : Set} {n m : ℕ} → Vector (Vector A n) m → Vector A (m · n)
concatV []         = []
concatV (xs ∷ xss) = xs ++ concatV xss
