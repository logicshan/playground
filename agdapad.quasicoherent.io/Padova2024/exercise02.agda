{-# OPTIONS --allow-unsolved-metas #-}
{-
  AGDA IN PADOVA 2024
  Exercise sheet 2

  ┌─ SHORTCUTS ───────────────────────┐    ┌─ BACKSLASH CHARACTERS ─┐
  │ C-c C-l   = load file             │    │ \bN    = ℕ             │
  │ C-c C-c   = case split            │    │ \alpha = α             │
  │ C-c C-SPC = check hole            │    │ \to    = →             │
  │ C-c C-,   = see context           │    │ \cdot  = ·             │
  │ C-c C-.   = see context and goal  │    │ \::    = ∷             │
  │ C-c C-d   = display type          │    │ \==    = ≡             │
  │ C-c C-v   = evaluate expression   │    └────────────────────────┘
  │ C-z       = enable Vi keybindings │    Use M-x describe-char to
  │ C-x C-+   = increase font size    │    lookup input method for
  └───────────────────────────────────┘    symbol under cursor.

  You can open this file in an Agdapad session by pressing C-x C-f ("find file")
  and then entering the path to this file: ~/Padova2024/exercise02.agda.
  As this file is read-only, you can then save a copy of this file to your personal
  directory and edit that one: File > Save As... For instance, you can save this file
  as ~/solutions02.agda.
-}


-- ─────────────────────────────
-- ────[ BASIC DEFINITIONS ]────
-- ─────────────────────────────

data Bool : Set where
  false : Bool
  true  : Bool

_&&_ : Bool → Bool → Bool
false && b     = false
true  && false = false
true  && true  = true

!_ : Bool → Bool
! false = true
! true  = false

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero   + b = b
succ a + b = succ (a + b)

_·_ : ℕ → ℕ → ℕ
zero   · b = zero
succ a · b = b + (a · b)

data ⊥ : Set where


-- ──────────────────────────────────
-- ────[ PROGRAMMING WITH LISTS ]────
-- ──────────────────────────────────

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

-- EXERCISE: Define a function which sums the numbers of a given list.
sum : List ℕ → ℕ
sum [] = zero
sum (x ∷ xs) = x + (sum xs)

-- EXERCISE: Define a function which computes the length of a given list.
length : List ℕ → ℕ
length [] = zero
length (x ∷ xs) = succ (length xs)

-- EXERCISE: Define the "map" function.
-- For instance, "map f (x ∷ y ∷ z ∷ []) = f x ∷ f y ∷ f z ∷ []".
map : {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs


-- ────────────────────────────────────
-- ────[ PROGRAMMING WITH VECTORS ]────
-- ────────────────────────────────────

data Vector (A : Set) : ℕ → Set where
  []  : Vector A zero
  _∷_ : {n : ℕ} → A → Vector A n → Vector A (succ n)

infixr 10 _∷_

-- EXERCISE: Define a function which computes the length of a given vector.
-- There are two possible implementations, one which runs in constant time
-- and one which runs in linear time.
lengthV : {n : ℕ} {A : Set} → Vector A n → ℕ
lengthV {n} = λ _ → n

lengthV' : {n : ℕ} {A : Set} → Vector A n → ℕ
lengthV' [] = zero
lengthV' (x ∷ v) = succ (lengthV' v)

-- EXERCISE: Define the "map" function for vectors.
-- For instance, "map f (x ∷ y ∷ z ∷ []) = f x ∷ f y ∷ f z ∷ []".
mapV : {n : ℕ} {A B : Set} → (A → B) → Vector A n → Vector B n
mapV f [] = []
mapV f (x ∷ xs) = f x ∷ mapV f xs

-- EXERCISE: Define these vector functions.
-- For instance, "zipWithV f (x ∷ y ∷ []) (a ∷ b ∷ [])" should evaluate to "f x a ∷ f y b ∷ []".
zipWithV : {A B C : Set} {n : ℕ} → (A → B → C) → Vector A n → Vector B n → Vector C n
zipWithV f [] [] = []
zipWithV f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWithV f xs ys

-- For instance, "dropV (succ zero) (a ∷ b ∷ c ∷ [])" should evaluate to "b ∷ c ∷ []".
dropV : {A : Set} {n : ℕ} (k : ℕ) → Vector A (k + n) → Vector A n
dropV zero xs = xs
dropV (succ k) (_ ∷ xs) = dropV k xs

-- For instance, "takeV (succ zero) (a ∷ b ∷ c ∷ [])" should evaluate to "a ∷ []".
takeV : {A : Set} {n : ℕ} (k : ℕ) → Vector A (k + n) → Vector A k
takeV zero xs = []
takeV (succ n) (x ∷ xs) = x ∷ takeV n xs

-- For instance, "(a ∷ b ∷ []) ++ (c ∷ d ∷ [])" should evaluate to "a ∷ b ∷ c ∷ d ∷ []".
_++_ : {A : Set} {n m : ℕ} → Vector A n → Vector A m → Vector A (n + m)
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

-- For instance, "snocV (a ∷ b ∷ []) c" should evaluate to "a ∷ b ∷ c ∷ []".
snocV : {A : Set} {n : ℕ} → Vector A n → A → Vector A (succ n)
snocV [] y = y ∷ []
snocV (x ∷ xs) y = x ∷ snocV xs y

-- For instance, "reverseV (a ∷ b ∷ c ∷ [])" should evaluate to "c ∷ b ∷ a ∷ []".
reverseV : {A : Set} {n : ℕ} → Vector A n → Vector A n
reverseV [] = []
reverseV (x ∷ xs) = snocV (reverseV xs) x

-- For instance, "concatV ((a ∷ b ∷ []) ∷ (c ∷ d ∷ []) ∷ [])" should evaluate to
-- "a ∷ b ∷ c ∷ d ∷ []".
concatV : {A : Set} {n m : ℕ} → Vector (Vector A m) n → Vector A (n · m)
concatV {n = zero} xss = []
concatV {n = succ n} (xs ∷ xss) = xs ++ (concatV xss)


-- ────────────────────────────────────────────
-- ────[ MORE PROOFS WITH NATURAL NUMBERS ]────
-- ────────────────────────────────────────────

-- "Even n" is the type of witnesses that "n" is even.
data Even : ℕ → Set where
  base-even : Even zero
  step-even : {n : ℕ} → Even n → Even (succ (succ n))

-- "Odd n" is the type of witnesses that "n" is odd.
data Odd : ℕ → Set where
  base-odd : Odd (succ zero)
  step-odd : {n : ℕ} → Odd n → Odd (succ (succ n))

-- EXERCISE: Show that the sum of even numbers is even.
lemma-sum-even : {a b : ℕ} → Even a → Even b → Even (a + b)
lemma-sum-even base-even base-even = base-even
lemma-sum-even base-even (step-even eb) = step-even eb
lemma-sum-even (step-even ea) base-even = step-even (lemma-sum-even ea base-even)
lemma-sum-even (step-even ea) (step-even eb) = step-even (lemma-sum-even ea (step-even eb))

-- EXERCISE: Show that the successor of an even number is odd and vice versa.
lemma-succ-even : {a : ℕ} → Even a → Odd (succ a)
lemma-succ-even base-even = base-odd
lemma-succ-even (step-even ea) = step-odd (lemma-succ-even ea)

lemma-succ-odd : {a : ℕ} → Odd a → Even (succ a)
lemma-succ-odd base-odd = step-even base-even
lemma-succ-odd (step-odd oa) = step-even (lemma-succ-odd oa)

-- EXERCISE: Show that the sum of odd numbers is even.
lemma-sum-odd : {a b : ℕ} → Odd a → Odd b → Even (a + b)
lemma-sum-odd base-odd base-odd = step-even base-even
lemma-sum-odd base-odd (step-odd ob) = lemma-sum-odd (step-odd base-odd) ob
lemma-sum-odd (step-odd oa) base-odd = step-even (lemma-sum-odd oa base-odd)
lemma-sum-odd (step-odd oa) (step-odd ob) = step-even (lemma-sum-odd oa (step-odd ob))

-- EXERCISE: Show that the sum of an odd number with an even number is odd.
lemma-sum-mixed : {a b : ℕ} → Odd a → Even b → Odd (a + b)
lemma-sum-mixed base-odd base-even = base-odd
lemma-sum-mixed base-odd (step-even eb) = lemma-sum-mixed (step-odd base-odd) eb
lemma-sum-mixed (step-odd oa) base-even = step-odd (lemma-sum-mixed oa base-even)
lemma-sum-mixed (step-odd oa) (step-even eb) = step-odd (lemma-sum-mixed oa (step-even eb))

-- EXERCISE: Show that it cannot be that a number is both even and odd.
lemma-odd-and-even : {a : ℕ} → Odd a → Even a → ⊥
lemma-odd-and-even base-odd ()
lemma-odd-and-even (step-odd p) (step-even q) = lemma-odd-and-even p q

-- EXERCISE: Show that every number is even or odd.
data _⊎_ (A B : Set) : Set where
  left  : A → A ⊎ B
  right : B → A ⊎ B
-- For instance, if x : A, then left x : A ⊎ B.

lemma-even-odd : (a : ℕ) → Even a ⊎ Odd a
lemma-even-odd zero = left base-even
lemma-even-odd (succ a) with lemma-even-odd a
... | left e = right (lemma-succ-even e)
... | right o = left (lemma-succ-odd o)


-- ─────────────────────────────
-- ────[ PROOFS WITH LISTS ]────
-- ─────────────────────────────

-- EXERCISE: Define a predicate "AllEven" for lists of natural numbers
-- such that "AllEven xs" is inhabited if and only if all entries of the list "xs" are even.
-- By convention, the empty list counts as consisting of even-only elements.
data AllEven : List ℕ → Set where
  {- supply appropriate clauses here -}
--  AllEvenNil : AllEven []
--  AllEvenCons : {a : ℕ}{es : List ℕ} → Even a → AllEven es → AllEven (a ∷ es)
  [] : AllEven []
  _∷_ : {a : ℕ}{es : List ℕ} → Even a → AllEven es → AllEven (a ∷ es)



lemma-sum-of-even-list-is-even : {xs : List ℕ} → AllEven xs → Even (sum xs)
lemma-sum-of-even-list-is-even [] = base-even
lemma-sum-of-even-list-is-even (x ∷ p) = lemma-sum-even x (lemma-sum-of-even-list-is-even p)

-- EXERCISE: Define a predicate "All P" for lists of elements of some type A
-- and predicates "P : A → Set" such that "All P xs" is inhabited if
-- and only if all entries of the list "xs" satisfy P.
-- The special case "All Even" should coincide with the predicate
-- "AllEven" from the previous exercise.
data All {A : Set} (P : A → Set) : List A → Set where
  {- give appropriate clauses -}
  []  : All P []
  _∷_ : {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)  


-- EXERCISE: Define a predicate "Any P" for lists of elements of some type A
-- and predicates "P : A → Set" such that "Any P xs" is inhabited if
-- and only if at least one entry of the list "xs" satisfies P.
data Any {A : Set} (P : A → Set) : List A → Set where
  {- give appropriate clauses -}
  here  : {x : A} {xs : List A} → P x → Any P (x ∷ xs)
  there : {x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)

-- EXERCISE: Define a relation "_∈_" such that "x ∈ ys" is the type
-- of witnesses that x occurs in the list ys.
data _∈_ {A : Set} : A → List A → Set where
  {- give appropriate clauses -}
  here  : {x : A} {ys : List A} → x ∈ (x ∷ ys)
  there : {x y : A} {ys : List A} → x ∈ ys → x ∈ (y ∷ ys)
