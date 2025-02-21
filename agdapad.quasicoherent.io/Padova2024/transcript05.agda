{-# OPTIONS --allow-unsolved-metas #-}
{-

  Plan for today:

  1. Solutions to exercises
  2. Modules
  3. Equational reasoning
  4. Correctness of algorithms

-}

-- ─────────────────────────────
-- ────[ BASIC DEFINITIONS ]────
-- ─────────────────────────────

open import Padova2024.EquationalReasoning
-- for _≡_, cong, symm, trans and also the convenient equational reasoning syntax

data Bool : Set where
  false : Bool
  true  : Bool

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

data ⊥ : Set where

¬ : Set → Set
¬ X = X → ⊥
-- In logic, the definition of "P is false" is "P implies a contradiction".

! : Bool → Bool
! false = true
! true  = false

_+_ : ℕ → ℕ → ℕ
zero   + b = b
succ a + b = succ (a + b)

_·_ : ℕ → ℕ → ℕ
zero   · b = zero
succ a · b = b + (a · b)

pred : ℕ → ℕ
pred zero     = zero
pred (succ a) = a


-- ────────────────────────────────────
-- ────[ GENERALITIES ON EQUALITY ]────
-- ────────────────────────────────────

-- EXERCISE: Prove that equal functions have equal values.
-- (The converse is a principle known as "function extensionality" which
-- can be postulated in Agda but is not assumed by default.)
equal→pwequal : {A B : Set} {f g : A → B} {x : A} → f ≡ g → f x ≡ g x
equal→pwequal p = {!!}

-- EXERCISE: Think about the expression "(⊥ ≡ ℕ)". Is it well-defined?
-- What would be its meaning?

-- EXERCISE: Fill in this hole. This lemma will be used below
-- in the proof that the double of any number is even.
transport : {A : Set} {x y : A} → (F : A → Set) → x ≡ y → F x → F y
transport F refl s = s
-- example usage:
-- given p : x ≡ y
-- and given q : Even x
-- we can conclude that y is even by using: transport Even p : Even y


-- ─────────────────────────────────
-- ────[ EQUALITIES OF NUMBERS ]────
-- ─────────────────────────────────

-- EXERCISE: Show that the predecessor of the successor of a number is that number again.
lemma-pred-succ : (a : ℕ) → pred (succ a) ≡ a
lemma-pred-succ a = {!!}

-- EXERCISE: Show that the two functions "even?" and "even?'" have the same values.
even? : ℕ → Bool
even? zero     = true
even? (succ n) = ! (even? n)

even?' : ℕ → Bool
even?' zero            = true
even?' (succ zero)     = false
even?' (succ (succ n)) = even?' n

lemma-even?-even?' : (a : ℕ) → even? a ≡ even?' a
lemma-even?-even?' a = {!!}

-- EXERCISE: Show that it is not the case that "succ (pred a) ≡ a" for all natural numbers a.
lemma-succ-pred : ((a : ℕ) → succ (pred a) ≡ a) → ⊥
lemma-succ-pred f = go (f zero)
  where
  go : succ zero ≡ zero → ⊥
  go ()
 
lemma-succ-pred'' : ((a : ℕ) → succ (pred a) ≡ a) → ⊥
lemma-succ-pred'' f with f zero
... | ()

-- an "anonymous module"
module _ (weird-assumption : (a : ℕ) → succ (pred a) ≡ a) where
  lemma-succ-pred''' : ⊥
  lemma-succ-pred''' with weird-assumption zero
  ... | ()

module _ (n : ℕ) (X : Set) (f : X → X) where
  -- ...

-- The following defines a type family "Positive : ℕ → Set" such that "Positive a" is the
-- type of witnesses that a is positive: The type "Positive zero" is empty
-- and the types "Positive (succ n)" are inhabited for every n.
data Positive : ℕ → Set where
  -- on purpose, we do NOT include this constructor: zero-is-positive : Positive zero
  succs-are-positive : {n : ℕ} → Positive (succ n)

-- EXERCISE: Fill in this hole.
lemma-succ-pred' : (a : ℕ) → Positive a → succ (pred a) ≡ a
lemma-succ-pred' (succ a) p = refl

-- EXERCISE: Verify the following two auxiliary lemmas, establishing that we
-- could have equivalently defined addition also by recursion on the second argument.
lemma-+-zero : (a : ℕ) → (a + zero) ≡ a
lemma-+-zero zero     = refl
lemma-+-zero (succ a) = cong succ (lemma-+-zero a)

lemma-+-succ : (a b : ℕ) → (a + succ b) ≡ succ (a + b)
lemma-+-succ zero     b = refl
lemma-+-succ (succ a) b = cong succ (lemma-+-succ a b)

-- EXERCISE: Verify that addition is commutative.
lemma-+-commutative : (a b : ℕ) → (a + b) ≡ (b + a)
lemma-+-commutative zero     b = symm (lemma-+-zero b)
lemma-+-commutative (succ a) b =
  trans (symm (lemma-+-succ a b))
    (trans (lemma-+-commutative a (succ b)) (symm (lemma-+-succ b a)))
-- that's a "write-only proof". Better to use equational reasoning:

lemma-+-commutative' : (a b : ℕ) → (a + b) ≡ (b + a)
lemma-+-commutative' zero     b = symm (lemma-+-zero b)
lemma-+-commutative' (succ a) b = begin
  succ a + b   ≡⟨⟩
  succ (a + b) ≡⟨ cong succ (lemma-+-commutative' a b) ⟩
  succ (b + a) ≡⟨ symm (lemma-+-succ b a) ⟩
  b + succ a   ∎

-- EXERCISE: Verify that addition is associative.
lemma-+-associative : (a b c : ℕ) → (a + (b + c)) ≡ ((a + b) + c)
lemma-+-associative a b c = {!!}

-- EXERCISE: Verify the distributive law. Similar as the implementation/proof
-- of lemma-+-commutative, the result will not be easy to read.
-- By a technique called "equational reasoning", to be introduced next time,
-- we will be able to clean up the proof.
lemma-distributive : (a b c : ℕ) → ((a + b) · c) ≡ ((a · c) + (b · c))
lemma-distributive a b c = {!!}

-- EXERCISE: Show that the double of any number is even.
data Even : ℕ → Set where
  base-even : Even zero
  step-even : {n : ℕ} → Even n → Even (succ (succ n))

lemma-double-even : (a : ℕ) → Even (a + a)
lemma-double-even a = {!!}


-- ───────────────────────────────
-- ────[ EQUALITIES OF LISTS ]────
-- ───────────────────────────────

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

exampleList : List ℕ
exampleList = zero ∷ (succ (succ zero) ∷ (zero ∷ []))
-- [zero, succ(succ(zero)), zero]

module _ {A : Set} where
  -- the "snoc" operation ("backwards cons"),
  -- i.e. append an element at the end
  _∷ʳ_ : List A → A → List A
  []       ∷ʳ y = y ∷ []
  (x ∷ xs) ∷ʳ y = x ∷ (xs ∷ʳ y)

  -- for instance, "reverse (a ∷ b ∷ c ∷ [])" is "c ∷ b ∷ a ∷ []".
  reverse : List A → List A
  reverse []       = []
  reverse (x ∷ xs) = reverse xs ∷ʳ x

  -- EXERCISE: Verify the following lemma.
  lemma-reverse-∷ʳ : (ys : List A) (x : A) → reverse (ys ∷ʳ x) ≡ (x ∷ reverse ys)
  lemma-reverse-∷ʳ ys x = {!!}

  lemma-reverse-reverse : (xs : List A) → reverse (reverse xs) ≡ xs
  lemma-reverse-reverse xs = {!!}

  -- EXERCISE: State and prove that _++_ on lists is associative.
  _++_ : List A → List A → List A
  []       ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  -- The following relation relates exactly those lists which have the same length
  -- and whose corresponding entries are equal.
  data _≈_ : List A → List A → Set where
    both-empty     : [] ≈ []
    both-same-cons : {xs ys : List A} {x y : A} → x ≡ y → xs ≈ ys → (x ∷ xs) ≈ (y ∷ ys)

  ≈-refl : (xs : List A) → xs ≈ xs
  ≈-refl []       = both-empty
  ≈-refl (x ∷ xs) = both-same-cons refl (≈-refl xs)

  -- EXERCISE: Show that equal lists are related by _≈_.
  ≡→≈ : {xs ys : List A} → xs ≡ ys → xs ≈ ys
  ≡→≈ refl = ≈-refl _

  -- EXERCISE: Show that related lists are equal.
  ≈→≡ : {xs ys : List A} → xs ≈ ys → xs ≡ ys
  ≈→≡ both-empty               = refl
  ≈→≡ (both-same-cons refl ps) = cong (_ ∷_) (≈→≡ ps)
  -- _∷_ : A → List A → List A
  -- x ∷_ : List A → List A          λ xs → x ∷ xs
  -- _∷ xs : A → List A              λ x  → x ∷ xs   (function (x) { return x ∷ xs; })
  -- (succ (succ zero) +_) : ℕ → ℕ   λ n → succ (succ zero) + n
  -- "section syntax"

  ≈→≡' : {xs ys : List A} → xs ≈ ys → xs ≡ ys
  ≈→≡' {[]}     {[]}     both-empty               = refl
  ≈→≡' {x ∷ xs} {x ∷ ys} (both-same-cons refl ps) = cong (x ∷_) (≈→≡' ps)

  -- EXERCISE: Regarding "Any" and "_∈_" from exercise02.agda, show that
  -- "Any (x ≡_) xs" implies "x ∈ xs" and conversely.


-- ─────────────────────────────────
-- ────[ EQUALITIES OF VECTORS ]────
-- ─────────────────────────────────

data Vector (A : Set) : ℕ → Set where
  []  : Vector A zero
  _∷_ : {n : ℕ} → A → Vector A n → Vector A (succ n)

drop : {A : Set} {n : ℕ} (k : ℕ) → Vector A (k + n) → Vector A n
drop zero      xs        = xs
drop (succ k') (x ∷ xs') = drop k' xs'

take : {A : Set} {n : ℕ} (k : ℕ) → Vector A (k + n) → Vector A k
take zero      xs        = []
take (succ k') (x ∷ xs') = x ∷ take k' xs'

_++ᵥ_ : {A : Set} {n m : ℕ} → Vector A n → Vector A m → Vector A (n + m)
[]        ++ᵥ ys = ys 
(x ∷ xs') ++ᵥ ys = x ∷ (xs' ++ᵥ ys) 

-- EXERCISE: Verify the following lemma.
lemma-take-drop : {A : Set} {n : ℕ} → (k : ℕ) → (xs : Vector A (k + n)) → (take k xs ++ᵥ drop k xs) ≡ xs
lemma-take-drop = {!!}

-- EXERCISE: Find out where the difficulty is in stating that _++ᵥ_ on
-- vectors is associative.


-- ─────────────────────────────────────
-- ────[ CORRECTNESS OF ALGORITHMS ]────
-- ─────────────────────────────────────

-- The following function determines whether two given numbers are equal.
eq? : ℕ → ℕ → Bool
eq? zero     zero     = true
eq? zero     (succ y) = false
eq? (succ x) zero     = false
eq? (succ x) (succ y) = eq? x y

-- Two approaches to correctness verification:
-- (1) Implement first, then verify correctness separately
-- (2) Correct by construction

-- Approach (1)
lemma₁ : (x y : ℕ) → eq? x y ≡ true → x ≡ y
lemma₁ zero     zero     p = refl
lemma₁ (succ x) (succ y) p = cong succ (lemma₁ x y p)

lemma₂ : (x y : ℕ) → x ≡ y → eq? x y ≡ true
lemma₂ = {!!}

-- Approach (2)
data _⊎_ (A B : Set) : Set where
  left  : A → A ⊎ B
  right : B → A ⊎ B
-- "A ⊎ B" is the disjoint union of the types "A" and "B".
-- Its inhabitants are:
-- 1. For every x : A, we have left  x : A ⊎ B.
-- 2. For every y : B, we have right y : A ⊎ B.


dec : (x y : ℕ) → (x ≡ y) ⊎ (¬ (x ≡ y))   -- \uplus \u+ ⊎
dec zero     zero     = left refl
dec zero     (succ y) = right {!!}
dec (succ x) zero     = right {!!}
dec (succ x) (succ y) with dec x y
... | left  p = left (cong succ p)
... | right p = right {!!}
