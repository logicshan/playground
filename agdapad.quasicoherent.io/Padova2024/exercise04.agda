{-# OPTIONS --allow-unsolved-metas #-}
{-
  AGDA IN PADOVA 2024
  Exercise sheet 4

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
  and then entering the path to this file: ~/Padova2024/exercise04.agda.
  As this file is read-only, you can then save a copy of this file to your personal
  directory and edit that one: File > Save As... For instance, you can save this file
  as ~/solutions04.agda.
-}


-- ─────────────────────────────
-- ────[ BASIC DEFINITIONS ]────
-- ─────────────────────────────

data Bool : Set where
  false : Bool
  true  : Bool

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

data ⊥ : Set where

infixr 5 _∷_
data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infix 3 ¬_
¬_ : Set → Set
¬ X = X → ⊥

infixr 1 _⊎_
data _⊎_ (A B : Set) : Set where
  left  : A → A ⊎ B
  right : B → A ⊎ B

infix 5 _≡_

data _≡_ {X : Set} : X → X → Set where
  refl : {a : X} → a ≡ a

cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

symm : {A : Set} {x y : A} → x ≡ y → y ≡ x
symm refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

_+_ : ℕ → ℕ → ℕ
zero   + b = b
succ a + b = succ (a + b)

_·_ : ℕ → ℕ → ℕ
zero   · b = zero
succ a · b = b + (a · b)


-- ─────────────────────────────────────
-- ────[ CORRECTNESS OF ALGORITHMS ]────
-- ─────────────────────────────────────

module _ where private
  eq? : ℕ → ℕ → Bool
  eq? zero     zero     = true
  eq? zero     (succ _) = false
  eq? (succ _) zero     = false
  eq? (succ x) (succ y) = eq? x y

  -- EXERCISE. Verify that "eq?" works as intended by filling in the next two holes.
  lemma-correct₁ : (x y : ℕ) → eq? x y ≡ true → x ≡ y
  lemma-correct₁ = {!!}

  lemma-correct₂ : (x y : ℕ) → x ≡ y → eq? x y ≡ true
  lemma-correct₂ = {!!}

  -- EXERCISE. Now follow the approach "correct by construction", by disregarding
  -- the implementation "eq?" and its correctness lemmas and instead filling in the
  -- next hole.
  dec : (x y : ℕ) → (x ≡ y) ⊎ ¬ (x ≡ y)
  dec x y = {!!}

module _ where private
  data _≤_ : ℕ → ℕ → Set where
    base : {y : ℕ} → zero ≤ y
    step : {x y : ℕ} → x ≤ y → succ x ≤ succ y

  -- EXERCISE. Implement the function "cmp?" which should return "true"
  -- if the first argument is smaller than or equal to the second argument,
  -- and "false" else. For instance "cmp? zero (succ zero)" should be "true".
  cmp? : ℕ → ℕ → Bool
  cmp? x y = {!!}

  -- EXERCISE. Verify the correctness of "cmp?" as follows.
  lemma-correct₁ : (x y : ℕ) → cmp? x y ≡ true → x ≤ y
  lemma-correct₁ = {!!}

  lemma-correct₂ : (x y : ℕ) → x ≤ y → cmp? x y ≡ true
  lemma-correct₂ = {!!}

  -- EXERCISE. Now with "correct by construction".
  dec : (x y : ℕ) → (x ≤ y) ⊎ (y ≤ x)
  dec = {!!}


-- ────────────────────────
-- ────[ DECIDABILITY ]────
-- ────────────────────────

-- A proposition is decidable iff it holds or if its converse holds.
data Dec (A : Set) : Set where
  yes : A   → Dec A
  no  : ¬ A → Dec A

-- EXERCISE. For every pair of numbers x, y, verify that "x ≡ y" is decidable.
dec-eq : (x y : ℕ) → Dec (x ≡ y)
dec-eq x y = {!!}

-- EXERCISE. Prove that, if "X" and "Y" are decidable, so is "X → Y".
dec-→ : {X Y : Set} → Dec X → Dec Y → Dec (X → Y)
dec-→ = {!!}


-- ──────────────────────────
-- ────[ INSERTION SORT ]────
-- ──────────────────────────

-- EXERCISE: Implement insertion sort, by filling in the two holes below.
module Implementation
  {A : Set}
  (_≤_ : A → A → Set)
  (cmp? : (x y : A) → (x ≤ y) ⊎ (y ≤ x)) where

  -- Given an ordered list "ys", "insert x ys" should be the same as "ys",
  -- but with "x" inserted at the correct place to ensure that the
  -- resulting list is again ordered.
  insert : (x : A) → List A → List A
  insert = {!!}

  sort : List A → List A
  sort = {!!}

module Verification₂ {A : Set} (_≤_ : A → A → Set) (cmp : (x y : A) → (x ≤ y) ⊎ (y ≤ x)) where
  open Implementation _≤_ cmp

  -- "(x ◂ ys ↝ xys)" should be the type of witnesses that inserting "x" into "ys" somewhere
  -- yields the list "xys".     -- ◂\t  ↝\leadsto
  data _◂_↝_ : A → List A → List A → Set where
    here  : {x : A} {xs : List A} → x ◂ xs ↝ (x ∷ xs)
    there : {x y : A} {ys xys : List A} → x ◂ ys ↝ xys → x ◂ (y ∷ ys) ↝ (y ∷ xys)

  -- "IsPerm xs ys" should be the type of witnesses that the two lists "xs" and "ys"
  -- are permutations of each other, that is, contain exactly the same elements just
  -- perhaps in different order.
  data IsPerm : List A → List A → Set where
    empty : IsPerm [] []
    cons  : {x : A} {xs ys xys : List A} → (x ◂ ys ↝ xys) → IsPerm xs ys → IsPerm (x ∷ xs) xys

  -- EXERCISE: Make sense of the preceding two definitions.

  -- EXERCISE: Fill in this hole.
  example : (x y z : A) → IsPerm (x ∷ y ∷ z ∷ []) (z ∷ x ∷ y ∷ [])
  example x y z = {!!}

  -- EXERCISE: Verify this lemma.
  lemma : (x : A) (ys : List A) → x ◂ ys ↝ insert x ys
  lemma x ys = {!!}

  -- EXERCISE: Deduce this theorem.
  theorem : (xs : List A) → IsPerm xs (sort xs)
  theorem xs = {!!}

-- A variant of what we did in the lecture.
module CorrectByConstruction₀
  {A : Set} (_≤_ : A → A → Set)
  (max : A) (≤max : {x : A} → x ≤ max)
  (cmp : (x y : A) → (x ≤ y) ⊎ (y ≤ x)) where

  -- "OList l" is the type of ordered lists of elements of A.
  data OList : Set
  -- The usual "where" is missing because the definition of "OList"
  -- mutually depends on the following function extracting the head
  -- of an ordered list.

  head : OList → A
  -- This is just a declaration. The definition will follow once
  -- the constructors of "OList" have been introduced.

  data OList where
    nil  : OList
    cons : (x : A) (xs : OList) → x ≤ head xs → OList

  head nil           = max
  head (cons x xs _) = x

  insert : A → OList → OList
  insert x ys = {!!}

  sort : List A → OList
  sort []       = nil
  sort (x ∷ xs) = insert x (sort xs)

module CorrectByConstruction₂
  {A : Set} (_≤_ : A → A → Set)
  (min : A) (min≤ : {x : A} → min ≤ x)
  (cmp : (x y : A) → (x ≤ y) ⊎ (y ≤ x)) where

  -- As in module Verification₂ above
  data _◂_↝_ : A → List A → List A → Set where
    here  : {x : A} {xs : List A} → x ◂ xs ↝ (x ∷ xs)
    there : {x y : A} {ys xys : List A} → x ◂ ys ↝ xys → x ◂ (y ∷ ys) ↝ (y ∷ xys)

  -- "OPList l xs" is the type of ordered lists whose elements are bounded from below by l
  -- and which are permutations of xs
  
  data OPList (l : A) : List A → Set where
    nil  : OPList l []
    cons : {ys xys : List A} → (x : A) → OPList x ys → l ≤ x → (x ◂ ys ↝ xys) → OPList l xys

  -- EXERCISE: Fill this in.
  insert : {!!}
  insert = {!!}

  -- EXERCISE: Fill this in.
  sort : (xs : List A) → OPList min xs
  sort = {!!}

-- The modules CorrectByConstruction₁ and CorrectByConstruction₂ require a least element "min".
-- EXERCISE: Define for any type A together with a relation _≤_ on A a new
-- type "* A" which is A adjoined by a new least element -∞. Use
-- this construction to get rid of the additional requirement.
data *_ (A : Set) : Set where
  -- EXERCISE: fill this in

module Lift {A : Set} (_≤_ : A → A → Set) where
  -- EXERCISE: Define a relation _≼_ on * A.
  -- EXERCISE: Verify that there is a least element for this relation.
  -- EXERCISE: Verify that if we have a function cmp for A then we also have such a function for * A.
  -- EXERCISE: Define a correct-by-construction sort function for A, by using * A.
