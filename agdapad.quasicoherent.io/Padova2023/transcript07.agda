{-# OPTIONS --allow-unsolved-metas #-}
{-
  Task: Implement insertion sort.

  For instance,

      sort (5 ∷ 3 ∷ 10 ∷ 1 ∷ [])

  will yield the list

      1 ∷ 3 ∷ 5 ∷ 10 ∷ [].
-}

data _⊎_ (X Y : Set) : Set where
  left  : X → X ⊎ Y
  right : Y → X ⊎ Y

-- "Let a set A be fixed."
module Implementation
  (A : Set)
  (_≤_ : A → A → Set)   -- "x ≤ y" is the type of
                        -- witnesses that x is less than
                        -- or equal to y
  (cmp? : (x y : A) → (x ≤ y) ⊎ (y ≤ x)) where
  -- For instance, in the case that "A" is the type ℕ
  -- and "_≤_" is the usual ordering relation,
  -- "cmp? 5 10" should be something of the form "left ...",
  -- "cmp? 10 5" should be something of the form "right ...".

  data List : Set where
    []  : List
    _∷_ : A → List → List

  -- If the list "ys" is already sorted (ascendingly),
  -- the list "insert x ys" should be the same as "ys",
  -- but with the element "x" inserted at the appropriate
  -- location.
  -- For instance: "insert 5 (2 ∷ 10 ∷ 20 ∷ [])" should
  -- yield "2 ∷ 5 ∷ 10 ∷ 20 ∷ []".
  insert : A → List → List
  insert x []       = x ∷ []
  insert x (y ∷ ys) with cmp? x y
  ... | left  x≤y = x ∷ (y ∷ ys)
  ... | right y≤x = y ∷ insert x ys
  -- There are two options: The correct result might by
  -- (a)    x ∷ y ∷ ys       (this is correct if x ≤ y)
  -- (b)    y ∷ insert x ys  (this is correct if y ≤ x)

  sort : List → List
  sort []       = []
  sort (x ∷ xs) = insert x (sort xs)

module Verification
  (A : Set)
  (_≤_ : A → A → Set)   -- "x ≤ y" is the type of
                        -- witnesses that x is less than
                        -- or equal to y
  (cmp? : (x y : A) → (x ≤ y) ⊎ (y ≤ x)) where

  open Implementation A _≤_ cmp?

  -- The type "IsSorted xs" should consist of witnesses that
  -- the list "xs" is sorted.
  data IsSorted : List → Set where
    empty     : IsSorted []
    singleton : {x : A} → IsSorted (x ∷ [])
    cons      : {x y : A} {ys : List} → IsSorted (y ∷ ys) → x ≤ y → IsSorted (x ∷ (y ∷ ys))

  lemma₀ : (x y : A) (ys : List) → y ≤ x → IsSorted (y ∷ ys) → IsSorted (y ∷ insert x ys)
  lemma₀ = {!!}

  lemma : (x : A) (ys : List) → IsSorted ys → IsSorted (insert x ys)
  lemma x []       p = singleton
  lemma x (y ∷ ys) p with cmp? x y
  ... | left  x≤y = cons {x} {y} {ys} p x≤y
  ... | right y≤x = lemma₀ x y ys y≤x p

  -- Logical reading: For every list "xs", it is a fact that "sort xs" is sorted.
  -- Computational reading: "theorem" is a function which reads a list "xs"
  -- as input and outputs a witness that "sort xs" is sorted.
  theorem : (xs : List) → IsSorted (sort xs)
  theorem []       = empty
  theorem (x ∷ xs) = lemma x (sort xs) (theorem xs)

  cheatsort : List → List
  cheatsort xs = []

  cheattheorem : (xs : List) → IsSorted (cheatsort xs)
  cheattheorem xs = empty

module CorrectByConstruction
  (A : Set)
  (_≤_ : A → A → Set)   -- "x ≤ y" is the type of
                        -- witnesses that x is less than
                        -- or equal to y
  (-∞ : A)
  (is-min : {x : A} → -∞ ≤ x)
  (cmp? : (x y : A) → (x ≤ y) ⊎ (y ≤ x)) where

  data List : Set where
    []  : List
    _∷_ : A → List → List

  -- "SList l" is the type of sorted lists whose elements are bounded
  -- from below by l. For instance, the numbers 10, 20 and 30 are
  -- bounded from below by 5.
  data SList (l : A) : Set where
    nil  : SList l
    cons : (x : A) → (xs : SList x) → l ≤ x → SList l

  insert : {l : A} (x : A) (ys : SList l) → l ≤ x → SList l
  insert x nil             l≤x = cons x nil l≤x
  insert x (cons y ys l≤y) l≤x with cmp? x y
  ... | left  x≤y = cons x (cons y ys x≤y) l≤x
  ... | right y≤x = cons y (insert x ys y≤x) l≤y

  sort : List → SList -∞
  sort []       = nil
  sort (x ∷ xs) = insert x (sort xs) is-min
