{-# OPTIONS --allow-unsolved-metas #-}
data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

data _⊎_ (A B : Set) : Set where
  left  : A → A ⊎ B
  right : B → A ⊎ B
-- A ⊎ A is NOT the same as A again.
-- For instance, if A contains n elements, then A ⊎ A contains 2n elements.

{-
  The idea of insertion sort:

  To sort 5 ∷ 2 ∷ 10 ∷ 1 ∷ [],

  start with []. Then successively insert additional elements at the correct position.

  []
  5 ∷ []
  2 ∷ 5 ∷ []
  2 ∷ 5 ∷ 10 ∷ []
  1 ∷ 2 ∷ 5 ∷ 10 ∷ []
-}

module Implementation
  {A : Set}
  (_≤_ : A → A → Set)
  (cmp? : (x y : A) → (x ≤ y) ⊎ (y ≤ x)) where
  -- For elements x, y : A, we are given a type "x ≤ y" of witnesses
  -- that x is less than or equal to y.
  
  -- "insert x ys" should return the same list as "ys", but with the element "x"
  -- inserted at the correct location.
  insert : A → List A → List A
  insert x []       = x ∷ []
  insert x (y ∷ ys) with cmp? x y
  ... | left  x≤y = x ∷ (y ∷ ys)
  ... | right y≤x = y ∷ insert x ys

  sort : List A → List A
  sort []       = []
  sort (x ∷ xs) = insert x (sort xs) 

  cheatsort : List A → List A
  cheatsort xs = []

module Verification₁
  {A : Set}
  (_≤_ : A → A → Set)
  (cmp? : (x y : A) → (x ≤ y) ⊎ (y ≤ x)) where

  open Implementation _≤_ cmp?

  data IsOrdered : List A → Set where
    empty     : IsOrdered []
    singleton : {x : A} → IsOrdered (x ∷ [])
    cons      : {x y : A} {ys : List A} → x ≤ y → IsOrdered (y ∷ ys) → IsOrdered (x ∷ (y ∷ ys))

  lemma₀ : (x y : A) (ys : List A) → y ≤ x → IsOrdered (y ∷ ys) → IsOrdered (y ∷ insert x ys)
  lemma₀ = {!!}

  lemma : (x : A) (ys : List A) → IsOrdered ys → IsOrdered (insert x ys)
  lemma x [] empty = singleton
  lemma x (y ∷ []) singleton with cmp? x y
  ... | left x≤y = cons x≤y singleton
  ... | right y≤x = cons y≤x singleton
  lemma x (y ∷ (z ∷ xs)) yzxs@(cons v p) with cmp? x y
  ... | left x≤y = cons x≤y (cons v p)
  ... | right y≤x = {!!}

  theorem : (xs : List A) → IsOrdered (sort xs)
  theorem []       = empty
  theorem (x ∷ xs) = lemma x (sort xs) (theorem xs)

  cheattheorem : (xs : List A) → IsOrdered (cheatsort xs)
  cheattheorem xs = empty

module CorrectByConstruction₁
  {A : Set}
  (_≤_ : A → A → Set)
  (-∞ : A)
  (min : {x : A} → -∞ ≤ x)
  (cmp? : (x y : A) → (x ≤ y) ⊎ (y ≤ x)) where

  -- "OList l" is the type of ordered lists where all elements are ≥ l.
  -- In other words, "OList l" is the type of ordered lists bounded from below by l.
  data OList (l : A) : Set where
    nil  : OList l
    cons : (x : A) → l ≤ x → OList x → OList l

  forget : {l : A} → OList l → List A
  forget nil           = []
  forget (cons x _ xs) = x ∷ forget xs

  insert : {l : A} → (x : A) → l ≤ x → OList l → OList l
  insert x l≤x nil             = cons x l≤x nil
  insert x l≤x (cons y l≤y ys) with cmp? x y
  ... | left  x≤y = cons x l≤x (cons y x≤y ys)
  ... | right y≤x = cons y l≤y (insert x y≤x ys)

  sort : List A → OList -∞
  sort []       = nil
  sort (x ∷ xs) = insert x min (sort xs)

  {-
  _ : {l : A} (xs : OList l) → sort (forget xs) ≡ xs
  _ = ?
  -}

