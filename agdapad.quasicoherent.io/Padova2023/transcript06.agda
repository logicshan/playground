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
module _
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
