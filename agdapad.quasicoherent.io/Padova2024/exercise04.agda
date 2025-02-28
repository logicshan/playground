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
{-# BUILTIN NATURAL ℕ #-}

data ⊥ : Set where

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

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
  lemma-correct₁ zero zero p = refl
  lemma-correct₁ (succ x) (succ y) p = cong succ (lemma-correct₁ x y p)

  lemma-correct₂ : (x y : ℕ) → x ≡ y → eq? x y ≡ true
  lemma-correct₂ zero     .zero     refl = refl
  lemma-correct₂ (succ x) .(succ x) refl = lemma-correct₂ x x refl

  -- EXERCISE. Now follow the approach "correct by construction", by disregarding
  -- the implementation "eq?" and its correctness lemmas and instead filling in the
  -- next hole.
  dec : (x y : ℕ) → (x ≡ y) ⊎ ¬ (x ≡ y)
  dec zero     zero     = left refl
  dec zero     (succ y) = right λ ()
  dec (succ x) zero     = right λ ()
  dec (succ x) (succ y) with dec x y
  ... | left p = left (cong succ p)
  ... | right p = right λ q → p (lemma x y q)
    where
    lemma : (x y : ℕ) → succ x ≡ succ y → x ≡ y
    lemma zero zero refl = refl
    lemma zero (succ y) ()
    lemma (succ x) zero ()
    lemma (succ x) (succ .x) refl = refl

module ℕ-≤ where
  data _≤_ : ℕ → ℕ → Set where
    base : {y : ℕ} → zero ≤ y
    step : {x y : ℕ} → x ≤ y → succ x ≤ succ y

  -- EXERCISE. Implement the function "cmp?" which should return "true"
  -- if the first argument is smaller than or equal to the second argument,
  -- and "false" else. For instance "cmp? zero (succ zero)" should be "true".
  cmp? : ℕ → ℕ → Bool
  cmp? zero zero = true
  cmp? zero (succ y) = true
  cmp? (succ x) zero = false
  cmp? (succ x) (succ y) = cmp? x y

  -- EXERCISE. Verify the correctness of "cmp?" as follows.
  lemma-correct₁ : (x y : ℕ) → cmp? x y ≡ true → x ≤ y
  lemma-correct₁ zero zero p = base
  lemma-correct₁ zero (succ y) p = base
  lemma-correct₁ (succ x) (succ y) p = step (lemma-correct₁ x y p)

  lemma-correct₂ : (x y : ℕ) → x ≤ y → cmp? x y ≡ true
  lemma-correct₂ zero zero base = refl
  lemma-correct₂ zero (succ y) base = refl
  lemma-correct₂ (succ x) zero ()
  lemma-correct₂ (succ x) (succ y) (step p) = lemma-correct₂ x y p

  -- EXERCISE. Now with "correct by construction".
  dec : (x y : ℕ) → (x ≤ y) ⊎ (y ≤ x)
  dec zero zero = left base
  dec zero (succ y) = left base
  dec (succ x) zero = right base
  dec (succ x) (succ y) with dec x y
  ... | left p = left (step p)
  ... | right p = right (step p)


-- ────────────────────────
-- ────[ DECIDABILITY ]────
-- ────────────────────────

-- A proposition is decidable iff it holds or if its converse holds.
data Dec (A : Set) : Set where
  yes : A   → Dec A
  no  : ¬ A → Dec A

-- EXERCISE. For every pair of numbers x, y, verify that "x ≡ y" is decidable.
dec-eq : (x y : ℕ) → Dec (x ≡ y)
dec-eq zero zero = yes refl
dec-eq zero (succ y) = no λ ()
dec-eq (succ x) zero = no λ ()
dec-eq (succ x) (succ y) with dec-eq x y
... | yes p = yes (cong succ p)
... | no p = no λ q → p (lemma x y q)
  where
  lemma : (x y : ℕ) → succ x ≡ succ y → x ≡ y
  lemma zero zero refl = refl
  lemma zero (succ y) ()
  lemma (succ x) zero ()
  lemma (succ x) (succ .x) refl = refl

-- EXERCISE. Prove that, if "X" and "Y" are decidable, so is "X → Y".
dec-→ : {X Y : Set} → Dec X → Dec Y → Dec (X → Y)
dec-→ (yes _) (yes y) = yes λ _ → y
dec-→ (yes x) (no ¬y) = no λ f → ¬y (f x)
dec-→ (no _) (yes y) = yes (λ _ → y)
dec-→ (no ¬x) (no _) = yes λ x → ⊥-elim (¬x x)


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
  insert x [] = x ∷ []
  insert x L@(y ∷ ys) with cmp? x y
  ... | left x≤y = x ∷ L
  ... | right y≤x = y ∷ insert x ys

  sort : List A → List A
  sort [] = []
  sort (x ∷ xs) = insert x (sort xs) 

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
  example x y z = cons (there here) (cons (there here) (cons here empty))

  -- EXERCISE: Verify this lemma.
  lemma : (x : A) (ys : List A) → x ◂ ys ↝ insert x ys
  lemma x [] = here
  lemma x (y ∷ ys) with cmp x y
  ... | left x≤y = here
  ... | right y≤x = there (lemma x ys)

  -- EXERCISE: Deduce this theorem.
  theorem : (xs : List A) → IsPerm xs (sort xs)
  theorem [] = empty
  theorem (x ∷ xs) = cons (lemma x (sort xs)) (theorem xs)

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
  insert x nil = cons x nil ≤max
  insert x OL@(cons y ys p) with cmp x y
  ... | left x≤y = cons x OL x≤y
  ... | right y≤x = cons y (insert x ys) (lemma x y ys y≤x p)
    where
    lemma : (x y : A) → (ys : OList) → y ≤ x → y ≤ head ys → y ≤ head (insert x ys)
    lemma x y nil p q = p
    lemma x y (cons x₁ ys x₂) p q with cmp x x₁
    ... | left x₃ = {!!}
    ... | right x₃ = {!!}
  

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
  insert : {l : A} {xs : List A} → (x : A) → l ≤ x → OPList l xs → OPList l (x ∷ xs)
  insert x l≤x nil = cons x nil l≤x here
  insert x l≤x (cons y ys l≤y p) with cmp x y
  ... | left x≤y = cons x (cons y ys x≤y p) l≤x here
  ... | right y≤x = cons y (insert x y≤x ys) l≤y (there p)


  -- EXERCISE: Fill this in.
  sort : (xs : List A) → OPList min xs
  sort [] = nil
  sort (x ∷ xs) = insert x min≤ (sort xs)

  forget : {l : A} → {xs : List A} → OPList l xs → List A
  forget nil = []
  forget (cons x xs _ _) = x ∷ forget xs


module _ where

  open ℕ-≤
  open module SortListℕ = CorrectByConstruction₂ {ℕ} _≤_ 0 base dec

  o1 : OPList 0 (2 ∷ 1 ∷ 0 ∷ [])
  o1 = cons 0
        (cons 1
         (cons 2 nil
          (step base) here)
         base (there here))
        base
        (there
         (there here))

  o2 : OPList 0 (1 ∷ 2 ∷ 0 ∷ [])
  o2 = cons 0
        (cons 1
         (cons 2 nil
          (step base) here)
         base here)
        base
        (there
         (there here))


  s : List ℕ
  s = forget (sort (2 ∷ 1 ∷ 0 ∷ []))

  _ : s ≡ (0 ∷ 1 ∷ 2 ∷ [])
  _ = refl


-- The modules CorrectByConstruction₁ and CorrectByConstruction₂ require a least element "min".
-- EXERCISE: Define for any type A together with a relation _≤_ on A a new
-- type "* A" which is A adjoined by a new least element -∞. Use
-- this construction to get rid of the additional requirement.
data *_ (A : Set) : Set where
  -- EXERCISE: fill this in
  -∞ : * A
  ⋆  : A → * A


module Lift {A : Set} (_≤_ : A → A → Set) (cmp : (x y : A) → (x ≤ y) ⊎ (y ≤ x)) where
  -- EXERCISE: Define a relation _≼_ on * A.
  -- EXERCISE: Verify that there is a least element for this relation.
  -- EXERCISE: Verify that if we have a function cmp for A then we also have such a function for * A.
  -- EXERCISE: Define a correct-by-construction sort function for A, by using * A.
  data _≼_ : * A → * A → Set where
     bot : {*x : * A} → -∞ ≼ *x
     up≤   : {x y : A} → x ≤ y → ⋆ x ≼ ⋆ y

  min : * A
  min = -∞
    
  min≼ : {x : * A} → min ≼ x
  min≼ = bot

  cmp≼ : (cmp : (x y : A) → (x ≤ y) ⊎ (y ≤ x)) → (s t : * A) → (s ≼ t) ⊎ (t ≼ s)
  cmp≼ cmp -∞ -∞ = left bot
  cmp≼ cmp -∞ (⋆ x) = left bot
  cmp≼ cmp (⋆ x) -∞ = right bot
  cmp≼ cmp (⋆ x) (⋆ y) with cmp x y
  ... | left x≤y = left (up≤ x≤y)
  ... | right y≤x = right (up≤ y≤x)

  data OList (l : * A) : Set where
    nil  : OList l
    cons : (x : * A) → l ≼ x → OList x → OList l

  insert : {l : * A} → (x : * A) → l ≼ x → OList l → OList l
  insert x l≼x nil = cons x l≼x nil
  insert x l≼x (cons y l≼y ys) with cmp≼ cmp x y
  ... | left x≼y = cons x l≼x (cons y x≼y ys)
  ... | right y≼x = cons y l≼y (insert x y≼x ys)

  sort : List A → OList -∞
  sort []       = nil
  sort (x ∷ xs) = insert (⋆ x) min≼ (sort xs)

  forget : {l : * A} → OList l → List A
  forget nil           = []
  forget (cons -∞ _ xs) = forget xs
  forget (cons (⋆ x) _ xs) = x ∷ forget xs

module _ where
  open ℕ-≤
  open Lift {ℕ}

  l : List ℕ
  l = 2 ∷ 0 ∷ 1 ∷ []
  
  sl : OList _≤_ dec -∞
  sl = sort _≤_ dec l

  l₁ : List ℕ
  l₁ = forget _≤_ dec sl

  _ : l₁ ≡ (0 ∷ 1 ∷ 2 ∷ [])
  _ = refl
