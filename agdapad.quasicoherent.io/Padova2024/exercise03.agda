{-# OPTIONS --allow-unsolved-metas #-}
{-
  AGDA IN PADOVA 2024
  Exercise sheet 3

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
  and then entering the path to this file: ~/Padova2024/exercise03.agda.
  As this file is read-only, you can then save a copy of this file to your personal
  directory and edit that one: File > Save As... For instance, you can save this file
  as ~/solutions03.agda.
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

¬ : Set → Set
¬ X = X → ⊥

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

infix 5 _≡_

data _≡_ {X : Set} : X → X → Set where
  refl : {a : X} → a ≡ a

{-# BUILTIN EQUALITY _≡_ #-}

cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : {A B C : Set} {x x' : A} {y y' : B} → (f : A → B → C) → x ≡ x' → y ≡ y' → f x y ≡ f x' y'
cong₂ f refl refl = refl

symm : {A : Set} {x y : A} → x ≡ y → y ≡ x
symm refl = refl


-- ────────────────────────────────────
-- ────[ GENERALITIES ON EQUALITY ]────
-- ────────────────────────────────────

-- EXERCISE: Fill in this hole, thereby proving that equality is transitive.
trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

-- EXERCISE: Prove that equal functions have equal values.
-- (The converse is a principle known as "function extensionality" which
-- can be postulated in Agda but is not assumed by default.)
equal→pwequal : {A B : Set} {f g : A → B} {x : A} → f ≡ g → f x ≡ g x
equal→pwequal refl = refl

-- EXERCISE: Think about the expression "(⊥ ≡ ℕ)". Is it well-defined?
-- What would be its meaning?

-- EXERCISE: Fill in this hole. This lemma will be used below
-- in the proof that the double of any number is even.
transport : {A : Set} {x y : A} → (F : A → Set) → x ≡ y → F x → F y
transport F refl s = s


-- ─────────────────────────────────
-- ────[ EQUALITIES OF NUMBERS ]────
-- ─────────────────────────────────

-- EXERCISE: Show that the predecessor of the successor of a number is that number again.
lemma-pred-succ : (a : ℕ) → pred (succ a) ≡ a
lemma-pred-succ zero = refl
lemma-pred-succ (succ a) = refl

-- EXERCISE: Show that the two functions "even?" and "even?'" have the same values.
even? : ℕ → Bool
even? zero     = true
even? (succ n) = ! (even? n)

even?' : ℕ → Bool
even?' zero            = true
even?' (succ zero)     = false
even?' (succ (succ n)) = even?' n

lemma-even?-even?' : (a : ℕ) → even? a ≡ even?' a
lemma-even?-even?' zero = refl
lemma-even?-even?' (succ a) rewrite lemma-even?-even?' a = lemma a
  where
  lemma : (x : ℕ) → ! (even?' x) ≡ even?' (succ x)
  lemma zero = refl
  lemma (succ zero) = refl
  lemma (succ (succ x)) = lemma x



-- EXERCISE: Show that it is not the case that "succ (pred a) ≡ a" for all natural numbers a.
lemma-succ-pred : ((a : ℕ) → succ (pred a) ≡ a) → ⊥
lemma-succ-pred f = 1≢0 (f zero)
  where
  1≢0 : succ zero ≡ zero → ⊥
  1≢0 ()

-- The following defines a type family "Positive : ℕ → Set" such that "Positive a" is the
-- type of witnesses that a is positive: The type "Positive zero" is empty
-- and the types "Positive (succ n)" are inhabited for every n.
data Positive : ℕ → Set where
  -- on purpose, we do NOT include this constructor: zero-is-positive : Positive zero
  succs-are-positive : {n : ℕ} → Positive (succ n)

-- EXERCISE: Fill in this hole.
lemma-succ-pred' : (a : ℕ) → Positive a → succ (pred a) ≡ a
lemma-succ-pred' zero ()
lemma-succ-pred' (succ a) succs-are-positive = refl

-- EXERCISE: Verify the following two auxiliary lemmas, establishing that we
-- could have equivalently defined addition also by recursion on the second argument.
lemma-+-zero : (a : ℕ) → (a + zero) ≡ a
lemma-+-zero zero = refl
lemma-+-zero (succ a) = cong succ (lemma-+-zero a)

lemma-+-succ : (a b : ℕ) → (a + succ b) ≡ succ (a + b)
lemma-+-succ zero b = refl
lemma-+-succ (succ a) b = cong succ (lemma-+-succ a b)

-- EXERCISE: Verify that addition is commutative.
lemma-+-commutative : (a b : ℕ) → (a + b) ≡ (b + a)
lemma-+-commutative zero b = symm (lemma-+-zero b)
lemma-+-commutative (succ a) b rewrite lemma-+-succ b a = cong succ (lemma-+-commutative a b)

-- EXERCISE: Verify that addition is associative.
lemma-+-associative : (a b c : ℕ) → (a + (b + c)) ≡ ((a + b) + c)
lemma-+-associative zero b c = refl
lemma-+-associative (succ a) b c = cong succ (lemma-+-associative a b c)

-- EXERCISE: Verify the distributive law. Similar as the implementation/proof
-- of lemma-+-commutative, the result will not be easy to read.
-- By a technique called "equational reasoning", to be introduced next time,
-- we will be able to clean up the proof.
lemma-distributive : (a b c : ℕ) → ((a + b) · c) ≡ ((a · c) + (b · c))
lemma-distributive zero b c = refl
lemma-distributive (succ a) b c
--  rewrite lemma-distributive a b c = lemma-+-associative c (a · c) (b · c)
  rewrite lemma-distributive a b c = lemma-+-associative c (a · c) (b · c)

-- EXERCISE: Show that the double of any number is even.
data Even : ℕ → Set where
  base-even : Even zero
  step-even : {n : ℕ} → Even n → Even (succ (succ n))

lemma-double-even : (a : ℕ) → Even (a + a)
lemma-double-even zero = base-even
lemma-double-even (succ a)
  rewrite lemma-+-commutative a (succ a) = step-even (lemma-double-even a)


-- ───────────────────────────────
-- ────[ EQUALITIES OF LISTS ]────
-- ───────────────────────────────

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

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
  lemma-reverse-∷ʳ [] x = refl
  lemma-reverse-∷ʳ (y ∷ ys) x rewrite lemma-reverse-∷ʳ ys x = refl

  lemma-reverse-reverse : (xs : List A) → reverse (reverse xs) ≡ xs
  lemma-reverse-reverse [] = refl
  lemma-reverse-reverse (x ∷ xs)
    rewrite lemma-reverse-∷ʳ (reverse xs) x = cong (x ∷_) (lemma-reverse-reverse xs)

  -- EXERCISE: State and prove that _++_ on lists is associative.
  _++_ : List A → List A → List A
  []       ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  lemma-++-associative : (xs ys zs : List A) → ((xs ++ ys) ++ zs) ≡ (xs ++ (ys ++ zs))
  lemma-++-associative [] ys zs = refl
  lemma-++-associative (x ∷ xs) ys zs = cong (x ∷_) (lemma-++-associative xs ys zs)

  -- The following relation relates exactly those lists which have the same length
  -- and whose corresponding entries are equal.
  data _≈_ : List A → List A → Set where
    both-empty     : [] ≈ []
    both-same-cons : {xs ys : List A} {x y : A} → x ≡ y → xs ≈ ys → (x ∷ xs) ≈ (y ∷ ys)

  -- EXERCISE: Show that equal lists are related by _≈_.
  ≡→≈ : {xs ys : List A} → xs ≡ ys → xs ≈ ys
  ≡→≈ {[]} {[]} refl = both-empty
  ≡→≈ {[]} {x ∷ ys} ()
  ≡→≈ {x ∷ xs} {[]} ()
  ≡→≈ {x ∷ xs} {.x ∷ .xs} refl = both-same-cons refl (≡→≈ refl)

  -- EXERCISE: Show that related lists are equal.
  ≈→≡ : {xs ys : List A} → xs ≈ ys → xs ≡ ys
  ≈→≡ both-empty = refl
  ≈→≡ (both-same-cons x p) = cong₂ _∷_ x (≈→≡ p)

  -- EXERCISE: Regarding "Any" and "_∈_" from exercise02.agda, show that
  -- "Any (x ≡_) xs" implies "x ∈ xs" and conversely.
  data Any (P : A → Set) : List A → Set where

    here  : {x : A} {xs : List A} → P x → Any P (x ∷ xs)
    there : {x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)

  data _∈_ : A → List A → Set where
    here  : {x : A} {ys : List A} → x ∈ (x ∷ ys)
    there : {x y : A} {ys : List A} → x ∈ ys → x ∈ (y ∷ ys)

  record _×_ (A B : Set) : Set where
    eta-equality
    constructor _,_
    field
      proj₁ : A
      proj₂ : B
  open _×_

  _↔_ : Set → Set → Set
  _↔_ A B = (A → B) × (B → A)
  
  variable
    x : A
    xs : List A

  anyEqIn : Any (x ≡_) xs ↔ (x ∈ xs)
  proj₁ anyEqIn (here x) rewrite x = here
  proj₁ anyEqIn (there any) = there (proj₁ anyEqIn any)
  proj₂ anyEqIn here = here refl
  proj₂ anyEqIn (there p) = there (proj₂ anyEqIn p)


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
lemma-take-drop zero xs = refl
lemma-take-drop (succ k) (x ∷ xs) = cong (x ∷_) (lemma-take-drop k xs)

-- EXERCISE: Find out where the difficulty is in stating that _++ᵥ_ on
-- vectors is associative.
