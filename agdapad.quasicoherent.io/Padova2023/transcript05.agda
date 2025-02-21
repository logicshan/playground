{-# OPTIONS --allow-unsolved-metas #-}
-- AGDA IN PADOVA 2023
-- Exercise sheet 3

data Bool : Set where
  false true : Bool

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

data ⊥ : Set where

data _⊎_ (A B : Set) : Set where
  left  : A → A ⊎ B
  right : B → A ⊎ B

¬ : Set → Set
¬ X = X → ⊥
-- Logical reading: "X is false if and only if assuming X would yield
-- a contradiction."
-- Computational reading: A witness of "¬ X" is a function which
-- could turn hypothetical witnesses of "X" into witnesses of "⊥".

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

-- EQUATIONAL REASONING

infix  3 _∎
infixr 2 _≡⟨_⟩_ _≡⟨⟩_
infix  1 begin_

-- EXERCISE: Prove that equality is symmetric.
symm : {A : Set} {x y : A} → x ≡ y → y ≡ x
symm p = {!!}

-- EXERCISE: Fill in this hole, thereby proving that equality is transitive.
trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans p q = {!!}


_≡⟨_⟩_ : {A : Set} {y z : A} → (x : A) → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ p ⟩ q = trans p q

_≡⟨⟩_ : {A : Set} {y : A} → (x : A) → (q : x ≡ y) → x ≡ y
x ≡⟨⟩ q = q

_∎ : {A : Set} → (x : A) → x ≡ x
x ∎ = refl

begin_ : {A : Set} {x y : A} → x ≡ y → x ≡ y
begin p = p


------------------------------------
----[ LOGICAL TAUTOLOGIES ]---------
------------------------------------

dni : {A B : Set} → A → ((A → ⊥) → ⊥)
dni p = λ f → f p

contraposition : {A B : Set} → (A → B) → (¬ B → ¬ A)
contraposition f p = {!!}

de-morgan₁ : {A B : Set} → ¬ (A ⊎ B) → ¬ A
de-morgan₁ = {!!}

de-morgan₂ : {A B : Set} → ¬ (A ⊎ B) → ¬ B
de-morgan₂ = {!!}


------------------------------------
----[ GENERALITIES ON EQUALITY ]----
------------------------------------

-- EXERCISE: Fill in this hole, thereby proving that equality is a "congruence";
-- by this lemma, we can apply the same operation to the two sides of an equation
-- and still be sure that the equation holds.
cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f p = {!!}

-- EXERCISE: Prove that equal functions have equal values. (The
-- converse is a principle known as "function extensionality" which
-- can be postulated in Agda but is not assumed by default.)
equal→pwequal : {A B : Set} {f g : A → B} {x : A} → f ≡ g → f x ≡ g x
equal→pwequal p = {!!}

-- EXERCISE: Think about the expression "(⊥ ≡ ℕ)". Is it well-defined?
-- What would be its meaning?

-- EXERCISE: Fill in this hole. This lemma will be used below
-- in the proof that the double of any number is even.
transport : {A : Set} {x y : A} → (F : A → Set) → x ≡ y → F x → F y
transport F p s = {!!}


---------------------------------
----[ EQUALITIES OF NUMBERS ]----
---------------------------------

-- EXERCISE: Show that the predecessor of the successor of a number is that number again.
lemma-pred-succ : (a : ℕ) → pred (succ a) ≡ a
lemma-pred-succ a = {!!}

lemma₀ : ! (! true) ≡ true
lemma₀ = refl

lemma₁ : ! (! false) ≡ false
lemma₁ = refl

-- Logical reading: "For every x, ! (! x) ≡ x."
-- Computational reading: "lemma₂ is a function
-- which reads a Boolean 'x' as input and outputs
-- a witness that '! (! x) ≡ x'."
lemma₂ : (x : Bool) → ! (! x) ≡ x
lemma₂ false = refl
lemma₂ true  = refl

lemma₃ : {x : Bool} → ! (! x) ≡ x
lemma₃ {false} = refl
lemma₃ {true}  = refl

lemma₄ : ! (! false) ≡ false
lemma₄ = lemma₂ false

lemma₅ : ! (! false) ≡ false
lemma₅ = lemma₃  -- {false}

-- EXERCISE: Show that the two functions "even?" and "even?'" have the same values.
even? : ℕ → Bool
even? zero     = true
even? (succ n) = ! (even? n)

even?' : ℕ → Bool
even?' zero            = true
even?' (succ zero)     = false
even?' (succ (succ n)) = even?' n

lemma-even?-even?' : (a : ℕ) → even? a ≡ even?' a
lemma-even?-even?' zero            = refl
lemma-even?-even?' (succ zero)     = refl
lemma-even?-even?' (succ (succ a)) = trans lemma₃ (lemma-even?-even?' a)

lemma-even?-even?'-second-proof : (a : ℕ) → even? a ≡ even?' a
lemma-even?-even?'-second-proof zero            = refl
lemma-even?-even?'-second-proof (succ zero)     = refl
lemma-even?-even?'-second-proof (succ (succ a)) with even? a with lemma-even?-even?'-second-proof a
... | false | p = p
... | true  | p = p

third-proof : (a : ℕ) → even? a ≡ even?' a
third-proof zero            = refl
third-proof (succ zero)     = refl
third-proof (succ (succ a)) = begin
  even? (succ (succ a))  ≡⟨⟩   -- \== \< \>
  ! (even? (succ a))     ≡⟨⟩
  ! (! (even? a))        ≡⟨ lemma₃ ⟩
  even? a                ≡⟨ third-proof a ⟩
  even?' a               ≡⟨⟩
  even?' (succ (succ a)) ∎   -- \qed

-- EXERCISE: Show that it is not the case that "succ (pred a) ≡ a" for all natural numbers a.
lemma-succ-pred : ((a : ℕ) → succ (pred a) ≡ a) → ⊥
lemma-succ-pred f = {!!}

-- The following defines a type family "Positive : ℕ → Set" such that "Positive a" is the
-- type of witnesses that a is positive: The type "Positive zero" is empty
-- and the types "Positive (succ n)" are inhabited for every n.
data Positive : ℕ → Set where
  -- on purpose, we do NOT include this constructor: zero-is-positive : Positive zero
  succs-are-positive : {n : ℕ} → Positive (succ n)

-- EXERCISE: Fill in this hole.
lemma-succ-pred' : (a : ℕ) → Positive a → succ (pred a) ≡ a
lemma-succ-pred' (succ b) p = refl

-- EXERCISE: Verify the following two auxiliary lemmas, establishing that we
-- could have equivalently defined addition also by recursion on the second argument.
lemma-+-zero : (a : ℕ) → (a + zero) ≡ a
lemma-+-zero a = {!!}

lemma-+-succ : (a b : ℕ) → (a + succ b) ≡ succ (a + b)
lemma-+-succ zero     b = refl
lemma-+-succ (succ a) b = begin
  succ a + succ b     ≡⟨⟩
  succ (a + succ b)   ≡⟨ cong succ (lemma-+-succ a b) ⟩
  succ (succ (a + b)) ≡⟨⟩
  succ (succ a + b)   ∎

-- EXERCISE: Verify that addition is commutative.
lemma-+-commutative : (a b : ℕ) → (a + b) ≡ (b + a)
lemma-+-commutative a b = {!!}

-- EXERCISE: Verify that addition is associative.
lemma-+-associative : (a b c : ℕ) → (a + (b + c)) ≡ ((a + b) + c)
lemma-+-associative a b c = {!!}

-- EXERCISE: Verify the distributive law. Similar as the implementation/proof
-- of lemma-+-commutative, the result will not be easy to read.
-- By a technique called "equational reasoning", to be introduced next week,
-- we will be able to clean up the proof.
lemma-distributive : (a b c : ℕ) → ((a + b) · c) ≡ ((a · c) + (b · c))
lemma-distributive a b c = {!!}

-- EXERCISE: Show that the double of any number is even.
data Even : ℕ → Set where
  base-even : Even zero
  step-even : {n : ℕ} → Even n → Even (succ (succ n))

lemma-double-even : (a : ℕ) → Even (a + a)
lemma-double-even a = {!!}


-------------------------------
----[ EQUALITIES OF LISTS ]----
-------------------------------

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

  -- EXERCISE: Show that equal lists are related by _≈_.
  ≡→≈ : {xs ys : List A} → xs ≡ ys → xs ≈ ys
  ≡→≈ p = {!!}

  -- EXERCISE: Show that related lists are equal.
  ≈→≡ : {xs ys : List A} → xs ≈ ys → xs ≡ ys
  ≈→≡ p = {!!}


---------------------------------
----[ EQUALITIES OF VECTORS ]----
---------------------------------

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
