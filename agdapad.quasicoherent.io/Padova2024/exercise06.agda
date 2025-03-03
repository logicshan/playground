{-# OPTIONS --cubical --allow-unsolved-meta #-}
{-
  AGDA IN PADOVA 2024
  Exercise sheet 6

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
  and then entering the path to this file: ~/Padova2024/exercise06.agda.
  As this file is read-only, you can then save a copy of this file to your personal
  directory and edit that one: File > Save As... For instance, you can save this file
  as ~/solutions06.agda.
-}

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero   + b = b
succ a + b = succ (a + b)

+zero : {x : ℕ} → x + zero ≡ x
+zero {zero} = λ i → zero
+zero {succ x} = cong succ (+zero {x})

+succ : {x y : ℕ} → x + (succ y) ≡ succ (x + y)
+succ {zero} {y} = refl
+succ {succ x} {y} = cong succ (+succ {x} {y})

lemma-+-commutative : (a b : ℕ) → (a + b) ≡ (b + a)
lemma-+-commutative zero zero = λ i → zero
lemma-+-commutative zero (succ b) = cong succ (sym (+zero {b}))
lemma-+-commutative (succ a) zero = cong succ (+zero {a})
lemma-+-commutative (succ a) (succ b) =
  succ (a + succ b)
    ≡⟨ cong succ (+succ {a} {b})  ⟩
  succ (succ (a + b))
    ≡⟨ cong (λ a₁ → succ (succ a₁)) (lemma-+-commutative a b) ⟩
  succ (succ (b + a))
    ≡⟨ cong succ (sym (+succ {b} {a})) ⟩
  succ (b + succ a) ∎

data UnorderedPair (X : Set) : Set where
  pair : (a b : X) → UnorderedPair X
  swap : (a b : X) → pair a b ≡ pair b a

data ⊥ : Set where

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

data ⊤ : Set where
  tt : ⊤

-- EXERCISE: Implement "cong". Because the name "cong" is already
-- exported from the standard library, we use a different name.
cong' : {X Y : Set} {a b : X} → (f : X → Y) → a ≡ b → f a ≡ f b
cong' f p = λ i → f (p i)

-- EXERCISE: Implement the sum operation on unordered pairs.
sum : UnorderedPair ℕ → ℕ
sum (pair a b) = a + b
sum (swap a b i) = lemma-+-commutative a b i

-- EXERCISE: Show that Cubical Agda validates the principle of function
-- extensionality, as follows:
funext : {A B : Set} (f g : A → B) → ((x : A) → f x ≡ g x) → f ≡ g
funext f g pntEq i = λ x → pntEq x i

-- EXERCISE: Implement the successor operation on ℤ.
-- https://github.com/agda/cubical/blob/master/Cubical/Data/Int/MoreInts/DeltaInt/Base.agda
data ℤ : Set where
  _⊝_ : ℕ → ℕ → ℤ     -- \o- \ominus
  cancel : (a b : ℕ) → a ⊝ b ≡ succ a ⊝ succ b

succℤ : ℤ → ℤ
succℤ (a ⊝ b) = succ a ⊝ b
succℤ (cancel a b i) = cancel (succ a) b i

-- EXERCISE: Show that zero is not succ zero.
--
-- With the inductive definition of _≡_ we used before, this required
-- an empty pattern. Now that _≡_ is no longer inductively defined,
-- but an in-built notion, we cannot case split on equality witnesses.
--
-- Instead, proceed as follows:
-- 1. Define a function "disambig : ℕ → Set" which maps zero to ⊥
--    and everything else to some inhabited type.
disambig : ℕ → Set
disambig zero = ⊥
disambig (succ _) = ⊤
-- 2. Assuming that there is a path "zero ≡ succ zero", combine
--    "transport" from the standard library and "disambig":
--        transport : {A B : Set} → A ≡ B → A → B
--
-- Note that "symm" is spelt "sym" in the cubical standard library
-- and "trans" is written as the binary operator "∙" (\.).
lemma-nontrivial : zero ≡ succ zero → ⊥
lemma-nontrivial p = subst disambig (sym p) tt

lemma-nontrivial' : {x : ℕ} → zero ≡ succ x → ⊥
lemma-nontrivial' p = subst disambig (sym p) tt

-- EXERCISE: Show that the unordered pair abstraction is not leaky, in the
-- sense that there cannot be a function which would extract the first
-- component of an unordered pair.
lemma-not-leaky : (f : UnorderedPair ℕ → ℕ) (p : (a b : ℕ) → f (pair a b) ≡ a) → ⊥
lemma-not-leaky f p = lemma-nontrivial absurd
  where
  absurd : zero ≡ succ zero
  absurd =
    zero ≡⟨ sym (p zero (succ zero)) ⟩
    f (pair zero (succ zero))  ≡⟨ cong f (swap zero (succ zero)) ⟩
    f (pair (succ zero) zero)  ≡⟨ p (succ zero) zero ⟩
    succ zero ∎

-- A type is called a "proposition" iff all its inhabitants are
-- equal. Hence all there is to know about a proposition is whether it is
-- inhabited.

isProp' : Set → Set
isProp' X = (a b : X) → a ≡ b

-- Show that negations are propositions.
lemma-negations-are-props : (X : Set) → isProp' (X → ⊥)
lemma-negations-are-props X a b = funext a b helper
  where
  helper : (x : X) → a x ≡ b x
  helper x = ⊥-elim (a x)

-- EXERCISE: Show that 𝟙 and Interval are the same, in the following sense.
data 𝟙 : Set where
  * : 𝟙

𝟙-isProp : isProp' 𝟙
𝟙-isProp * * = refl

data Interval : Set where
  left  : Interval
  right : Interval
  path  : left ≡ right

toInterval : 𝟙 → Interval
toInterval * = left

fromInterval : Interval → 𝟙
fromInterval _ = *

is-iso₁ : (x : 𝟙) → fromInterval (toInterval x) ≡ x
is-iso₁ * = refl

-- Hint: Use _∧_.
is-iso₂ : (x : Interval) → toInterval (fromInterval x) ≡ x
is-iso₂ left = refl
is-iso₂ right = path
is-iso₂ (path i) = λ j → path (i ∧ j)


-- EXERCISE: Show that ℕ is discrete, in the following sense.
isDiscrete : Set → Set
isDiscrete X = (a b : X) → isProp' (a ≡ b)

Code : ℕ → ℕ → Set
Code zero     zero     = 𝟙
Code zero     (succ y) = ⊥
Code (succ x) zero     = ⊥
Code (succ x) (succ y) = Code x y

fromCode : (a b : ℕ) → Code a b → a ≡ b
fromCode zero zero p = refl
fromCode (succ a) (succ b) p = cong succ (fromCode a b p)

ref : (a : ℕ) → Code a a
ref zero = *
ref (succ a) = ref a

-- Hint: Use "J" or "transport"!

toCode : (a b : ℕ) → a ≡ b → Code a b
toCode a b p = transport (λ i → Code (p i0) (p i)) (ref a)

lemma-code-prop : (a b : ℕ) → isProp' (Code a b)
lemma-code-prop zero zero * * = refl
lemma-code-prop zero (succ b) () ()
lemma-code-prop (succ a) zero () ()
lemma-code-prop (succ a) (succ b) p q = lemma-code-prop a b p q

lemma-fromCode : {a : ℕ} → fromCode a a (ref a) ≡ refl
lemma-fromCode {zero} = refl
lemma-fromCode {succ a} = cong (cong succ) lemma-fromCode

lemma-toCode : {a : ℕ} → toCode a a refl ≡ ref a
lemma-toCode {a} = lemma-code-prop a a (toCode a a refl) (ref a)

fromCode∘toCode : (a b : ℕ) (p : a ≡ b) → fromCode a b (toCode a b p) ≡ p
fromCode∘toCode a b p =  J
                         (λ b p → fromCode a b (toCode a b p) ≡ p)
                         (cong (fromCode a a) (lemma-toCode {a}) ∙ lemma-fromCode)
                         p

lemma-ℕ-discrete : isDiscrete ℕ
lemma-ℕ-discrete a b p q =
  p
    ≡⟨ sym (fromCode∘toCode a b p) ⟩
  fromCode a b (toCode a b p)
    ≡⟨ cong (fromCode a b) (lemma-code-prop a b (toCode a b p) (toCode a b q)) ⟩
  fromCode a b (toCode a b q)
    ≡⟨ fromCode∘toCode a b q ⟩
  q ∎
