
module ParamFunctor where

open import Cubical.Foundations.Prelude

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function renaming (idfun to id)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma

-- The parametricity presentation below is based on
--
--   Logical Relations and Parametricity - A Reynolds
--   Programme for Category Theory and Programming Languages
--     - Hermida, Reddy and Robinson
--
--   https://www.sciencedirect.com/science/article/pii/S1571066114000346

variable
  A A' B B' C : Type

-- A 'relation' between two types is just a family.
-- Technically this is some sort of profunctor, and is
-- proof relevant.
infix 10 _⇔_
_⇔_ : Type → Type → Type₁
A ⇔ B = A → B → Type

-- Given a function A → B, we can form the graph relation B ⇔ A
G : (A → B) → B ⇔ A
G f y x = y ≡ f x

-- The comma relation, given two functions into a common type.
_↓_ : (A → C) → (B → C) → A ⇔ B
_↓_ f g x y = f x ≡ g y

-- A 'relator' from Type to Type is:
--
--   1. A mapping F : Type → Type
--   2. A mapping [F] : (A ⇔ B) → (F A ⇔ F B)
--   3. Such that [F] _≡_ ≡ _≡_
--
-- 3 is the identity extension principle.
--
-- We can also have n-ary relators which satisfy analogous
-- conditions for multiple arguments.

-- The function type extends to a relator.
infixr 15 _[→]_
_[→]_ : (A ⇔ A') → (B ⇔ B') → (A → B) ⇔ (A' → B')
(R [→] S) f g = ∀ x y → R x y → S (f x) (g y)

module _ {f g : A → B} where
  hFunExt : (∀ x y → x ≡ y → f x ≡ g y) → f ≡ g
  hFunExt pw i x = pw x x refl i

  hFunExt⁻ : f ≡ g → ∀ x y → x ≡ y → f x ≡ g y
  hFunExt⁻ fg _ _ p i = fg i (p i)

  hFunExt-lemma : retract hFunExt hFunExt⁻
  hFunExt-lemma pw j x y p =
    J (λ z q → hFunExt⁻ (hFunExt pw) x z q ≡ pw x z q) refl p j

  open Iso
  hFunExt-iso : Iso (∀ x y → x ≡ y → f x ≡ g y) (f ≡ g)
  hFunExt-iso .fun = hFunExt
  hFunExt-iso .inv = hFunExt⁻
  hFunExt-iso .rightInv _ = refl
  hFunExt-iso .leftInv    = hFunExt-lemma

hFunExt-path
  : (f g : A → B) → (∀ x y → x ≡ y → f x ≡ g y) ≡ (f ≡ g)
hFunExt-path f g = isoToPath hFunExt-iso

id-ext-→ : Path A [→] Path B ≡ Path (A → B)
id-ext-→ i f g = hFunExt-path f g i

-- Most other standard, non-dependent type formers act as
-- relators as well. In something like System F, even quantifiers
-- of relators are relators. Here I haven't bothered to define
-- things generally enough to model that.

-- Even Path seems to act like a relator, although this is
-- just a guess at the appropriate definition, not a
-- rigorous derivation from some theory.
[Path] : ∀(R : A ⇔ B) {w y x z} → R w x → R y z → Path A w y ⇔ Path B x z
[Path] R wx yz p q = PathP (λ i → R (p i) (q i)) wx yz

id-ext-Path : ∀{x : A} → [Path] _≡_ refl refl ≡ Path (x ≡ x)
id-ext-Path j p q = isoToPath the-iso j where
  open Iso
  the-iso : Iso (PathP (λ i → p i ≡ q i) refl refl) (p ≡ q)
  the-iso .fun r i j = r j i
  the-iso .inv r i j = r j i
  the-iso .rightInv r = refl
  the-iso .leftInv  r = refl

-- A parametric transformation between relators F and G is:
--
--   1. A mapping t : (A : Type) → F A → G A
--   2. That lifts to relations:
--        (R : A ⇔ B) → ([F] R [→] [G] R) (t A) (t B)
--
-- As with relators, we can have transformations involving
-- multiple quantifiers and multi-argument relators. The
-- parametricity theorem for a polymorphic function is the
-- second part of the witness that it's a parametric
-- transformation.

module Map
  -- Let F be a relator
  (F : Type → Type)
  ([F] : ∀{A B} → (A ⇔ B) → F A ⇔ F B)
  (id-ext-F : ∀{A} → [F] {A} _≡_ ≡ _≡_)
  -- Let m be a parametric transformation
  (m : ∀{A B} → (A → B) → F A → F B)
  (pm : ∀{A A'} {B B'} (R : A ⇔ A') (S : B ⇔ B')
      → ((R [→] S) [→] [F] R [→] [F] S) m m)
  -- Suppose m id = id
  (m-id : ∀{A} → m (id A) ≡ id (F A))
  where
  -- There is a reflexive value of [F] _≡_
  [F]-refl : ∀(x : F A) → [F] _≡_ x x
  [F]-refl x = transport⁻ (λ i → id-ext-F i x x) refl

  -- By parametricity, `m f x` is related to `m id x` by
  -- the lifting of the graph relation.
  m-G-id : ∀(f : A → B) x → [F] (G f) (m f x) (m (id A) x)
  m-G-id f x =
    pm _≡_ (G f) f (id _) (λ x y → cong f) x x ([F]-refl x)

  -- So `m f x` is related to `x` by our identity assumption
  m-G : ∀(f : A → B) x → [F] (G f) (m f x) x
  m-G f x = transport (cong T m-id) (m-G-id f x) where
    T : (_ → _) → Type
    T h = [F] (G f) (m f x) (h x)

  -- Again by parametricity, `m g (m f x)` is related to
  -- `m (g ∘ f) x` by [F] _≡_
  m-∘-[F] : ∀(f : A → B) (g : B → C) x
          → [F] _≡_ (m g (m f x)) (m (g ∘ f) x)
  m-∘-[F] f g x =
    pm (G f) _≡_ g (g ∘ f) cg (m f x) x (m-G f x)
    where
    cg : ∀ y x → y ≡ f x → g y ≡ g (f x)
    cg _ _ = cong g

  -- So, `m (g ∘ f) ≡ m g ∘ m f` by identity extension
  m-∘ : ∀(f : A → B) (g : B → C) → m g ∘ m f ≡ m (g ∘ f)
  m-∘ f g = funExt λ x →
      transport (cong (T x) id-ext-F) (m-∘-[F] f g x)
    where
    T : _ → (_ → _ → _) → Type
    T x R = R (m g (m f x)) (m (g ∘ f) x)

  -- Therefore, m satisfies the specification for being
  -- a functorial mapping.

-- Alternately, we can prove a 'free theorem' analogue
-- using `m` itself as the functorial action.
module Free
  -- Let F be a relator
  (F : Type → Type)
  ([F] : ∀{A B} → (A ⇔ B) → F A ⇔ F B)
  (id-ext-F : ∀{A} → [F] {A} _≡_ ≡ _≡_)
  -- Let m be a parametric transformation
  (m : ∀{A B} → (A → B) → F A → F B)
  (pm : ∀{A A'} {B B'} (R : A ⇔ A') (S : B ⇔ B')
      → ((R [→] S) [→] [F] R [→] [F] S) m m)
  where
  -- There is a reflexive value of [F] _≡_
  [F]-refl : ∀(x : F A) → [F] _≡_ x x
  [F]-refl x = transport⁻ (λ i → id-ext-F i x x) refl

  module _ (f : A → B) (g : A' → B')
           (h : A → A') (k : B → B')
           (ghkf : g ∘ h ≡ k ∘ f)
    where
    square : ∀ x → [F] (g ↓ k) (m h x) (m f x)
    square x = pm _≡_ (g ↓ k) h f (hFunExt⁻ ghkf) x x ([F]-refl x)

    free-[F] : ∀ x → [F] _≡_ (m g (m h x)) (m k (m f x))
    free-[F] x = pm (g ↓ k) _≡_ g k (λ _ _ p → p) (m h x) (m f x) (square x)

    free : m g ∘ m h ≡ m k ∘ m f
    free i x = transport T (free-[F] x) i
      where T = λ i → id-ext-F i (m g (m h x)) (m k (m f x))

-- Using the 'free' theorem about m in terms of itself, and that
-- m preserves identity, we can prove that it preserves composition.
module FreeMap
  (F : Type → Type)
  (m : ∀{A B} → (A → B) → F A → F B)
  (m-id : ∀{A} → m (id A) ≡ id (F A))
  (free : ∀{A A' B B'}
        → (f : A → B) (g : A' → B')
        → (h : A → A') (k : B → B')
        → g ∘ h ≡ k ∘ f
        → m g ∘ m h ≡ m k ∘ m f)
  where
  m-∘ : ∀(f : A → B) (g : B → C) → m g ∘ m f ≡ m (g ∘ f)
  m-∘ f g = free (g ∘ f) g f (id _) refl ∙ cong (_∘ m (g ∘ f)) m-id

-- Final aside:
--
-- Type equivalence is a relator, because it is just a subtype
-- of functions, which are relators. This would mean that
-- type equality is also a relator (by univalence), except
-- it's too large for the definitions in this file.
_[≃]_ : (R : A ⇔ A') (S : B ⇔ B') → (A ≃ B) ⇔ (A' ≃ B')
(R [≃] S) E F = (R [→] S) (fst E) (fst F)

id-ext-≃ : (Path A [≃] Path B) ≡ Path (A ≃ B)
id-ext-≃ {A} {B} i E F = the-path i where
  the-path : (Path A [≃] Path B) E F ≡ Path (A ≃ B) E F
  the-path = hFunExt-path (fst E) (fst F)
           ∙ ua (Σ≡PropEquiv isPropIsEquiv)
