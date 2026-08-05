module Magic where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Nullary

Pointed : Type₁
Pointed = Σ[ X ∈ Type ] X

Homogeneous : Type → Type _
Homogeneous X = ∀ x y → Path Pointed (X , x) (X , y)

module _ (X : Type) (HX : Homogeneous X) (x : X) where
  Xx : Pointed
  Xx = (X , x)

  -- singl v = Σ[ u ∈ _ ] v ≡ u
  f : X → singl Xx
  f y = (X , y) , HX x y

  f' : ∥ X ∥ → singl Xx
  f' = PT.rec isPropSingl f

  magic : (tx : ∥ X ∥) → fst (fst (f' tx))
  magic = snd ∘ fst ∘ f'

  id-factored : X → X
  id-factored = magic ∘ ∣_∣

  lemma : ∀ z → id-factored z ≡ z
  lemma _ = refl

  reduce-me : X → X
  reduce-me z = {!magic ∣ z ∣!}

module _
  (X : Type)
  (_≟_ : Discrete X)
  where

  switch₀ : ∀(x y z : X) → Dec (x ≡ z) → Dec (y ≡ z) → X
  switch₀ x y z (yes _) dy = y
  switch₀ x y z (no _) (yes _) = x
  switch₀ x y z (no _) (no  _) = z

  switch : X → X → X → X
  switch x y z = switch₀ x y z (x ≟ z) (y ≟ z)

  switch₀-x : ∀ x y dx dy → switch₀ x y x dx dy ≡ y
  switch₀-x x y (yes p) dy = refl
  switch₀-x x y (no ¬p) dy = Empty.rec (¬p refl)

  switch₀-y : ∀ x y dx dy → switch₀ x y y dx dy ≡ x
  switch₀-y x y (yes p) dy = sym p
  switch₀-y x y (no _) (yes _) = refl
  switch₀-y x y (no _) (no ¬p) = Empty.rec (¬p refl)

  switch₀-z : ∀ x y z dx dy → ¬ x ≡ z → ¬ y ≡ z → switch₀ x y z dx dy ≡ z
  switch₀-z x y z (yes p) dy x≢z y≢z = Empty.rec (x≢z p)
  switch₀-z x y z (no _) (yes p) x≢z y≢z = Empty.rec (y≢z p)
  switch₀-z x y z (no _) (no  _) x≢z y≢z = refl

  switch₀-switch₀
    : ∀ x y z dx dy dy' dx'
    → switch₀ y x (switch₀ x y z dx dy) dy' dx' ≡ z
  switch₀-switch₀ x y z (yes p) dy dy' dx'
    = switch₀-x y x _ _ ∙ p
  switch₀-switch₀ x y z (no ¬p) (yes p) dy' dx'
    = switch₀-y y x _ _ ∙ p
  switch₀-switch₀ x y z (no ¬p) (no ¬q) dy' dx'
    = switch₀-z y x z _ _ ¬q ¬p

  switch-switch : ∀ x y z → switch y x (switch x y z) ≡ z
  switch-switch x y z
    = switch₀-switch₀ x y z (x ≟ z) (y ≟ z) (y ≟ _) (x ≟ _)

  Switch : X → X → X ≡ X
  Switch x y = isoToPath λ where
      .fun → switch x y
      .inv → switch y x
      .rightInv → switch-switch y x
      .leftInv  → switch-switch x y
    where open Iso

  switches : ∀ x y → PathP (λ i → Switch x y i) x y
  switches x y = toPathP (transportRefl _ ∙ switch₀-x x y _ _)

  homogeneous : Homogeneous X
  homogeneous x y = ΣPathP (Switch x y , switches x y)
