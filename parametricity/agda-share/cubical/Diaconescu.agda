
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Data.Bool
open import Cubical.Data.Unit
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Relation.Nullary

module Diaconescu {ℓ} (P : Type ℓ) (Pp : isProp P) where

private
  variable
    ℓ' : Level

data T : Type ℓ where
  low high : T
  med : P -> low ≡ high

record T-Prop-Motive ℓ' : Type (ℓ-max ℓ (ℓ-suc ℓ')) where
  field
    Φ : T -> Type ℓ'
    Φ-prop : ∀ t → isProp (Φ t)
    on-low : Φ low
    on-high : Φ high

elim→Prop : (M : T-Prop-Motive ℓ') → (t : T) → T-Prop-Motive.Φ M t
elim→Prop M = go where
  open T-Prop-Motive M
  go : ∀ t → Φ t
  go  low = on-low
  go high = on-high
  go (med ¬p i) =
    isOfHLevel→isOfHLevelDep 1 Φ-prop on-low on-high (med ¬p) i

module Cover where
  LUnit = Lift {j = ℓ} Unit

  isPropLUnit : isProp LUnit
  isPropLUnit = isOfHLevelLift 1 isPropUnit

  p-unit : P -> P ≡ LUnit
  p-unit p = hPropExt Pp isPropLUnit (const _) (const p)

  low≅_ : T -> Type _
  low≅ low = LUnit
  low≅ high = P
  low≅ med p i = p-unit p (~ i)

  high≅_ : T -> Type _
  high≅ low = P
  high≅ high = LUnit
  high≅ med p i = p-unit p i

  low≅-prop : ∀ u → isProp (low≅ u)
  low≅-prop = elim→Prop λ where
      .Φ u → isProp (low≅ u)
      .Φ-prop _ → isPropIsProp
      .on-low → isPropLUnit
      .on-high → Pp
    where open T-Prop-Motive

  high≅-prop : ∀ u → isProp (high≅ u)
  high≅-prop = elim→Prop λ where
      .Φ u → isProp (high≅ u)
      .Φ-prop _ → isPropIsProp
      .on-low → Pp
      .on-high → isPropLUnit
    where open T-Prop-Motive

  lover : ∀ u → low ≡ u -> low≅ u
  lover u p = subst low≅_ p _

  hover : ∀ u → high ≡ u -> high≅ u
  hover u p = subst high≅_ p _

  med-low : ∀ p q → Square refl (med p) refl (med q)
  med-low p q i j =
    hcomp (λ k → λ where
        (i = i0) → low
        (i = i1) → med (Pp q p k) j
        (j = i0) → low
        (j = i1) → med q i)
      (med q (i ∧ j))

  med-high : ∀ p q → Square (med p) refl (med q) refl
  med-high p q i j =
    hcomp (λ k → λ where
        (i = i0) → med (Pp q p k) j
        (i = i1) → high
        (j = i0) → med q i
        (j = i1) → high)
      (med q (i ∨ j))

  unlover : ∀ u → low≅ u -> low ≡ u
  unlover  low c = refl
  unlover high c = med c
  unlover (med ¬p i) c =
    med-low (transp (λ k → low≅ med ¬p (i ∨ k)) i c) ¬p i

  unhover : ∀ u → high≅ u -> high ≡ u
  unhover  low c = sym (med c)
  unhover high _ = refl
  unhover (med p i) c j =
    med-high (transp (λ k → high≅ med p (i ∧ ~ k)) (~ i) c) p i (~ j)

  unlover-lover : ∀ u p → unlover u (lover u p) ≡ p
  unlover-lover u = J (λ t p → unlover t (lover t p) ≡ p) refl

  unhover-hover : ∀ u p → unhover u (hover u p) ≡ p
  unhover-hover u = J (λ t p → unhover t (hover t p) ≡ p) refl

low≅-prop : ∀ u → isProp (low ≡ u)
low≅-prop u =
  isPropRetract (Cover.lover u) (Cover.unlover u)
    (Cover.unlover-lover u) (Cover.low≅-prop u)

high≅-prop : ∀ u → isProp (high ≡ u)
high≅-prop u =
  isPropRetract (Cover.hover u) (Cover.unhover u)
    (Cover.unhover-hover u) (Cover.high≅-prop u)

T-set : isSet T
T-set = elim→Prop λ where
    .Φ t → ∀ u → isProp (t ≡ u)
    .Φ-prop t → isPropΠ (λ _ → isPropIsProp)
    .on-low  → low≅-prop
    .on-high → high≅-prop
  where open T-Prop-Motive

module Choice
  (C : ∀{ℓ'} {Q : T -> Type ℓ'} → ((t : T) -> ∥ Q t ∥₁) -> ∥ (∀ t → Q t) ∥₁)
  where
  open Cover
  _≅_ : Bool -> T -> Type _
  _≅_ false = low≅_
  _≅_  true = high≅_

  f : (t : T) -> ∥ Σ[ b ∈ Bool ] b ≅ t ∥₁
  f  low = ∣ false , _ ∣₁
  f high = ∣  true , _ ∣₁
  f (med p i) =
    isOfHLevel→isOfHLevelDep 1
      (λ t → squash₁ {A = Σ[ b ∈ Bool ] b ≅ t})
      ∣ false , _ ∣₁
      ∣  true , _ ∣₁
      (med p) i

  f! : (∀ t → Σ[ b ∈ Bool ] b ≅ t) -> Dec P
  f! ≅? with ≅? low | ≅? high | cong (fst ∘ ≅?) ∘ med
  ... | false , _ | false , p | k = yes p
  ... | false , x |  true , y | k = no (false≢true ∘ k)
  ... |  true , x | false , y | k = no (true≢false ∘ k)
  ... |  true , p |  true , _ | k = yes p

  EM : Dec P
  EM = PT.rec (isPropDec Pp) f! (C f)
