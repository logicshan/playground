
module ThinOrdinal where

open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe as Maybe
open import Cubical.Data.Unit
open import Cubical.Induction.WellFounded
open import Cubical.Relation.Nullary

-- Ordinals as types with a well-founded, extensional, transitive order.
record Ord ℓ : Type (ℓ-suc ℓ) where
  field
    O : Type ℓ
    _≺_ : O -> O -> Type ℓ
    pr : ∀ α β → isProp (α ≺ β)
    wf : WellFounded _≺_

  -- The weak ordering on ordinal is taken to be induced, as
  --
  --   'Everything below α is also below β.'
  _≼_ : O -> O -> Type ℓ
  α ≼ β = ∀ γ → γ ≺ α -> γ ≺ β

  field
    -- extensionality
    ex : ∀{α β} → α ≼ β -> β ≼ α -> α ≡ β
    -- transitivity
    tr : ∀{α β γ} → α ≺ β -> β ≺ γ -> α ≺ γ

  -- Well-foundedness makes the relation irreflexive.
  irref : ∀{α} → ¬ α ≺ α
  irref {α} =
    WFI.induction wf {P = λ β → ¬ β ≺ β} (λ β rec β≺β → rec β β≺β β≺β) α

  -- Transitivity with weak ordering on the right always holds.
  ≺-≼ : ∀{α β γ} → α ≺ β -> β ≼ γ -> α ≺ γ
  ≺-≼ αβ βγ = βγ _ αβ

  ≼-¬≺ : ∀{α β} → α ≼ β -> ¬ β ≺ α
  ≼-¬≺ αβ βα = irref (≺-≼ βα αβ)

module _ (P : Type) (Pp : isProp P) where
  -- The thin ordinal will make use of the same type that underlies
  -- Diaconescu's proof that choice implies excluded middle.
  open import Diaconescu (¬ P) (isProp¬ P)
  open Ord

  -- U is the Diaconescu type with an extra value, which we will take
  -- to be the 'top' of the order.
  U = Maybe T
  U-set = isOfHLevelMaybe 0 T-set

  pattern l = just low
  pattern h = just high
  pattern t = nothing
  pattern m p i = just (med p i)

  private variable ℓ : Level

  p-botp : ¬ P -> Path (hProp _) (P , Pp) (⊥ , isProp⊥)
  p-botp ¬p = Σ≡Prop (λ _ → isPropIsProp) (hPropExt Pp isProp⊥ ¬p Empty.rec)

  p-bot : ¬ P -> P ≡ ⊥
  p-bot = cong fst ∘ p-botp

  dec-unit : ¬ P -> Dec P ≡ Unit
  dec-unit ¬p = hPropExt (isPropDec Pp) isPropUnit (const tt) (const (no ¬p))

  isPropp : isPropDep {A = Type} isProp
  isPropp = isOfHLevel→isOfHLevelDep 1 (λ _ → isPropIsProp)

  cancel
    : ∀{A : Type ℓ} {x y : A} → (p : x ≡ y)
    → Square (symP p) refl refl p
  cancel {y = y} p i j =
    hcomp (λ k → λ where
        (j = i0) → y
        (i = i0) → p (~ j)
        (i = i1) → p (~ j ∨ k)
        (j = i1) → p (i ∧ k))
      (p (~ j))

  p-botp-cancel : ∀ ¬p ¬q → Square (sym (p-botp ¬q)) refl refl (p-botp ¬p)
  p-botp-cancel ¬p ¬q =
    subst (Square (sym (p-botp ¬q)) refl refl ∘ p-botp)
          (isProp¬ P ¬q ¬p)
          (cancel (p-botp ¬q))

  p-bot-cancel : ∀ ¬p ¬q → Square (sym (p-bot ¬q)) refl refl (p-bot ¬p)
  p-bot-cancel ¬p ¬q i j = fst (p-botp-cancel ¬p ¬q i j)

  -- The most direct way to derive excluded middle is to use Dec P in
  -- the order itself.
  _<_ : U -> U -> Type
  l < l = ⊥
  l < h = P
  l < t = Dec P
  h < t = Unit
  h < _ = ⊥
  t < _ = ⊥
  m ¬p i < l = ⊥
  m ¬p i < h = p-bot ¬p i
  m ¬p i < t = dec-unit ¬p i
  l < m ¬p i = p-bot ¬p (~ i)
  m ¬p i < m ¬q j = fst (p-botp-cancel ¬p ¬q i j)

  isProp-< : ∀ t u → isProp (t < u)
  isProp-< l l = isProp⊥
  isProp-< l h = Pp
  isProp-< l t = isPropDec Pp
  isProp-< h t = isPropUnit
  isProp-< h l = isProp⊥
  isProp-< h h = isProp⊥
  isProp-< t _ = isProp⊥
  isProp-< (m p i) l = isProp⊥
  isProp-< (m p i) h = snd (p-botp p i)
  isProp-< (m p i) t = isPropp (isPropDec Pp) isPropUnit (dec-unit p) i
  isProp-< l (m p i) = snd (p-botp p (~ i))
  isProp-< h (m p i) = isProp⊥
  isProp-< (m ¬p i) (m ¬q j) = snd (p-botp-cancel ¬p ¬q i j)

  _≤_ : U -> U -> Type
  u ≤ v = ∀ w → w < u -> w < v

  Accp : isPropDep (Acc _<_)
  Accp = isOfHLevel→isOfHLevelDep 1 isPropAcc

  wfl : Acc _<_ l
  wfl = acc pre where
    pre : ∀ t → t < l -> Acc _<_ t
    pre l ()

  wfh : Acc _<_ h
  wfh = acc pre where
    pre : ∀ α → α < h -> Acc _<_ α
    pre l ti = wfl
    pre h bo = Empty.rec bo
    pre (m p i) ti =
      Accp wfl (Empty.rec (transp (λ k → p-bot p (i ∨ k)) i ti)) (m p) i

  wft : Acc _<_ t
  wft = acc pre where
    pre : ∀ u → u < t -> Acc _<_ u
    pre l _ = wfl
    pre h _ = wfh
    pre (m p i) _ = Accp wfl wfh (m p) i

  extt : ∀ u v → u ≤ v -> v ≤ u -> u ≡ v
  extt = Maybe.elim Q goₙ goⱼ₀ where
    open T-Prop-Motive
    R : U -> U -> Type
    R u v = u ≤ v -> v ≤ u -> u ≡ v
    Q : U -> Type
    Q u = ∀ v → R u v

    goⱼⱼ : ∀ u v → R (just u) (just v)
    goⱼⱼ = elim→Prop λ where
      .Φ u → ∀ v → R (just u) (just v)
      .Φ-prop u → isPropΠ λ v → isProp→ (isProp→ (U-set (just u) (just v)))
      .on-low  → elim→Prop λ where
        .Φ v → R l (just v)
        .Φ-prop v → isProp→ (isProp→ (U-set l (just v)))
        .on-low  _ _ → refl
        .on-high x y → m (y l)
      .on-high → elim→Prop λ where
        .Φ v → R h (just v)
        .Φ-prop v → isProp→ (isProp→ (U-set h (just v)))
        .on-low  x y → sym (m (x l))
        .on-high _ _ → refl

    goₙ : Q nothing
    goₙ = Maybe.elim (R t) (λ _ _ → refl) (λ v x y → Empty.rec (x h _))

    goⱼ₀ : ∀ u → Q (just u)
    goⱼ₀ u = Maybe.elim (R (just u)) (λ v x → Empty.rec (x h _)) (goⱼⱼ u)

  module _ where
    open T-Prop-Motive
    private
      Q : U -> U -> U -> Type
      Q u v w = u < v -> v < w -> u < w

      isPropQ : ∀ u v w → isProp (Q u v w)
      isPropQ u v w = isProp→ (isProp→ (isProp-< u w))

    tran : ∀ u v w → u < v -> v < w -> u < w
    tran (just u) (just v) (just w) = flip elim→Prop w λ where
      .Φ w → Q (just u) (just v) (just w)
      .Φ-prop → isPropQ (just u) (just v) ∘ just
      .on-low → flip elim→Prop v λ where
        .Φ v → Q (just u) (just v) l
        .Φ-prop v → isPropQ (just u) (just v) l
      .on-high → flip elim→Prop v λ where
        .Φ v → Q (just u) (just v) h
        .Φ-prop v → isPropQ (just u) (just v) h
        .on-low → flip elim→Prop u λ where
          .Φ u → Q (just u) l h
          .Φ-prop u → isPropQ (just u) l h
    tran (just u) (just v) t = flip elim→Prop u λ where
        .Φ u → Q (just u) (just v) t
        .Φ-prop u → isPropQ (just u) (just v) t
        .on-low → flip elim→Prop v λ where
          .Φ v → Q l (just v) t
          .Φ-prop v → isPropQ l (just v) t
          .on-high p _ → yes p

  -- τ is a transitive ordinal whose plumpness entails excluded middle
  τ : Ord _
  τ .O = U
  τ ._≺_ = _<_
  τ .pr = isProp-<
  τ .wf l = wfl
  τ .wf h = wfh
  τ .wf t = wft
  τ .wf (m ¬p i) = Accp wfl wfh (m ¬p) i
  τ .ex = extt _ _
  τ .tr {u} {v} {w} = tran u v w

  -- l is less or equal to h simply because nothing is below l ..
  l≤h : l ≤ h
  l≤h l ()

  -- h is trivially less than t ...
  h<t : h < t
  h<t = tt

  -- However, l is only less than t when we can decide P. Since l is
  -- below h when P holds, we can prove transitivity of the strict
  -- order, but not with the weak order on the left.
  ¬plump : (∀ u v w → u ≤ v -> v < w -> u < w) -> Dec P
  ¬plump plump = plump l h t l≤h h<t
