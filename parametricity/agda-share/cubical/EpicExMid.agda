module EpicExMid where

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty
open import Cubical.Data.Bool
open import Cubical.Data.Maybe

open import Cubical.Relation.Nullary

variable
  A B : Type

-- Handy machinery
record Reveal_·_is_ (f : A → B) (x : A) (y : B) : Type where
  constructor [_]
  field eq : f x ≡ y

inspect : (f : A → B) → (x : A) → Reveal f · x is f x
inspect f x = [ refl ]

-- Epic with respect to all types
Epic : (A → B) → Type _
Epic f = ∀(C : Type₁) → (g h : _ → C)
       → (∀ x → g (f x) ≡ h (f x)) → ∀ b → g b ≡ h b

-- Epic with respect to sets
EpicS : (A → B) → Type _
EpicS f = ∀(C : Type₁) → isSet C → (g h : _ → C)
        → (∀ x → g (f x) ≡ h (f x)) → ∀ b → g b ≡ h b

module _
  (P : Type)
  (Pprp : isProp P)
  where

  -- T is the interval if P is inhabited, the two element set if
  -- P is uninhabited
  data T : Type where
    zero one : T
    yes : P → zero ≡ one

  -- Proposed covering of T by the booleans
  cover : Bool → T
  cover false = zero
  cover true  = one

  MP = Maybe P

  swap : P → MP → MP
  swap p nothing = just p
  swap p (just _) = nothing

  swapPath : P → MP ≡ MP
  swapPath p = isoToPath theIso where
    open Iso

    theIso : Iso MP MP
    theIso .fun = swap p
    theIso .inv = swap p
    theIso .rightInv nothing = refl
    theIso .rightInv (just x) i = just (Pprp p x i)
    theIso .leftInv nothing = refl
    theIso .leftInv (just x) i = just (Pprp p x i)

  G : T → Type
  G _ = MP

  H : T → Type
  H zero = MP
  H  one = MP
  H (yes p i) = swapPath p i

  -- G and H are equal on the supposed covering.
  lemma₀ : ∀ b → G (cover b) ≡ H (cover b)
  lemma₀ false = refl
  lemma₀  true = refl

  lemma₁ : (p : P) → ¬ PathP (λ i → swapPath p i) nothing nothing
  lemma₁ p pp = ¬just≡nothing (fromPathP pp)

  lemma₂
    : (α : ∀ x → G x ≡ H x)
    → transport (α zero) nothing ≡ nothing
    → transport (α one) nothing ≡ nothing
    → P → ⊥
  lemma₂ α r s p = lemma₁ p (subst2 (PathP (λ i → swapPath p i)) r s pp)
    where
    pp : PathP (λ i → swapPath p i)
           (transport (α zero) nothing)
           (transport (α  one) nothing)
    pp = cong (λ t → transport (α t) nothing) (yes p)

  -- If G and H are homotopic, then excluded middle holds for P
  lemma₃ : (∀ t → G t ≡ H t) → Dec P
  lemma₃ α
    with transport (α zero) nothing | inspect (transport (α zero)) nothing
  ... | just p | _ = yes p
  ... | nothing | [ zz ]
    with transport (α one) nothing | inspect (transport (α one)) nothing
  ... | just p | _ = yes p
  ... | nothing | [ oo ] = no (lemma₂ α zz oo)

  -- If the covering is epic with respect to all types, then
  -- excluded middle holds for P.
  Epic→DiscreteP : Epic cover → Dec P
  Epic→DiscreteP epi = lemma₃ (epi Type G H lemma₀)

  -- The covering is epic with respect to sets, thus surjective.
  cover-epis : EpicS cover
  cover-epis C Cset g h q zero = q false
  cover-epis C Cset g h q  one = q true
  cover-epis C Cset g h q (yes p i)
    = isSet→isSet' Cset
        (q false) (q true) (cong g (yes p)) (cong h (yes p)) i
