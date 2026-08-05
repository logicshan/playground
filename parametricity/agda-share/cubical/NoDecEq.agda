
module NoDecEq where

open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma as Sigma
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Unit as Unit
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Relation.Nullary

variable ℓ : Level

module _ (P : Type) (Pprp : isProp P) where
  data Q : Type where
    a b c : Q
    yes :   P -> a ≡ b
    no  : ¬ P -> a ≡ c

  elimProp
    : (P : Q -> Type ℓ)
   -> (Pprp : isOfHLevelDep 1 P)
   -> (Pa : P a) -> (Pb : P b) -> (Pc : P c)
   -> ∀ t -> P t
  elimProp P Pprp Pa Pb Pc = λ where
    a → Pa
    b → Pb
    c → Pc
    (yes p i) → Pprp Pa Pb (yes p) i
    (no ¬p i) → Pprp Pa Pc (no ¬p) i

  F : Q -> Type
  F a = P
  F b = Unit
  F c = ⊥
  F (yes p i) = hPropExt Pprp isPropUnit (const _) (const p) i
  F (no ¬p i) = hPropExt Pprp isProp⊥ ¬p Empty.rec i

  b≠c : ¬ b ≡ c
  b≠c p = transport (λ i → F (p i)) _

  Hyp : Type _
  Hyp = ∃[ x ∈ Q ] ∃[ y ∈ Q ] ¬ x ≡ y -> ∀ x → ∃[ y ∈ Q ] ¬ x ≡ y

  some-x≠y : ∃[ x ∈ Q ] ∃[ y ∈ Q ] ¬ x ≡ y
  some-x≠y = ∣ b , ∣ c , b≠c ∣₁ ∣₁

  extract : (w : Q) -> ¬ a ≡ w -> Dec (¬ P)
  extract =
    elimProp (λ w → ¬ a ≡ w -> Dec (¬ P))
      (isOfHLevel→isOfHLevelDep 1 (λ _ → isProp→ (isPropDec (isProp¬ P))))
      (λ ne → Empty.rec (ne refl))
      (λ ne → yes (ne ∘ yes))
      (λ ne → no  (ne ∘ no))

  w-dec : Hyp -> Dec (¬ P)
  w-dec hyp =
    PT.rec (isPropDec (isProp¬ P))
           (uncurry extract)
           (hyp some-x≠y a)
