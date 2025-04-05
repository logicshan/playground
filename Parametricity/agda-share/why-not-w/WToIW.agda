
module WToIW where

open import Level

open import Function

open import Data.Product
open import Data.Container as Nm
open import Data.W as Nm
open import Data.Container.Indexed as Ix
open import Data.W.Indexed as Ix

open import Relation.Binary.PropositionalEquality as Eq

variable
  c r ℓ : Level

-- Encoding indexed W-types using regular W-types and the identity
-- type, with the correct judgmental behavior. No K or extensionality
-- required.
module _ (I : Set) (C : Ix.Container I I c r) where
  Lax : Nm.Container c r
  Lax .Shape = Σ I (Command C)
  Lax .Position = Response C ∘ proj₂

  canonical : I → Nm.W Lax → Set (c ⊔ r)
  canonical i (sup ((j , x) , f))
    = (j ≡ i) × (∀ y → canonical (C .next x y) (f y))

  EW : I → Set _
  EW i = Σ _ (canonical i)

  zup : ∀{i} → Ix.⟦ C ⟧ EW i → EW i
  zup {i} (c , f) = sup ((i , c) , proj₁ ∘ f) , Eq.refl , proj₂ ∘ f

  module _
    (P : Σ I EW → Set ℓ)
    (φ : ∀{i} → (cs : Ix.⟦ C ⟧ EW i) → Ix.□ C P (i , cs) → P (i , zup cs))
    where
    induct : ∀ i w → P (i , w)
    induct i (w , c) = Nm.induction Q case w i c where
      Q : Nm.W Lax → Set _
      Q w = ∀ i (c : canonical i w) → P (i , w , c)

      case : ∀{t} → Nm.□ Lax Q t → Q (sup t)
      case {(j , x) , f} v i (e , subcanon)
        = J R e (φ (x , (λ y → f y , subcanon y))
                   (λ y → v .□.proof y _ (subcanon y)))
        where
        R : (i : I) → j ≡ i → Set _
        R i e = P (i , sup ((j , x) , f) , e , subcanon)
        
    induct-lemma : ∀ i c f
      → induct i (zup (c , f))
      ≡ φ (c , f) λ y → induct _ (f y)
    induct-lemma i c f = Eq.refl
