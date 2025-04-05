
module Desc where

import Level

open import Data.Empty using (⊥)
open import Data.Product
open import Data.Unit using (⊤)

private variable ℓ ℓ' : Level.Level

module Inductive where
  data Desc ℓ : Set (Level.suc ℓ) where
    [] : Desc ℓ
    ·∷_ : Desc ℓ → Desc ℓ
    ·^_∷_ : (A : Set ℓ) → Desc ℓ → Desc ℓ
    tag : (T : Set) → (T → Desc ℓ) → Desc ℓ
    fld : (A : Set ℓ) → (A → Desc ℓ) → Desc ℓ

  infixr 0 fld
  syntax fld A (λ x → D) = [ x ∈ A ] ∷ D

  infixr 0 _∷_
  _∷_ : Set ℓ → Desc ℓ → Desc ℓ
  A ∷ D = fld A (λ _ → D)

  [_] : Desc ℓ → Set ℓ → Set ℓ
  [ [] ] X = Level.Lift _ ⊤
  [ ·∷ D ] X = X × [ D ] X
  [ ·^ A ∷ D ] X = (A → X) × [ D ] X
  [ tag T D ] X = Σ[ t ∈ T ] [ D t ] X
  [ fld A D ] X = Σ[ a ∈ A ] [ D a ] X

  data μ (D : Desc ℓ) : Set ℓ where
    inj : [ D ] (μ D) → μ D

  data Free (D : Desc ℓ) (A : Set ℓ) : Set ℓ where
    pure : A → Free D A
    roll : [ D ] (Free D A) → Free D A

  □ : (D : Desc ℓ) {X : Set ℓ} (P : X → Set ℓ) → [ D ] X → Set ℓ
  □ [] P _ = Level.Lift _ ⊤
  □ (·∷ D) P (x , v) = P x × □ D P v
  □ (·^ A ∷ D) P (f , v) = (∀ a → P (f a)) × □ D P v
  □ (tag T D) P (t , v) = □ (D t) P v
  □ (fld A D) P (a , v) = □ (D a) P v

  module _ {ℓ}
    where
    induct
      : (D : Desc ℓ)
      → (P : μ D → Set ℓ)
      → (φ : ∀ v → □ D P v → P (inj v))
      → ∀ v → P v
    inducts
      : (D : Desc ℓ)
      → (P : μ D → Set ℓ)
      → (φ : ∀ v → □ D P v → P (inj v))
      → ∀ E v → □ E P v

    induct D P φ (inj v) = φ v (inducts D P φ D v)

    inducts D P φ [] t = t
    inducts D P φ (·∷ E) (r , v) = induct D P φ r , inducts D P φ E v
    inducts D P φ (·^ A ∷ E) (f , v) = (λ a → induct D P φ (f a)) , inducts D P φ E v
    inducts D P φ (tag T E) (t , v) = inducts D P φ (E t) v 
    inducts D P φ (fld A E) (a , v) = inducts D P φ (E a) v



module Indexed where
  data Desc ℓ (I : Set ℓ) : Set (Level.suc ℓ) where
    _⟩ : I → Desc ℓ I
    ·_∷_ : I → Desc ℓ I → Desc ℓ I
    tag : (T : Set) → (T → Desc ℓ I) → Desc ℓ I



  [_] : {I : Set ℓ} → (D : Desc ℓ I) → (I → Set ℓ) → Set ℓ
  [ i ⟩ ] X = X i
  [ · i ∷ D ] X = X i × [ D ] X
  [ tag T D ] X = Σ[ t ∈ T ] [ D t ] X 

  data μ {I : Set ℓ} (D : I → Desc ℓ I) (i : I) : Set ℓ where
    inj : [ D i ] (μ D) → μ D i
