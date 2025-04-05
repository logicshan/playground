
module NBP.Prod.Terms.Core where

open import Cubical.Foundations.Prelude

open import NBP.Prod.Types

module Stx where
  data Tm (Γ : Cx) : Ty → Type where
    va : A ∈ Γ → Tm Γ A
    tt : Tm Γ ⊤

    _,_ : Tm Γ A → Tm Γ B → Tm Γ (A * B)
    π₁ : Tm Γ (A * B) → Tm Γ A
    π₂ : Tm Γ (A * B) → Tm Γ B

    la : Tm (Γ ∷ A) B → Tm Γ (A ⇒ B)
    _$_ : Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B

module Sem where
  data No (Γ : Cx) : Ty → Type
  data Ne (Γ : Cx) : Ty → Type

  data No Γ where
    tt : No Γ ⊤

    _,_ : No Γ A → No Γ B → No Γ (A * B)

    la : No (Γ ∷ A) B → No Γ (A ⇒ B)

    ne : Ne Γ A → No Γ A

  data Ne Γ where
    va : A ∈ Γ → Ne Γ A

    π₁ : Ne Γ (A * B) → Ne Γ A
    π₂ : Ne Γ (A * B) → Ne Γ B

    _$_ : Ne Γ (A ⇒ B) → No Γ A → Ne Γ B
