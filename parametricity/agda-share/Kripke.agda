
module Kripke where

open import Data.Nat
open import Data.Product
open import Data.Unit

data Pr : Set where
  _⊃_ : Pr -> Pr -> Pr

infixr 30 _⊃_

data Cx : Set where
  [] : Cx
  _∷_ : Cx -> Pr -> Cx

infixl 20 _∷_

variable
  Γ : Cx
  P Q : Pr

infix 5 _⊢_
data _⊢_ : Cx -> Pr -> Set where
  to : Γ ∷ P ⊢ P
  po : Γ ⊢ Q -> Γ ∷ P ⊢ Q
  la : Γ ∷ P ⊢ Q -> Γ ⊢ P ⊃ Q
  ap : Γ ⊢ P ⊃ Q -> Γ ⊢ P -> Γ ⊢ Q

derived : [] ⊢ ((((P ⊃ Q) ⊃ P) ⊃ P) ⊃ Q) ⊃ Q
derived = la (ap to (la (ap to (la (ap (po (po to)) (la (po to)))))))

module Kripke
  (W : Set)
  (_≤_ : W -> W -> Set)
  (≤-refl : ∀ w → w ≤ w)
  (≤-trans : ∀{u v w} → u ≤ v -> v ≤ w -> u ≤ w)
  where
  _∣⊢_ : W -> Pr -> Set
  w₀ ∣⊢ P ⊃ Q = ∀ w₁ → w₀ ≤ w₁ -> w₁ ∣⊢ P -> w₁ ∣⊢ Q

  mono : ∀{w₀ w₁} → w₀ ≤ w₁ -> w₀ ∣⊢ P -> w₁ ∣⊢ P
  mono {P ⊃ Q} w₀≤w₁ f w₂ w₁≤w₂ = f w₂ (≤-trans w₀≤w₁ w₁≤w₂)

  ∣_∣ : Cx -> W -> Set
  ∣ [] ∣ _ = ⊤
  ∣ Γ ∷ P ∣ w = ∣ Γ ∣ w × (w ∣⊢ P)

  ∣∣-mono : ∀{w₀ w₁} → w₀ ≤ w₁ -> ∣ Γ ∣ w₀ -> ∣ Γ ∣ w₁
  ∣∣-mono {[]}    _        _    = _
  ∣∣-mono {Γ ∷ x} pre (env , v) = ∣∣-mono {Γ} pre env , mono pre v

  kriptic : Γ ⊢ P -> ∀ w → ∣ Γ ∣ w → w ∣⊢ P
  kriptic to w₀ (_ , v) = v
  kriptic (po dv) w₀ (env , _) = kriptic dv w₀ env
  kriptic (la dv) w₀ env w₁ w₀≤w₁ P₁ =
    kriptic dv w₁ (∣∣-mono w₀≤w₁ env , P₁)
  kriptic (ap df dv) w₀ env =
    kriptic df w₀ env w₀ (≤-refl w₀) (kriptic dv w₀ env)

  test = {!kriptic derived!}
  -- λ w₀ env w₁ w₀≤w₁ P₁ →
  --   P₁ w₁ (≤-refl w₁)
  --   (λ w₂ w₀≤w₂ P₂ →
  --     P₂ w₂ (≤-refl w₂)
  --     (λ w₃ w₀≤w₃ P₃ →
  --         P₁ w₃ (≤-trans w₀≤w₂ (≤-trans w₀≤w₃ (≤-refl w₃)))
  --         (λ w₄ w₀≤w₄ P₄ → mono w₀≤w₄ P₃)))
