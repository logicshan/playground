
module IRDomain where

open import Level
open import Function hiding (_↪_)

open import Data.Bool
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Relation.Binary.PropositionalEquality

variable
  ℓ : Level
  A B : Set

Sys : Set₁
Sys = Σ[ U ∈ Set ] (U → Set)

isInjective : (A → B) → Set
isInjective f = ∀ x y → f x ≡ f y → x ≡ y

_↪_ : Set → Set → Set
A ↪ B = Σ (A → B) isInjective

_≼_ : Sys → Sys → _
(U , φ) ≼ (V , ψ) = Σ[ (𝕗 , inj) ∈ U ↪ V ] (∀ u → φ u ≡ ψ (𝕗 u))

isDirected : ∀{I : Set ℓ} (T : I → Sys) → Set _
isDirected T = ∀ i j → ∃[ k ] (T i ≼ T k) × (T j ≼ T k)

id-directed : isDirected id
id-directed (U , φ) (V , ψ) = λ where
    .proj₁ .proj₁ → U ⊎ V
    .proj₁ .proj₂ (inj₁ x) → φ x
    .proj₁ .proj₂ (inj₂ y) → ψ y
    .proj₂ .proj₁ .proj₁ .proj₁ → inj₁
    .proj₂ .proj₁ .proj₁ .proj₂ x y → cover
    .proj₂ .proj₁ .proj₂ _ → refl
    .proj₂ .proj₂ .proj₁ .proj₁ → inj₂
    .proj₂ .proj₂ .proj₁ .proj₂ x y → cover
    .proj₂ .proj₂ .proj₂ _ → refl
  where
  Cover : (s t : U ⊎ V) → Set
  Cover (inj₁ x) (inj₁ y) = x ≡ y
  Cover (inj₁ x) (inj₂ y) = ⊤
  Cover (inj₂ x) (inj₁ y) = ⊤
  Cover (inj₂ x) (inj₂ y) = x ≡ y

  cover : ∀{s t} → s ≡ t → Cover s t
  cover {s} p
    = subst (Cover s) p
        (case s return (λ s → Cover s s) of
           λ { (inj₁ _) → refl ; (inj₂ _) → refl })

module _
  (lim : (f : Sys → Sys) → isDirected f → Sys)
  (≼-lim : ∀ f d s → f s ≼ lim f d)
  where

  id-lim = lim id id-directed
  ≼-id-lim = ≼-lim id id-directed

  U : Set
  U = id-lim .proj₁

  El : U → Set
  El = id-lim .proj₂

  pt : Set → ⊤ → Set
  pt S _ = S

  ι : Set → U
  ι S = ≼-id-lim (⊤ , pt S) .proj₁ .proj₁ _

  problem₁ : ∀ S → S ≡ El (ι S)
  problem₁ S = ≼-id-lim (⊤ , pt S) .proj₂ _
