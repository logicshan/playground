
module Coexp where

open import Function

open import Data.Product
open import Data.Sum

open import Relation.Binary.PropositionalEquality hiding ([_])

module K (R : Set)
         -- eta rule for sums
         (eta : ∀{A B C : Set} (f : A ⊎ B → C) →  [ f ∘ inj₁ , f ∘ inj₂ ] ≡ f)
  where
  _⇒_ : Set → Set → Set
  A ⇒ B = A → (B → R) → R

  _-_ : Set → Set → Set
  A - B = A × (B → R)

  -- Make sure _⊎_ is really a sum here
  module S (A B C : Set) (f : A ⇒ C) (g : B ⇒ C) where
    [f,g] : (A ⊎ B) ⇒ C
    [f,g] = [ f , g ]

    lemma₁ : ∀ x → ([f,g] ∘ inj₁) x ≡ f x
    lemma₁ x = refl

    lemma₂ : ∀ y → ([f,g] ∘ inj₂) y ≡ g y
    lemma₂ y = refl

    lemma₃ : ∀ h → (∀ x → (h ∘ inj₁) x ≡ f x)
                 → (∀ y → (h ∘ inj₂) y ≡ g y)
                 → ∀ s → h s ≡ [f,g] s
    lemma₃ h l r (inj₁ x) = l x
    lemma₃ h l r (inj₂ y) = r y


  module Adj (A B C : Set) where
    to : (A ⇒ (B ⊎ C)) → ((A - B) ⇒ C)
    to f (x , g) k = f x ([ g , k ])

    from : ((A - B) ⇒ C) → (A ⇒ (B ⊎ C))
    from f x k = f (x , k ∘ inj₁) (k ∘ inj₂)

    iso₁ : ∀ f x k → from (to f) x k ≡ f x k
    iso₁ f x k = cong (f x) (eta k)

    iso₂ : ∀ g p k → to (from g) p k ≡ g p k
    iso₂ g p k = refl
