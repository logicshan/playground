module ParamProj where

open import Data.Product
open import Data.Sum
open import Data.Unit

open import Relation.Binary.PropositionalEquality

variable
  A B : Set

Rel : Set → Set → _
Rel A B = A → B → Set

Δ : Rel A B → A × A → B × B → _
Δ R (w , y) (x , z) = R w x × R y z

module Para
    (f : ∀ A → A × A → A)
    (para-f : ∀ A B (R : Rel A B) p q → Δ R p q → R (f A p) (f B q))
  where
  Two : _
  Two = ⊤ ⊎ ⊤

  pattern zro = inj₁ _
  pattern one = inj₂ _

  two : Two × Two
  two = zro , one

  Dec : A × A → Rel A Two
  Dec p z zro = z ≡ proj₁ p
  Dec p z one = z ≡ proj₂ p

  lemma₀ : ∀(p : A × A) → Δ (Dec p) p two
  lemma₀ (x , y) = refl , refl

  lemma₁ : ∀ p → f Two two ≡ zro → f A p ≡ proj₁ p
  lemma₁ {A = A} p eq
    = subst (Dec p (f A p)) eq (para-f A Two (Dec p) p two (lemma₀ p))

  lemma₂ : ∀ p → f Two two ≡ one → f A p ≡ proj₂ p
  lemma₂ {A = A} p eq
    = subst (Dec p (f A p)) eq (para-f A Two (Dec p) p two (lemma₀ p))

  isProj : (∀ A p → f A p ≡ proj₁ p) ⊎ (∀ A p → f A p ≡ proj₂ p)
  isProj with f Two two | inspect (f Two) two
  ... | inj₁ _ | [ eq ] = inj₁ (λ A p → lemma₁ p eq)
  ... | inj₂ _ | [ eq ] = inj₂ (λ A p → lemma₂ p eq)
