import Axiom.Extensionality.Propositional as Ext

open import Level
open import Function

open import Data.Empty
open import Data.Nat
open import Data.Product

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

module ChurchLaw
  (T : ℕ → ℕ → ℕ → Set)
  (T? : ∀ #f m p → Dec (T #f m p))
  (U : ℕ → ℕ)
  (det : ∀{#f m p q} → T #f m p → T #f m q → U p ≡ U q)
  (church : ∀(f : ℕ → ℕ) → ∃[ #f ] ∀ m → ∃[ p ] (T #f m p × U p ≡ f m))
  (ext : Ext.Extensionality 0ℓ 0ℓ)
  (HP : ¬ ∀{#f m} → Dec (∀ p → ¬ T #f m p))
  where

  variable
    #f m p : ℕ
    f g : ℕ → ℕ

  ¬H : ℕ → ℕ → Set
  ¬H #f m = ∀ p → ¬ T #f m p

  # : (ℕ → ℕ) → ℕ
  # f = church f .proj₁

  #-total : (f : ℕ → ℕ) → ∀ m → ∃[ p ] T (# f) m p
  #-total f m with church f .proj₂ m
  ... | (p , t , _) = p , t

  * : (∀ m → ∃[ p ] T #f m p) → ℕ → ℕ
  * total m = U (total m .proj₁)

  compute-lemma : * (#-total f) ≡ f
  compute-lemma {f} = ext sub
    where
    sub : ∀ m → * (#-total f) m ≡ f m
    sub m with church f .proj₂ m
    ... | (_ , _ , e) = e

  #z : ℕ
  #z = # (λ _ → 0)

  t : ℕ → ℕ → ℕ → ℕ
  t #f m p with T? #f m p
  ... | yes _ = 1
  ... | no  _ = 0

  t0→¬T : t #f m p ≡ 0 → ¬ T #f m p
  t0→¬T {#f} {m} {p} eq with T? #f m p
  ... | no np = np
  t0→¬T () | yes _

  #t : ℕ → ℕ → ℕ
  #t #f m = # (t #f m)

  #-inj : # f ≡ # g → f ≡ g
  #-inj {f} {g} heq = ext sub
    where
    open ≡-Reasoning
    sub : ∀ m → f m ≡ g m
    sub m with church f .proj₂ m | church g .proj₂ m
    ... | p , tfmp , peq | q , tgmq , qeq
      = begin
          f m ≡⟨ sym peq ⟩
          U p ≡⟨ det (subst (λ #h → T #h m p) heq tfmp) tgmq ⟩
          U q ≡⟨ qeq ⟩
          g m ∎


  diverge-lemma₀ : ¬H #f m → t #f m p ≡ 0
  diverge-lemma₀ { #f} {m} {p} ¬Hfm with T? #f m p
  ... | no  _ = refl
  ... | yes q = ⊥-elim $ ¬Hfm p q

  diverge-lemma₁ : ¬H #f m → #t #f m ≡ #z
  diverge-lemma₁ ¬Hfm = cong # ∘ ext $ λ p → diverge-lemma₀ ¬Hfm

  diverge-lemma₂ : #t #f m ≡ #z → ¬H #f m
  diverge-lemma₂ {#f} {m} heq p = t0→¬T ∘ cong (_$ p) $ #-inj heq

  ¬H? : Dec (¬H #f m)
  ¬H? { #f} {m} with #t #f m ≟ #z
  ... | yes eq = yes (diverge-lemma₂ eq)
  ... | no ¬eq = no (¬eq ∘ diverge-lemma₁)


  bad : ⊥
  bad = HP ¬H?
