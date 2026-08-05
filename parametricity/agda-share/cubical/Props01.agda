module Props01 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Foundations.HLevels
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum
open import Cubical.Relation.Nullary


variable
  ℓ : Level
  X Y : Type ℓ
  y : Y

lemma₀ : (X → isProp X) → isProp X
lemma₀ f x = f x x

lemma₁ : (X → isContr X) → isProp X
lemma₁ f x = isContr→isProp (f x) x

lemma₂ : isProp X → isProp (X ≡ Y)
lemma₂ Xprp = lemma₀ (λ P → isOfHLevel≡ 1 Xprp (subst isProp P Xprp))

lemma₃ : (P : X ≡ Y) → PathP (λ i → P i) (transport⁻ P y) y
lemma₃ {y = y} P i = transp (λ j → P (i ∨ ~ j)) i y

module _ (P : Type) (Pprp : isProp P) where
  PP : Type → _
  PP B = ∥ (P ≡ B) ⊎ ((¬ P) ≡ B) ∥

  A : Type _
  A = Σ[ B ∈ Type ] PP B

  T : Type _
  T = Σ[ X ∈ A ] X .fst

  lemma₄ : P → isContr T
  lemma₄ p .fst = (P , ∣ inl refl ∣) , p
  lemma₄ p .snd ((X , t) , x) = ΣPathP ((ΣPathP (P≡X , r≡t)) , p≡x)
    where
    ¬P≢X : ¬ (¬ P) ≡ X
    ¬P≢X q = transport (λ i → q (~ i)) x p

    P≡X : P ≡ X
    P≡X = PT.rec (lemma₂ Pprp) (Sum.rec (λ x → x) (Empty.rec ∘ ¬P≢X)) t

    r≡t : PathP (λ i → PP (P≡X i)) ∣ inl refl ∣ t
    r≡t = isOfHLevel→isOfHLevelDep 1 {B = PP} (λ _ → squash) ∣ inl refl ∣ t P≡X

    p≡x : PathP (λ i → P≡X i) p x
    p≡x = subst (λ q → PathP (λ i → P≡X i) q _) (Pprp _ p) (lemma₃ P≡X)

  lemma₅ : ¬ P → isContr T
  lemma₅ ¬p .fst = ((¬ P) , ∣ inr refl ∣) , ¬p
  lemma₅ ¬p .snd ((X , t) , x) = ΣPathP ((ΣPathP (¬P≡X , r≡t)) , p≡x)
    where
    P≢X : ¬ P ≡ X
    P≢X q = ¬p (transport (λ i → q (~ i)) x)

    ¬P≡X : (¬ P) ≡ X
    ¬P≡X = PT.rec (lemma₂ (isProp¬ P))
             (Sum.rec (Empty.rec ∘ P≢X) λ x → x) t

    r≡t : PathP (λ i → PP (¬P≡X i)) ∣ inr refl ∣ t
    r≡t = isOfHLevel→isOfHLevelDep 1 {B = PP}
            (λ _ → squash) ∣ inr refl ∣ t ¬P≡X

    p≡x : PathP (λ i → ¬P≡X i) ¬p x
    p≡x = subst (λ q → PathP (λ i → ¬P≡X i) q _) (isProp¬ P _ ¬p) (lemma₃ ¬P≡X)

  lemma₆ : isProp T
  lemma₆ = lemma₁ λ where
      ((X , t) , x) → PT.rec isPropIsContr (disc x) t
    where
    disc : X → (P ≡ X) ⊎ ((¬ P) ≡ X) → isContr T
    disc x (inl P≡X) = lemma₄ (transport (λ i → P≡X (~ i)) x)
    disc x (inr ¬P≡X) = lemma₅ (transport (λ i → ¬P≡X (~ i)) x)
