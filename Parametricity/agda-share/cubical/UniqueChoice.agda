
module UniqueChoice where

open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

module UC
  (A B : Type)
  (C : A -> B -> Type)
  (Cp : ∀ x y → isProp (C x y))
  (fun : ∀ x → ∃[ y ∈ B ] C x y × ∀ z → C x z -> y ≡ z)
  where
  C⇒p : ∀(h : A -> B) → isProp (∀ x → C x (h x))
  C⇒p h = isPropΠ λ x → Cp x (h x)

  f₀ : (x : A) -> isContr (Σ[ y ∈ B ] C x y)
  f₀ x = PT.rec isPropIsContr dakka (fun x) where
    dakka : (Σ[ y ∈ B ] C x y × ∀ z → C x z -> y ≡ z) -> isContr (Σ B (C x))
    dakka (y , Cxy , yz) = λ where
      .fst → y , Cxy
      .snd (z , Cxz) → Σ≡Prop (Cp x) (yz z Cxz)

  f : A -> B
  f x = f₀ x .fst .fst

  Cf : ∀ x → C x (f x)
  Cf x = f₀ x .fst .snd

  f! : ∀ g → (∀ x → C x (g x)) -> f ≡ g
  f! g Cg i x = f₀ x .snd (g x , Cg x) i .fst

  uc : isContr (Σ[ f ∈ (A -> B) ] ∀ x → C x (f x))
  uc = (f , Cf) , λ{ (g , Cg) → Σ≡Prop C⇒p (f! g Cg) }
