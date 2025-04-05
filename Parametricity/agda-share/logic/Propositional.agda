
module Propositional where

open import Data.Unit using (⊤)
open import Data.Product
open import Data.Nat

open import SnocList

open import Propositional.Syntax
open import Propositional.Deduction
open import Propositional.Valuation

soundness₀ : ∀{B Bs} → (ded : Deduction [] (Bs :: B))
           → Tautology B
soundness₀ ded = d-wf-induct s-aux' ded
 where
 P : ∀{Bs} → Deduction [] Bs → Set
 P {[]}      _ = ⊤
 P {Bs :: B} _ = Tautology B

 s-aux : ∀{B} Bs → (ded : Deduction [] (Bs :: B))
       → (∀ B' Bs' (ded' : Deduction [] (Bs' :: B')) → d-length ded' < d-length ded → Tautology B')
       → Tautology B
 s-aux Bs (axiom₁ {A} {B} _)        _ = taut₁ {A} {B}
 s-aux Bs (axiom₂ {A} {B} {C} _)        _ = taut₂ {A} {B} {C}
 s-aux Bs (axiom₃ {A} _)        _ = taut₃ {A}
 s-aux Bs (assumption () _) _
 s-aux Bs (modus-ponens {B₁} {B} B₁⊃B∈ B₁∈ ded) rec with ∈-deduction B₁⊃B∈ ded | ∈-deduction B₁∈ ded
 ... | (s⊃ , d⊃ , ≤⊃) | (s₁ , d₁ , ≤₁) = taut-ponens {B₁} {B} (rec (B₁ ⊃ B) s⊃ d⊃ (s≤s ≤⊃))
                                                              (rec B₁ s₁ d₁ (s≤s ≤₁))

 s-aux' : ∀ Bs (ded : Deduction [] Bs)
        → (∀ Bs' (ded' : Deduction [] Bs') → d-length ded' < d-length ded → P ded')
        → P ded
 s-aux' [] _ _ = _
 s-aux' (Bs :: B) ded φ = s-aux Bs ded (λ B' Bs' ded' m<n → φ (Bs' :: B') ded' m<n)

soundness : ∀{B} → (∀ As → As ⊢ B) → Tautology B
soundness ⊢B with ⊢B []
... | (_ , ded) = soundness₀ ded



