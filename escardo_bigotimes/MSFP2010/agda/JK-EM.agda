module JK-EM where

open import Logic
open import JK-Monads

Decidable : Ω → Ω → Ω
Decidable R A = A ∨ (A → R)

-- J- and K-versions of excluded middle.

J-EM : {R A : Ω} →
----
       J R (Decidable R A) 

J-EM = λ p → ∨-intro₁(λ a → p (∨-intro₀ a))


K-EM : {R A : Ω} →
----
       K R (Decidable R A) 

K-EM = J-K(J-EM)

-- So, in a way, J-excluded-middle is stronger than K-excluded middle.

negation-of-decidable-is-decidable : {R A : Ω} →
----------------------------------
     Decidable R A → Decidable R (A → R)

negation-of-decidable-is-decidable (∨-intro₀ a) = ∨-intro₁(λ p → p a)
negation-of-decidable-is-decidable (∨-intro₁ p) = ∨-intro₀ p
