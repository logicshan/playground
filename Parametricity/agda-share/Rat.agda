
-- A smart constructor for values of ℚ

module Rat where

open import Data.Maybe
open import Data.Product
open import Data.Nat as Nat using (ℕ ; _*_ ; suc)
open import Data.Nat.Coprimality using (gcd′ ; GCD′ ; gcd-* ; coprime? ; Coprime)
open import Data.Integer as Int using (ℤ ; -[1+_] ; +_ ; _◃_ ; ∣_∣)
open import Data.Integer.Properties using (abs-◃)
open import Data.Rational
open import Data.Sign as Sign using (Sign)

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; subst ; sym)
open import Relation.Nullary
open import Relation.Nullary.Decidable

truthFromWitness : ∀{P} {Q : Dec P} → P → True Q
truthFromWitness {Q = no ¬p} p = ¬p p
truthFromWitness {Q = yes _} p = _

build : Sign → (n d : ℕ) {≢0 : False (Nat._≟_ d 0)} -> ℚ
build sgn num          den with gcd′ num den
build sgn .(num' * d) .0 {} | d , gcd-* {.d} num' 0 cop
build sgn .(num' * d) .(suc den' * d) | d , gcd-* num' (suc den') cop
  = record { numerator = sgn ◃ num'
           ; denominator-1 = den'
           ; isCoprime = proof
           }
 where
 proof₀ : Coprime ∣ sgn ◃ num' ∣ (suc den')
 proof₀ = subst (λ n → Coprime n (suc den')) (sym (abs-◃ sgn num')) cop
 proof : True (coprime? ∣ sgn ◃ num' ∣  (suc den'))
 proof = truthFromWitness {Coprime ∣ sgn ◃ num' ∣ (suc den')} proof₀


infix 4 _%_
_%_ : ℤ → ℕ → Maybe ℚ
z        % 0  = nothing
-[1+ m ] % suc n = just (build Sign.- (suc m) (suc n))
+ m      % suc n = just (build Sign.+ m (suc n))

