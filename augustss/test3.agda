open import Data.Unit.Base using (⊤)
open import Agda.Builtin.Nat
open import Data.Integer using (ℤ;+_;-_)
open import Data.Integer.Literals
open import Agda.Builtin.FromNeg using (Negative)
open import Agda.Builtin.FromNat using (Number)


--{-# BUILTIN FROMNEG fromNeg #-}
--{-# BUILTIN FROMNAT fromNat #-}

instance
  NumberNat : Number Nat
  NumberNat = record
    { Constraint = λ _ → ⊤
    ; fromNat    = λ n → n
    }

  ℤ-Negative : Negative ℤ
  ℤ-Negative = negative

  ℤ-Number : Number ℤ
  ℤ-Number = number

x : ℤ
x = -1

y : ℤ
y = + 0
