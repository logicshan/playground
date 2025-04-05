open import Data.Unit.Base using (⊤)
open import Agda.Builtin.Nat
open import Agda.Builtin.Int
open import Agda.Builtin.FromNeg using (Negative)
open import Agda.Builtin.FromNat

instance
  NumberNat : Number Nat
  NumberNat = record
    { Constraint = λ _ → ⊤
    ; fromNat    = λ n → n
    }

  NumberInt : Number Int
  NumberInt = record
    { Constraint = λ _ → ⊤
    ; fromNat    = λ n → pos n
    }

  NegativeInt : Negative Int
  NegativeInt = record
    { Constraint = λ _ → ⊤  -- No constraints, always valid
    ; fromNeg    = λ n → negsuc (n - 1)  -- Convert natural number to negative integer
    }

example : Int
example = -5  -- This will be desugared to fromNeg 5

example' : Nat
example' = 1

example'' : Int
example'' = 1
