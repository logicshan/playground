{-# OPTIONS --no-postfix-projections #-}

open import Data.Nat.Base using (ℕ)
open import Data.Bool.Base using (Bool; true; false)

record MyRecord : Set where
  field
    field1 : ℕ
    field2 : Bool
open MyRecord

myRecord : MyRecord
field1 myRecord = 1
field2 myRecord = true

myRecord2 : MyRecord
field1 myRecord2 = 2
field2 myRecord2 = false

myRecord3 : MyRecord
field1 myRecord3 = {!!}
field2 myRecord3 = {!!}
