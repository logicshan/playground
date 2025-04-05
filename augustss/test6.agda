open import Agda.Builtin.Int
open import Agda.Builtin.Bool

-- Example usage:
test1 : Bool
test1 = primIntegerLess 3 5        -- returns true

test2 : Bool
test2 = primIntegerEquals 4 4      -- returns true

test3 : Bool
test3 = primIntegerGreaterEq 6 5   -- returns true
