
module MFin where

open import Data.Maybe
open import Data.Function
open import Data.Nat hiding (_+_ ; _*_)
open import Data.Fin hiding (_+_ ; fold)

-- modular arithmetic
msuc : ∀{k} → Fin k → Fin k
msuc {zero} ()
msuc {suc k} i = maybe id zero (aux i)
 where
 aux : ∀{k} → Fin (suc k) → Maybe (Fin (suc k))
 aux {zero}  zero = nothing
 aux {zero}  (suc ())
 aux {suc k} zero = just (suc zero)
 aux {suc k} (suc i) with aux {k} i
 ... | nothing = nothing
 ... | just i' = just (suc i')

-- I go through ℕ to avoid termination problems. Defining
-- _+_ and _*_ directly would require bumping up the recursive
-- argument's index by one, which would upset the termination
-- checker. You could also define them in two steps by using
-- two different indices (the first of which gets ignored), and
-- fixing them to be equal in the 'real' function, but that's
-- no less work.
_⊕_ : ∀{k} → ℕ → Fin k → Fin k
n ⊕ j = fold j msuc n

_+_ : ∀{k} → Fin k → Fin k → Fin k
i + j = toℕ i ⊕ j

_⊗_ : ∀{k} → ℕ → Fin k → Fin k
_⊗_ {zero}  _ ()
_⊗_ {suc k} n j = fold (msuc zero) (_+_ j) n

_*_ : ∀{k} → Fin k → Fin k → Fin k
i * j = toℕ i ⊗ j

_^_ : ∀{k} → Fin k → ℕ → Fin k
_^_ {zero}  () _
_^_ {suc k} i  n = fold (msuc zero) (_*_ i) n

f0 : Fin 5
f0 = zero

f1 : Fin 5
f1 = msuc f0

f2 : Fin 5
f2 = msuc f1

f3 : Fin 5
f3 = msuc f2

f4 : Fin 5
f4 = msuc f3

f5 : Fin 5
f5 = msuc f4
