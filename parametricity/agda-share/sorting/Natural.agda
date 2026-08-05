
module Natural where

open import Logic

data Nat : Set where
  zero : Nat
  succ : Nat -> Nat

{-# BUILTIN NATURAL Nat  #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     succ #-}

one = succ zero

infix 50 _<=_
_<=_ : Nat -> Nat -> Prop
zero <= n        = ⊤
succ m <= zero   = ⊥
succ m <= succ n = m <= n

dec-<= : (m : Nat) -> Decidable (\n -> m <= n)
dec-<= zero n = pfl True
dec-<= (succ m) zero = pfr (\())
dec-<= (succ m) (succ n) = dec-<= m n

≡-succ : {m n : Nat} -> m ≡ n -> succ m ≡ succ n
≡-succ ≡-refl = ≡-refl

≡-pred : {m n : Nat} -> succ m ≡ succ n -> m ≡ n
≡-pred ≡-refl = ≡-refl

≢-succ : {m n : Nat} -> ¬ (m ≡ n) -> ¬ (succ m ≡ succ n)
≢-succ m≢n sm≡sn = m≢n (≡-pred sm≡sn) 

dec-≡-Nat : (m : Nat) -> Decidable (_≡_ m)
dec-≡-Nat zero    zero      = pfl ≡-refl 
dec-≡-Nat (succ m) (succ n) with dec-≡-Nat m n
...                         | pfl m≡n = pfl (≡-succ m≡n)
...                         | pfr m≢n = pfr (≢-succ m≢n)
dec-≡-Nat zero     (succ n) = pfr (\())
dec-≡-Nat (succ m) zero     = pfr (\()) 


trans-<= : {i j k : Nat} -> i <= j -> j <= k -> i <= k
trans-<= {zero}                     pf-ij pf-jk = True 
trans-<= {succ i} {zero}            ()    pf-jk
trans-<= {succ i} {succ j} {zero}   pf-ij ()
trans-<= {succ i} {succ j} {succ k} pf-ij pf-jk = trans-<= pf-ij pf-jk 


∀trans-<= : {x y : Nat} -> x <= y -> (k : Nat) -> y <= k -> x <= k
∀trans-<= x<=y k = trans-<= {_} {_} {k} x<=y

¬<=->= : {i j : Nat} -> ¬ (i <= j) -> j <= i
¬<=->= {zero}   {zero}   pf = True 
¬<=->= {zero}   {succ j} pf = pf True  
¬<=->= {succ i} {zero}   pf = True 
¬<=->= {succ i} {succ y} pf = ¬<=->= pf 
