{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Data.Int using (ℤ; _+_)
open import Cubical.Data.Int.MoreInts.DeltaInt hiding (zero; succ)
open import Cubical.Data.Nat using (ℕ; zero) renaming (suc to succ)


ℤ≡DeltaInt : ℤ ≡ DeltaInt
ℤ≡DeltaInt = sym DeltaInt≡ℤ

_+Δ_ : DeltaInt → DeltaInt → DeltaInt
_+Δ_ = transport (λ i → ℤ≡DeltaInt i → ℤ≡DeltaInt i → ℤ≡DeltaInt i) _+_

x y : DeltaInt
x = (succ zero) ⊖ (succ (succ zero))
y = (succ (succ zero)) ⊖ (succ (succ zero))

sum : DeltaInt
sum = x +Δ y
