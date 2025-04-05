{-# OPTIONS --type-in-type #-}

module Nest where

data Nat : Set where
  z : Nat
  s : Nat → Nat

induction : ∀{P : Nat → Set} → (∀{m} → P m → P (s m)) → P z → (n : Nat) → P n
induction f n z     = n
induction f n (s m) = f (induction (λ {k} → f {k}) n m)

nest : ∀{a : Set} {f : Set → Set}
      → (n : Nat) → (∀{a} → a → f a)
      → a → induction f a n
nest {a} {f} n g x = induction {induction f a} g x n
