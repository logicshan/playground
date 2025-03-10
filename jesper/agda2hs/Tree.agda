{-# OPTIONS --erasure #-}

import Relation.Binary.PropositionalEquality as Eq
-- open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq using (cong)
open import Haskell.Prelude

maxNat : Nat → Nat → Nat
maxNat zero    n       = n
maxNat (suc m) zero    = suc m
maxNat (suc m) (suc n) = suc (maxNat m n)

data Tree (a : Set) : (@0 height : Nat) → Set where
  Tip : Tree a 0
  Bin : ∀ {@0 l r}
      → a → Tree a l → Tree a r → Tree a (suc (maxNat l r))
{-# COMPILE AGDA2HS Tree #-}

transport : (p : @0 a → Set) {@0 m n : a}
          → @0 m ≡ n → p m → p n
transport p refl t = t
{-# COMPILE AGDA2HS transport transparent #-}

@0 max-comm : (@0 l r : Nat) → maxNat l r ≡ maxNat r l
max-comm zero    zero    = refl
max-comm zero    (suc r) = refl
max-comm (suc l) zero    = refl
max-comm (suc l) (suc r) = cong suc (max-comm l r)

mirror : ∀ {@0 h} → Tree a h → Tree a h
mirror Tip =  Tip
mirror {a = a} (Bin {l} {r} x lt rt)
  = transport (Tree a)
              (cong suc (max-comm r l))
              (Bin x (mirror rt) (mirror lt))
{-# COMPILE AGDA2HS mirror #-}
