{-# OPTIONS --erasure #-}

open import Haskell.Prelude
{-
transport : {a : Set} {@0 m n : a}
          → @0 m ≡ n → a → a
transport refl t = t
{-# COMPILE AGDA2HS transport #-}
-}

transport : (p : @0 a → Set) {@0 m n : a}
          → @0 m ≡ n → p m → p n
transport p refl t = t
{-# COMPILE AGDA2HS transport #-}
