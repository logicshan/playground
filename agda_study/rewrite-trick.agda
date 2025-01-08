{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Equality

{-# BUILTIN REWRITE _≡_ #-}

module _ {a} (A : Set a) (x y : A) (eq : x ≡ y) where

  abstract
    x' : A
    x' = x
    y' : A
    y' = y
    eq' : x' ≡ y'
    eq' = eq

  {-# REWRITE eq' #-}

  lemma : x' ≡ y'
  lemma = refl
