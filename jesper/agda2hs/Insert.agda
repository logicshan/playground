{-# OPTIONS --erased-matches #-}

open import Haskell.Prelude

insert : {{Ord a}} → a → List a → List a
insert x [] = x ∷ []
insert x (y ∷ ys) =
  if x < y
  then x ∷ y ∷ ys
  else y ∷ insert x ys

{-# COMPILE AGDA2HS insert #-}

data _∈_ (x : a) : List a → Set where
  here  : ∀ {ys}            → x ∈ (x ∷ ys)
  there : ∀ {y ys} → x ∈ ys → x ∈ (y ∷ ys)

insert-elem : ∀ {{_ : Ord a}} (x : a) (xs : List a)
            → x ∈ insert x xs
insert-elem x [] = here
insert-elem x (y ∷ ys) with x < y
... | True  = here
... | False = there (insert-elem x ys)
