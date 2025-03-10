{-# OPTIONS --erasure #-}

open import Haskell.Prelude

headMaybe : List a → Maybe a
headMaybe [] = Nothing
headMaybe (x ∷ xs) = Just x
{-# COMPILE AGDA2HS headMaybe #-}

tailMaybe : List a → Maybe (List a)
tailMaybe [] = Nothing
tailMaybe (x ∷ xs) = Just xs
{-# COMPILE AGDA2HS tailMaybe #-}

third : List a → Maybe a
third xs = do
  ys ← tailMaybe xs
  zs ← tailMaybe ys
  z  ← headMaybe zs
  return z
{-# COMPILE AGDA2HS third #-}
