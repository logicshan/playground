{-# OPTIONS --no-positivity-check #-}

module Negative where

module Rick {A : Set} where
  private 
    data U : Set where
      roll : (U → A) → U

  fix : (A → A) → A
  fix f = ω (roll ω)
   where
   ω : U → A
   ω (roll x) = f (x (roll x))

