{-# OPTIONS --cubical --safe --postfix-projections #-}

module Comp where

open import Cubical.Core.Everything

open import Cubical.HITs.S1

ps1 : base ≡ base
ps1 i = bl
  where
  -- these do not reduce
  bb = hcomp (λ _ → λ{ (i = i0) → base ; (i = i1) → base }) base
  bl = hcomp (λ _ → λ{ (i = i0) → base ; (i = i1) → base }) (loop i)

  -- leave the j = 1 end unspecified, so that at that end it becomes
  -- the unreduced hcomp over i.
  pb : base ≡ bb
  pb j = hcomp (λ _ → λ where
              (i = i0) → base
              (i = i1) → base
              (j = i0) → base) base

  pl : loop i ≡ bl
  pl j = hcomp (λ _ → λ where
              (i = i0) → base
              (i = i1) → base
              (j = i0) → loop i) (loop i)

