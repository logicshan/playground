{-# OPTIONS --universe-polymorphism #-}
open import Setoids
module SetoidEqReasoning {a b} (S : Setoid a b) where

infixl 3 _∼_by_
infixl 3 _∼_yb_
infix 4 ∵_

open Setoid S
∵_ : (x : object) → x ∼ x
∵_ x = refl∼

_∼_by_ : ∀ {x y : object} → x ∼ y → (z : object) → y ∼ z → x ∼ z
_∼_by_ x∼y _ y∼z = trans∼ y∼z x∼y
_∼_yb_ : ∀ {x y : object} → x ∼ y → (z : object) → z ∼ y → x ∼ z
_∼_yb_ x∼y _ z∼y = trans∼ (sym∼ z∼y) x∼y
