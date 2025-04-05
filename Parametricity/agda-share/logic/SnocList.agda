
module SnocList where

open import Data.Nat

import Relation.Binary

infixl 30 _::_
data List (a : Set) : Set where
  []   : List a
  _::_ : List a → a → List a

infixl 25 _++_
_++_ : ∀{a} → List a → List a → List a
l ++ []      = l
l ++ xs :: x = (l ++ xs) :: x

length : ∀{a} → List a → ℕ
length []        = 0
length (xs :: _) = suc (length xs)

infix 20 _∈_
data _∈_ {a : Set} : a → List a → Set where
  now    : {e   : a} {l : List a} → e ∈ l :: e
  before : {e x : a} {l : List a} → e ∈ l → e ∈ l :: x

∈-++₁ : ∀{a} {xs ys : List a} {e : a} → e ∈ xs → e ∈ ys ++ xs
∈-++₁ now = now
∈-++₁ (before e∈xs) = before (∈-++₁ e∈xs)

∈-++₂ : ∀{a} {xs ys : List a} {e : a} → e ∈ ys → e ∈ ys ++ xs
∈-++₂ {xs = []}      e∈ys = e∈ys
∈-++₂ {xs = xt :: x} e∈ys = before (∈-++₂ {xs = xt} e∈ys)

wf-induct : {a : Set} {P : List a → Set}
          → (∀ l → (∀ l' → length l' < length l → P l') → P l)
          → (l : List a) → P l
wf-induct {a} {P} p l = p l (wf-aux l)
 where
 wf-aux : ∀ (l l' : List a) → length l' < length l → P l'
 wf-aux []        l'        ()
 wf-aux (xs :: x) []        ll'<ll    = p [] (λ _ ())
 wf-aux (xs :: x) (ys :: y) (s≤s m≤n) = p (ys :: y)
                                          (λ l' m'<m → wf-aux xs l' (trans m'<m m≤n))
  where open Relation.Binary
        open DecTotalOrder decTotalOrder