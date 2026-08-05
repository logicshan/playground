
module Syntax where

-- Simple type contexts
data Ctx (T : Set) : Set where
  [] : Ctx T
  _∷_ : (Γ : Ctx T) -> (t : T) -> Ctx T
infixl 10 _∷_

-- Simple types with unit, function and sum
data Ty : Set where
  un : Ty
  _⇒_ _+_ : (s t : Ty) -> Ty

Cx = Ctx Ty

_++_ : ∀{T} -> Ctx T -> Ctx T -> Ctx T
Γ ++ [] = Γ
Γ ++ (Δ ∷ t) = (Γ ++ Δ) ∷ t
infixl 8 _++_

variable
  Γ Δ Θ : Cx
  s t u : Ty

-- Well typed and scoped variables
data Vr : Cx -> Ty -> Set where
  to : Vr (Γ ∷ t) t
  po : Vr Γ t -> Vr (Γ ∷ s) t

-- Well typed and scoped terms
data Tm : Cx -> Ty -> Set where
  vr : Vr Γ t -> Tm Γ t

  tt : Tm Γ un

  la : Tm (Γ ∷ s) t -> Tm Γ (s ⇒ t)
  ap : Tm Γ (s ⇒ t) -> Tm Γ s -> Tm Γ t

  il : Tm Γ s -> Tm Γ (s + t)
  ir : Tm Γ t -> Tm Γ (s + t)
  ca : Tm Γ (s + t) -> Tm (Γ ∷ s) u -> Tm (Γ ∷ t) u -> Tm Γ u
