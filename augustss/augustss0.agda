open import Agda.Builtin.Int    using (Int; pos)
open import Data.Integer.Base   using (_+_; _-_)
open import Agda.Builtin.Bool   using (Bool; true; false)
open import Data.Bool.Base      using (_∧_)
open import Agda.Builtin.String using (String)

_≤_ : Int → Int → Bool
x ≤ y with y - x
...      | (pos _) = true
...      | _       = false

data Expr : Set where
  EBool : Bool → Expr
  EInt  : Int  → Expr
  EAdd  : Expr → Expr → Expr
  EAnd  : Expr → Expr → Expr
  ELE   : Expr → Expr → Expr

data Type : Set where
  TBool : Type
  TInt  : Type

data Truth : Set where
  truth : Truth

data Absurd : Set where

data _⋀_ (a : Set) (b : Set) : Set where
  _&_ : a → b → a ⋀ b

HasType : Expr → Type → Set
HasType (EBool    _) TBool = Truth
HasType (EInt     _) TInt  = Truth
HasType (EAdd e₁ e₂) TInt  = HasType e₁ TInt  ⋀ HasType e₂ TInt
HasType (EAnd e₁ e₂) TBool = HasType e₁ TBool ⋀ HasType e₂ TBool
HasType (ELE  e₁ e₂) TBool = HasType e₁ TInt  ⋀ HasType e₂ TInt
HasType _            _     = Absurd

Decode : Type → Set
Decode TBool = Bool
Decode TInt  = Int

interp : (e : Expr) → (t : Type) → HasType e t → Decode t
interp (EBool    b) TBool p         = b
interp (EInt     i) TInt  p         = i
interp (EAdd e₁ e₂) TInt  (p₁ & p₂) = interp e₁ TInt  p₁ + interp e₂ TInt  p₂
interp (EAnd e₁ e₂) TBool (p₁ & p₂) = interp e₁ TBool p₁ ∧ interp e₂ TBool p₂ 
interp (ELE  e₁ e₂) TBool (p₁ & p₂) = interp e₁ TInt  p₁ ≤ interp e₂ TInt  p₂
