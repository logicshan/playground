{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Int    using (Int; pos;negsuc)
open import Data.Integer.Base   using (_+_) renaming (_-_ to _∸_)
open import Agda.Builtin.Bool   using (Bool; true; false)
open import Data.Bool.Base      using (_∧_;if_then_else_)
open import Agda.Builtin.String using (String; primStringEquality)

open import Data.Unit.Base using (⊤)
open import Agda.Builtin.Nat hiding (_==_)
open import Agda.Builtin.FromNeg
open import Agda.Builtin.FromNat

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

--open import Data.Product using (Σ; _,_; Σ-syntax)
open import Data.Product using (Σ-syntax)

instance
  NumberNat : Number Nat
  NumberNat = record
    { Constraint = λ _ → ⊤
    ; fromNat    = λ n → n
    }

  NumberInt : Number Int
  NumberInt = record
    { Constraint = λ _ → ⊤
    ; fromNat    = λ n → pos n
    }

  NegativeInt : Negative Int
  NegativeInt = record
    { Constraint = λ _ → ⊤  -- No constraints, always valid
    ; fromNeg    = λ n → negsuc (n - 1)  -- Convert natural number to negative integer
    }

_==_ : String → String → Bool
_==_ = primStringEquality

_≤_ : Int → Int → Bool
x ≤ y with y ∸ x
...      | (pos _) = true
...      | _       = false

IF : {tx ty : Set} → (b : Bool) → tx → ty → if b then tx else ty
IF true  x _ = x
IF false _ y = y

Symbol : Set
Symbol = String

data Type : Set where
  TBool  : Type
  TInt   : Type
  TArrow : Type → Type → Type

data Expr : Set where
  EBool : Bool   → Expr
  EInt  : Int    → Expr
  EAdd  : Expr   → Expr → Expr
  EAnd  : Expr   → Expr → Expr
  ELE   : Expr   → Expr → Expr
  EVar  : Symbol → Expr
  ELam  : Symbol → Type → Expr → Expr
  EAp   : Expr   → Expr → Expr

data Truth : Set where
  truth : Truth

data Absurd : Set where

data _⋀_ (a : Set) (b : Set) : Set where
  _&_ : a → b → a ⋀ b


Decode : Type → Set
Decode TBool = Bool
Decode TInt = Int
Decode (TArrow a b) = Decode a → Decode b


lemma : ∀{x' x t t'} → (if x' == x then Decode t else Decode t') ≡ (Decode (if x' == x then t else t'))
lemma {x'} {x} with x' == x
...               | true  = refl
...               | false = refl
{-# REWRITE lemma #-}

TEnv : Set
TEnv = Symbol → Type

emptyT : TEnv
emptyT = λ(s : Symbol) → TInt

extendT : TEnv → Symbol → Type → TEnv
extendT g x t = λ(x' : Symbol) → if (x' == x) then t else (g x')

VEnv : TEnv → Set
VEnv g = (x : Symbol) → Decode (g x)

emptyV : VEnv emptyT
emptyV = λ(x : Symbol) → 0

extendV : (g : TEnv) →
          (r : VEnv g) →
          (x : Symbol) →
          (t : Type) →
          (v : Decode t) →
          (VEnv (extendT g x t))
extendV g r x t v = λ(x' : Symbol) → IF (x' == x) v (r x')

EqType : Type → Type → Set
EqType TBool TBool                   = Truth
EqType TInt TInt                     = Truth
EqType (TArrow s₁ t₁) (TArrow s₂ t₂) = EqType s₁ s₂ ⋀ EqType t₁ t₂
EqType _              _              = Absurd

HasType : TEnv → Expr → Type → Set
HasType g (EBool _)     TBool        = Truth
HasType g (EInt  _)     TInt         = Truth
HasType g (EAdd e₁ e₂)  TInt         = HasType g e₁ TInt  ⋀ HasType g e₂ TInt
HasType g (EAnd e₁ e₂)  TBool        = HasType g e₁ TBool ⋀ HasType g e₂ TBool
HasType g (ELE  e₁ e₂)  TBool        = HasType g e₁ TInt  ⋀ HasType g e₂ TInt
HasType g (EVar x)      t            = EqType (g x) t
HasType g (EAp f a)     t            = Σ[ s ∈ Type ] (HasType g f (TArrow s t) ⋀ HasType g a s)
HasType g (ELam x s' e) (TArrow s t) = HasType (extendT g x s) e t ⋀ EqType s' s
HasType _ _             _            = Absurd



{-
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
-}
