data Bool : Set where
  True  : Bool
  False : Bool

{-# BUILTIN BOOL  Bool  #-}
{-# BUILTIN TRUE  True  #-}
{-# BUILTIN FALSE False #-}

data Expr : Set where
  EBool : Bool -> Expr
  EInt  : Int  -> Expr
  EAdd  : Expr -> Expr -> Expr
  EAnd  : Expr -> Expr -> Expr
  ELE   : Expr -> Expr -> Expr

data Ty : Set where
  TBool : Ty
  TInt  : Ty

data Truth : Set where
  truth : Truth

data Absurd : Set where

--data (/\) a b = (&&) a b
