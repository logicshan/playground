{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}

module CoreCTT where

import Data.Maybe (fromJust)

import Ident
import Interval

{- Syntax (terms/values) -}

data Term
  = Var Ident
  | Universe
  {- Let-definition `[x:ty = e]t` -}
  | TDef (Ident,Term,Term) Term
  {- Π types -}
  | Abst Ident Term Term
  | App Term Term
  {- Σ types -}
  | Sigma Ident Term Term
  | Pair Term Term
  | Fst Term
  | Snd Term
  {- Coproducts -}
  | Sum Term Term
  | InL Term
  | InR Term
  --      fam  f₀   f₁   x
  | Split Term Term Term Term
  {- Naturals -}
  | Nat
  | Zero
  | Succ Term
  --    fam  c₀   cₛ    n
  | Ind Term Term Term Term
  {- Cubical -}
  | I | I0 | I1
  | Sys System
  | Partial DisjFormula Term
  | Restr System Term
  --     fam  φ           i₀   u    base i
  | Comp Term DisjFormula Term Term Term Term
  {- For values only: -}
  | Closure Term Ctx
  --        val   type
  | Neutral Value Value
  -- Just for composition (wrap a value inside a term)
  | TermV Value
  deriving (Eq,Ord)

type Value = Term

newtype Program = Program [Toplevel]

data Toplevel = Definition Ident Term Term
              | Declaration Ident Term
              | Example Term
  deriving (Eq,Ord)

newVar :: [Ident] -> Ident -> Ident
newVar used x
  | x `elem` used = newVar used (Ident $ show x ++ "'")
  | otherwise     = x

-- For printing purposes: e.g. collectApps ((App (App f x_1) x_2) x_3) []
-- returns (f,[x_1,x_2,x_3])
collectApps :: Term -> [Term] -> (Term,[Term])
collectApps t apps = case t of
  App t1 t2' -> collectApps t1 (t2' : apps)
  otherwise -> (t,apps)

-- Generic class for objects (terms,values,top-levels,formulas,etc.)
-- which contain variables
class SyntacticObject a where
  containsVar :: Ident -> a -> Bool
  containsVar s x = s `elem` freeVars x
  vars :: a -> [Ident]
  freeVars :: a -> [Ident]

instance SyntacticObject Ident where
  vars s = [s]
  freeVars s = [s]

instance SyntacticObject System where
  vars sys = concatMap vars (keys sys) ++ concatMap vars (elems sys)
  freeVars = vars

-- For terms only and not for values (which means we don't
-- define `vars` and `freeVars` for closures and neutral values)
instance SyntacticObject Term where
  vars = \case
    Var s -> [s]
    Universe -> []
    TDef (s,t,e) t' -> s : vars t ++ vars e ++ vars t'
    Abst s t e -> s : vars t ++ vars e
    App fun arg -> vars fun ++ vars arg
    Sigma s t e -> s : vars t ++ vars e
    Pair t1 t2 -> vars t1 ++ vars t2
    Fst t -> vars t
    Snd t -> vars t
    Sum ty1 ty2 -> vars ty1 ++ vars ty2
    InL t1 -> vars t1
    InR t2 -> vars t2
    Split ty f1 f2 x -> vars ty ++ vars f1 ++ vars f2 ++ vars x
    Nat -> []
    Zero -> []
    Succ t -> vars t
    Ind ty b s n -> vars ty ++ vars b ++ vars s ++ vars n
    I -> []
    I0 -> []
    I1 -> []
    Sys sys -> vars sys
    Partial phi t -> vars phi ++ vars t
    Restr sys t -> vars sys ++ vars t
    Comp fam phi i0 u b i -> vars fam ++ vars phi ++ vars i0 ++ vars u
      ++ vars b ++ vars i
    TermV v -> [] -- Dummy value (not necessary)





{- Printing functions are in 'Eval.hs' -}

type ErrorString = String

{- Generic association lists utilities -}

extend :: Ctx -> Ident -> CtxEntry -> Ctx
extend ctx s e = if s == Ident "" then ctx else (s,e) : ctx

keys :: [(k,a)] -> [k]
keys = map fst

elems :: [(k,a)] -> [a]
elems = map snd

at :: (Eq k) => [(k,a)] -> k -> a
al `at` s = fromJust $ lookup s al

{- Contexts -}

type Ctx = [(Ident,CtxEntry)]

data CtxEntry = Decl Term -- Type
              | Def Term Term -- Type and definition
              | Val Value -- Value binding for `eval`
  deriving (Eq, Ord)

emptyCtx :: Ctx
emptyCtx = []

{- Systems -}

type System = [(ConjFormula,Term)]

-- Get the disjunction of the (conjunctive) formulas of the system
getSystemFormula :: System -> DisjFormula
getSystemFormula = Disj . map fst
