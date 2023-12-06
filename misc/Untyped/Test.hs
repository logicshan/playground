module Test where

import Data.List(union, (\\))

import LexUntyped
import ParUntyped
import AbsUntyped

import ErrM

type Sym = String

data Expr
  = Var Sym
  | App Expr Expr
  | Lam Sym Expr
  deriving (Eq, Read, Show)

exp_to_expr :: Exp -> Expr
exp_to_expr (Var0 (Ident s)) = Var s
exp_to_expr (Lam0 (Ident s) e) = Lam s (exp_to_expr e)
exp_to_expr (App0 e1 e2) = App (exp_to_expr e1) (exp_to_expr e2)

parse :: String -> Expr
parse s =
  let Ok e = pExp (myLexer s)
  in exp_to_expr e

whnf :: Expr -> Expr
whnf ee = spine ee []
  where spine (App f a) as = spine f (a:as)
        spine (Lam s e) (a:as) = spine (subst s a e) as
        spine f as = foldl App f as

freeVars :: Expr -> [Sym]
freeVars (Var s) = [s]
freeVars (App f a) = freeVars f `union` freeVars a
freeVars (Lam i e) = freeVars e \\ [i]

subst :: Sym -> Expr -> Expr -> Expr
subst v x b = sub b
  where sub e@(Var i) = if i == v then x else e
        sub (App f a) = App (sub f) (sub a)
        sub (Lam i e) =
            if v == i then
                Lam i e
            else if i `elem` fvx then
                let i' = cloneSym e i
                    e' = substVar i i' e
                in  Lam i' (sub e')
            else
                Lam i (sub e)
        fvx = freeVars x
        cloneSym e i = loop i
           where loop i' = if i' `elem` vars then loop (i ++ "'") else i'
                 vars = fvx ++ freeVars e

substVar :: Sym -> Sym -> Expr -> Expr
substVar s s' e = subst s (Var s') e

alphaEq :: Expr -> Expr -> Bool
alphaEq (Var v)   (Var v')= v == v'
alphaEq (App f a) (App f' a') = alphaEq f f' && alphaEq a a'
alphaEq (Lam s e) (Lam s' e') = alphaEq e (substVar s' s e')
alphaEq _ _ = False

nf :: Expr -> Expr
nf ee = spine ee []
  where spine (App f a) as = spine f (a:as)
        spine (Lam s e) [] = Lam s (nf e)
        spine (Lam s e) (a:as) = spine (subst s a e) as
        spine f as = app f as
        app f as = foldl App f (map nf as)

betaEq :: Expr -> Expr -> Bool
betaEq e1 e2 = alphaEq (nf e1) (nf e2)

zero = parse("λs.λz.z")
one  = parse("λs.λz.s z")
two = parse("λs.λz.s (s z)")
three = parse("λs.λz.s (s (s z))")
plus = parse("λm.λn.λs.λz.m s (n s z)")

app2 f x y = App (App f x) y

-- betaEq (app2 plus one two) three = True
