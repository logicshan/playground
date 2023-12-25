module LambdaCube where

import Data.List(union, (\\))
import Control.Monad.Except

import LexCube
import ParCube
import AbsCube

import ErrM

type Sym = String

data Expr
    = Var Sym
    | App Expr Expr
    | Lam Sym Type Expr
    | Pi  Sym Type Type
    | Kind Kinds
    deriving (Eq, Read, Show)
type Type = Expr

exp_to_expr :: Exp -> Expr
exp_to_expr (Var0 (Ident s)) = Var s
exp_to_expr (Lam0 (Ident s) t e) = Lam s (exp_to_expr t) (exp_to_expr e)
exp_to_expr (Pi0 (Ident s) t1 t2) = Pi s (exp_to_expr t1) (exp_to_expr t2)
exp_to_expr (App0 e1 e2) = App (exp_to_expr e1) (exp_to_expr e2)
exp_to_expr (Kind0 k) = Kind k

parse :: String -> Expr
parse s =
  let Ok e = pExp (myLexer s)
  in exp_to_expr e


freeVars :: Expr -> [Sym]
freeVars (Var s) = [s]
freeVars (App f a) = freeVars f `union` freeVars a
freeVars (Lam i t e) = freeVars t `union` (freeVars e \\ [i])
freeVars (Pi i k t) = freeVars k `union` (freeVars t \\ [i])
freeVars (Kind _) = []

subst :: Sym -> Expr -> Expr -> Expr
subst v x = sub
  where sub e@(Var i) = if i == v then x else e
        sub (App f a) = App (sub f) (sub a)
        sub (Lam i t e) = abstr Lam i t e
        sub (Pi i t e) = abstr Pi i t e
        sub (Kind k) = Kind k
        fvx = freeVars x
        cloneSym e i = loop i
           where loop i' = if i' `elem` vars then loop (i ++ "'") else i'
                 vars = fvx ++ freeVars e
        abstr con i t e =
            if v == i then
                con i (sub t) e
            else if i `elem` fvx then
                let i' = cloneSym e i
                    e' = substVar i i' e
                in  con i' (sub t) (sub e')
            else
                con i (sub t) (sub e)

substVar :: Sym -> Sym -> Expr -> Expr
substVar s s' e = subst s (Var s') e

whnf :: Expr -> Expr
whnf ee = spine ee []
    where spine (App f a) as = spine f (a:as)
          spine (Lam s _ e) (a:as) = spine (subst s a e) as
          spine f as = foldl App f as


nf :: Expr -> Expr
nf ee = spine ee []
  where spine (App f a) as = spine f (a:as)
        spine (Lam s t e) [] = Lam s (nf t) (nf e)
        spine (Lam s _ e) (a:as) = spine (subst s a e) as
        spine (Pi s k t) as = app (Pi s (nf k) (nf t)) as
        spine f as = app f as
        app f as = foldl App f (map nf as)


alphaEq :: Expr -> Expr -> Bool
alphaEq (Var v) (Var v')           = v == v'
alphaEq (App f a) (App f' a')      = alphaEq f f' && alphaEq a a'
alphaEq (Lam s t e) (Lam s' t' e') = alphaEq t t' && alphaEq e (substVar s' s e')
alphaEq (Pi s k t)  (Pi s' k' t')  = alphaEq k k' && alphaEq t (substVar s' s t')
alphaEq (Kind k) (Kind k')         = k == k'
alphaEq _        _                 = False

betaEq :: Expr -> Expr -> Bool
betaEq e1 e2 = alphaEq (nf e1) (nf e2)

type ErrorMsg = String
type TC a = Either ErrorMsg a

data Env = Env [(Sym, Type)] deriving (Show)

initalEnv :: Env
initalEnv = Env []

extend :: Sym -> Type -> Env -> Env
extend s t (Env r) = Env ((s, t) : r)

findVar :: Env -> Sym -> TC Type
findVar (Env r) s =
    case lookup s r of
    Just t -> return t
    Nothing -> throwError ("Cannot find variable " ++ s)

tCheckRed r e = liftM whnf (tCheck r e)

tCheck :: Env -> Expr -> TC Type
tCheck r (Var s) = findVar r s
tCheck r (App f a) = do
    tf <- tCheckRed r f
    case tf of
     Pi x at rt -> do
        ta <- tCheck r a
        when (not (betaEq ta at)) $ throwError $ "Bad function argument type"
        return $ subst x a rt
     _ -> throwError $ "Non-function in application"
tCheck r (Lam s t e) = do
    tCheck r t
    let r' = extend s t r
    te <- tCheck r' e
    let lt = Pi s t te
    tCheck r lt
    return lt
tCheck r (Pi x a b) = do
    s <- tCheckRed r a
    let r' = extend x a r
    t <- tCheckRed r' b
    when ((s, t) `notElem` allowedKinds) $ throwError "Bad abstraction"
    return t
tCheck _ (Kind Star) = return $ Kind Box
tCheck _ (Kind Box) = throwError "Found a Box"

allowedKinds :: [(Type, Type)]
allowedKinds = [(Kind Star, Kind Star), (Kind Star, Kind Box), (Kind Box, Kind Star), (Kind Box, Kind Box)]


typeCheck :: Expr -> Type
typeCheck e =
    case tCheck initalEnv e of
    Left msg -> error ("Type error:\n" ++ msg)
    Right t -> nf t


e1 = parse("λA:★.λx:A.x")
e2 = parse("λB:★.λy:B.y")

e3 = parse("λA:★.λf:A→A.λx:A.f x")
t3 = typeCheck e3

bool = parse("Πa:★.a→a→a")

false = parse("λa:★.λx:a.λy:a.x")

true = parse("λa:★.λx:a.λy:a.y")

ifT = parse("Πa:★.(Πa:★.a→a→a)→a→a→a")
if' = parse("λa:★.λb:(Πa:★.a→a→a).λt:a.λf:a.b a t f")

-- betaEq bool (typeCheck false) -> True
-- betaEq ifT (typeCheck if') -> True
