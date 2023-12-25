module Test where

import Data.List(union, (\\))
import Control.Monad.Except

import LexSimplyTyped
import ParSimplyTyped
import AbsSimplyTyped

import ErrM

type Sym = String

data Expr
    = Var Sym
    | App Expr Expr
    | Lam Sym Type Expr
    deriving (Eq, Read, Show)

exp_to_expr :: Exp -> Expr
exp_to_expr (Var0 (Ident s)) = Var s
exp_to_expr (Lam0 (Ident s) t e) = Lam s t (exp_to_expr e)
exp_to_expr (App0 e1 e2) = App (exp_to_expr e1) (exp_to_expr e2)

newtype Env = Env [(Sym, Type)] deriving (Show)

initalEnv :: Env
initalEnv = Env []

extend :: Sym -> Type -> Env -> Env
extend s t (Env r) = Env ((s, t) : r)

type ErrorMsg = String

type TC a = Either ErrorMsg a

findVar :: Env -> Sym -> TC Type
findVar (Env r) s =
    case lookup s r of
    Just t -> return t
    Nothing -> throwError $ "Cannot find variable " ++ s

tCheck :: Env -> Expr -> TC Type
tCheck r (Var s) =
    findVar r s
tCheck r (App f a) = do
    tf <- tCheck r f
    case tf of
     Arrow at rt -> do
        ta <- tCheck r a
        when (ta /= at) $ throwError "Bad function argument type"
        return rt
     _ -> throwError "Non-function in application"
tCheck r (Lam s t e) = do
    let r' = extend s t r
    te <- tCheck r' e
    return $ Arrow t te

typeCheck :: Expr -> Type
typeCheck e =
    case tCheck initalEnv e of
    Left msg -> error ("Type error:\n" ++ msg)
    Right t -> t
