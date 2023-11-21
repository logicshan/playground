module Unique(nf) where

import Lambda
import qualified Data.Map as M
import Control.Monad.State
import IdInt

nf :: LC IdInt -> LC IdInt
nf e = evalState (nf' e') i
  where (e', (i, _)) = runState (unique e) (firstBoundId, M.empty)

type N a = State IdInt a

nf' :: LC IdInt -> N (LC IdInt)
nf' e@(Var _) = return e
nf' (Lam x e) = liftM (Lam x) (nf' e)
nf' (App f a) = do
  f' <- whnf f
  case f' of
    Lam x b -> subst x a b >>= nf'
    _ -> liftM2 App (nf' f') (nf' a)

whnf :: LC IdInt -> N (LC IdInt)
whnf e@(Var _) = return e
whnf e@(Lam _ _) = return e
whnf (App f a) = do
  f' <- whnf f
  case f' of
    Lam x b -> subst x a b >>= whnf
    _ -> return $ App f' a

subst :: IdInt -> LC IdInt -> LC IdInt -> N (LC IdInt)
subst x s b = sub b
  where sub e@(Var v) | v == x = clone M.empty s
                      | otherwise = return e
        sub (Lam v e) = liftM (Lam v) (sub e)
        sub (App f a) = liftM2 App (sub f) (sub a)

        clone m e@(Var v) = return $ maybe e Var (M.lookup v m)
        clone m (Lam v e) = do v' <- newVar; liftM (Lam v') (clone (M.insert v v' m) e)
        clone m (App f a) = liftM2 App (clone m f) (clone m a)

newVar :: N IdInt
newVar = do
  i <- get
  put (succ i)
  return i

type U a = State (IdInt, M.Map IdInt IdInt) a

unique :: LC IdInt -> U (LC IdInt)
unique (Var v) = liftM Var (getVar v)
unique (Lam v e) = liftM2 Lam (addVar v) (unique e)
unique (App f a) = liftM2 App (unique f) (unique a)

addVar :: IdInt -> U IdInt
addVar v = do
  (i, m) <- get
  put (succ i, M.insert v i m)
  return i

getVar :: IdInt -> U IdInt
getVar v = do
  (_, m) <- get
  return $ maybe v id (M.lookup v m)
