module HOAS(nf) where

import qualified Data.Map as M
import Lambda
import IdInt

data HOAS = HVar IdInt | HLam (HOAS -> HOAS) | HApp HOAS HOAS

nf :: LC IdInt -> LC IdInt
nf = toLC . nfh . fromLC

nfh :: HOAS -> HOAS
nfh e@(HVar _) = e
nfh (HLam b) = HLam (nfh . b)
nfh (HApp f a) =
  case whnf f of
    HLam b -> nfh (b a)
    f' -> HApp (nfh f') (nfh a)

whnf :: HOAS -> HOAS
whnf e@(HVar _) = e
whnf e@(HLam _) = e
whnf (HApp f a) =
  case whnf f of
    HLam b -> whnf (b a)
    f' -> HApp f' a

fromLC :: LC IdInt -> HOAS
fromLC = from M.empty
  where from m (Var v) = maybe (HVar v) id (M.lookup v m)
        from m (Lam v e) = HLam $ \ x -> from (M.insert v x m) e
        from m (App f a) = HApp (from m f) (from m a)

toLC :: HOAS -> LC IdInt
toLC = to firstBoundId
  where to _ (HVar v) = Var v
        to n (HLam b) = Lam n (to (succ n) (b (HVar n)))
        to n (HApp f a) = App (to n f) (to n a)
