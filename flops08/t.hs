{-# LANGUAGE UnicodeSyntax #-}

data Exp = Var Int
         | App Exp Exp
         | Lam Exp
         | Pi Exp Exp
         | U
  deriving (Eq)

type Ty    = Exp
type Subst = [Exp]
type Cxt   = [Ty]

isCo ∷ Cxt → Bool
isCo []      = True
isCo (a:cxt) = isCo cxt && isTy cxt a

isSu ∷ Cxt → Cxt → Subst → Bool
isSu cxt []     []     = True
isSu cxt (b:bs) (t:ts) = isSu cxt bs ts &&
                         isTm cxt (subst b cxt) t

isTy ∷ Cxt → Ty → Bool
isTy cxt (Pi a b) = isTy cxt a && isTy (a:cxt) b
isTy cxt U        = True
isTy cxt a        = isTm cxt U a

isTm ∷ Cxt → Ty → Exp → Bool
isTm cxt (Pi a b) (Lam t)  = isTm (a:cxt) b t
isTm cxt a        (Lam t)  = False
isTm cxt U        (Pi a b) = isTm cxt U a && isTm (a:cxt) U b
isTm cxt c        (Pi a b) = False
isTm cxt a        U        = False
isTm cxt a        s        = case inferTy cxt s of
                               Just a' → a == a'
                               Nothing → False

inferTy ∷ Cxt → Exp → Maybe Ty
inferTy cxt (Var i)   = Just (shift (cxt !! i) (i+1))
inferTy cxt (App s t) = case inferTy cxt s of
  Just (Pi a b) → if isTm cxt a t
                  then Just (subst b (t:ide))
                  else Nothing
  otherwise     → Nothing

shift ∷ Exp → Int → Exp
shift t i = subst t (map Var [i ..])

comp ∷ Subst → Subst → Subst
comp []     ts' = []
comp (t:ts) ts' = (subst t ts'):(comp ts ts')

ide ∷ Subst
ide = map Var [0 ..]

subst ∷ Exp → Subst → Exp
subst (Var i)   ts = ts !! i
subst (App s t) ts = app (subst s ts) (subst t ts)
subst (Lam t)   ts = Lam (subst t (lift ts))
subst (Pi a b)  ts = Pi (subst a ts) (subst b (lift ts))
subst U         ts = U

lift ∷ Subst → Subst
lift ts = q : comp ts p

p ∷ Subst
p = map Var [1 ..]

q ∷ Exp
q = Var 0

app ∷ Exp → Exp → Exp
app (Lam t) s = subst t (s:ide)
app r       s = App r s
