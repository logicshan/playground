type Ix  = Int
type Lvl = Int

data Tm      = Var Ix
             | Lam Tm
             | App Tm Tm
  deriving (Show)
data Closure = Close [Val] Tm
  deriving (Show)
data Val     = VVar Lvl
             | VApp Val Val
             | VLam Closure
  deriving (Show)
eval :: [Val] -> Tm -> Val
eval env t = case t of
  Var x   -> env !! x
  App t u -> case (eval env t, eval env u) of
               (VLam (Close env' t), u) -> eval (u:env') t
               (t                  , u) -> VApp t u
  Lam t   -> VLam (Close env t)

quote :: Lvl -> Val -> Tm
quote l t = case t of
  VVar x             -> Var (l - x - 1)
  VApp t u           -> App (quote l t) (quote l u)
  VLam (Close env t) -> Lam (quote (l + 1) (eval (VVar l:env) t))

nf :: [Val] -> Tm -> Tm
nf env t = quote (length env) (eval env t)

term1 :: Tm
term1_val :: Val

term1 = Lam (App (Lam (App (Var 1) (Var 0))) (Var 0))
term1_val = eval [] term1
