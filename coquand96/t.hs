{-# LANGUAGE UnicodeSyntax #-}

import Prelude hiding ( lookup )

-- M := x
--    | λx.M
--    | M N
--    | (x:M)N
--    | let x=M:A in N
--    | Type

-- Ide: an infinite set of identifiers
-- Env D: functions in `Ide -> D`

-- a model is a tuple (D,App,eval,Type,:)
-- D is a set
-- App : D -> [D -> D]
-- eval : Exp -> Env D -> D
-- : ⊆ D × D (⊆ is a binary relation on D; the relation `a : d` means intuitively that the value `a ∈ D` is of type d)
-- ⟦M⟧ := eval M ()

-- ------------------------
--    eval Type ρ = Type

--    eval A ρ = eval C ρ         eval B (ρ,x=d) = eval D (ν,y=d)
-- -----------------------------------------------------------------
--               eval ((x:A)B) ρ = eval ((y:C)D) ν

-- rules for types

-- ---------------------
--      Type : Type

--     eval A ρ : Type     a : eval A ρ      eval B (ρ,x=a) : Type
-- -------------------------------------------------------------------
--                         eval ((x:A)B) ρ

--       c : eval ((x:A)B) ρ     a : eval A ρ
-- -----------------------------------------------
--            App c a : eval B (ρ,x=a)

--       a : eval A ρ     eval N (ν,y=a) : eval B (ρ,x=a)
-- ------------------------------------------------------------
--               eval (λy.N) ν : eval ((x:A)B) ρ

-- values V

-- Let G be an infinite set of new variables, the generic values. We write v₁,v₂,v₃... for
-- elements of G.

-- G ⊆ V
-- if u,w ∈ V, then u w ∈ V
-- Type ∈ V
-- if M is an expression, ρ ∈ Env, FV(M) ⊆ dom(ρ), then Mρ ∈ V
-- () ∈ Env, and dom(()) = ∅
-- if ρ ∈ Env, x ∈ Ide, u ∈ V, then (ρ,x=u) ∈ Env, and dom((ρ,x=u)) = dom(ρ)∪{x}.

-- We define `lookup x ρ` as before. In the following, assume u,v,w ∈ V.
-- Any assignment `f ∈ G → D` extends uniquely to an `f ∈ V → D` such that
-- - f Type = Type
-- - f (u₁u₂) = App (f u₁) (f u₂)
-- - f (Mρ) = eval M (f⃰ρ)
-- where f⃰() = () and f⃰(ρ,x=u) = ((f⃰ρ),x=fu)
--   We can define inductively when a generic value occurs in a given value,
-- and prove that `f u = g u` if f and g agree on all generic values that
-- occur in u.



-- the main data types and general functions

type Id = String

data Exp = Var Id              -- x
         | App Exp Exp         -- M N
         | Abs Id Exp          -- λx.M
         | Let Id Exp Exp Exp  -- let x=M:A in N
         | Pi Id Exp Exp       -- Π(x:M)N
         | Type

data Val = VGen Int
         | VApp Val Val
         | VType
         | VClos Env Exp

type Env = [(Id,Val)]

update :: Env → Id → Val → Env
update env x u = (x,u):env

lookup :: Id → Env → Val
lookup x ((y,u):env) =
  if x==y then u
  else lookup x env
lookup x [] = error $ "lookup " ++ x

-- a short way of writing the whnf algorithm

app  :: Val → Val → Val
eval :: Env → Exp → Val

app (VClos env (Abs x e)) v = eval (update env x v) e
app u                     v = VApp u v

eval env (Var x)         = lookup x env
eval env (App e1 e2)     = app (eval env e1) (eval env e2)
eval env (Let x e1 _ e3) = eval (update env x (eval env e1)) e3
eval env Type            = VType
eval env e               = VClos env e

whnf :: Val → Val
whnf (VApp u w) = app (whnf u) (whnf w)
whnf (VClos env e) = eval env e
whnf v             = v

-- the conversion algorithm; the integer is
-- used to represent the introduction of a fresh variable

eqVal :: (Int,Val,Val) → Bool
eqVal (k,u1,u2) =
  case (whnf u1,whnf u2) of
    (VType,VType) → True
    (VApp t1 w1,VApp t2 w2) →
      eqVal (k,t1,t2) && eqVal (k,w1,w2)
    (VGen k1,VGen k2) → k1==k2
    (VClos env1 (Abs x1 e1),VClos env2 (Abs x2 e2)) →
      let v = VGen k
      in eqVal (k+1,
                VClos (update env1 x1 v) e1,
                VClos (update env2 x2 v) e2)
    (VClos env1 (Pi x1 a1 b1),VClos env2 (Pi x2 a2 b2)) →
      let v = VGen k
      in eqVal (k,VClos env1 a1,VClos env2 a2) &&
         eqVal (k+1,
                VClos (update env1 x1 v) b1,
                VClos (update env2 x2 v) b2)
    _ → False

-- type-checking and type inference

checkExp  :: (Int,Env,Env) → Exp → Val → Bool
inferExp  :: (Int,Env,Env) → Exp → Val
checkType :: (Int,Env,Env) → Exp → Bool

checkType (k,rho,gamma) e = checkExp (k,rho,gamma) e VType

checkExp (k,rho,gamma) (Abs x n) v =
  case whnf v of
    VClos env (Pi y a b) →
      let v = VGen k
      in checkExp (k+1,
                   update rho x v,
                   update gamma x (VClos env a))
                  n (VClos (update env y v) b)
    _ → error "expected Pi"
checkExp (k,rho,gamma) (Pi x a b) v =
  case whnf v of
    VType → checkType (k,rho,gamma) a &&
             checkType (k+1,
                        update rho x (VGen k),
                        update gamma x (VClos rho a))
                       b
    _ → error "expected Type"
checkExp (k,rho,gamma) (Let x e1 e2 e3) v =
  checkType (k,rho,gamma) e2 &&
  checkExp (k,
            update rho x (eval rho e1),
            update gamma x (eval rho e2))
           e3 v
checkExp (k,rho,gamma) e v = eqVal (k,inferExp (k,rho,gamma) e,v)

inferExp (k,rho,gamma) (Var id) = lookup id gamma
inferExp (k,rho,gamma) (App e1 e2) =
  case whnf (inferExp (k,rho,gamma) e1) of
    VClos env (Pi x a b) →
      if checkExp (k,rho,gamma) e2 (VClos env a)
      then VClos (update env x (VClos rho e2)) b
      else error "application error"
    _ → error "application, expected Pi"
inferExp (k,rho,gamma) Type = VType
inferExp _ _ = error "cannot infer type"

typecheck :: Exp → Exp → Bool

typecheck m a =
  checkType (0,[],[]) a &&
  checkExp (0,[],[]) m (VClos [] a)

test :: Bool
test =
  typecheck (Abs "A" (Abs "x" (Var "x")))
            (Pi "A" Type (Pi "x" (Var "A") (Var "A")))
