{-# LANGUAGE UnicodeSyntax #-}

newtype Name = Name String
  deriving (Show, Eq)

newtype Env val = Env [(Name, val)]
  deriving Show

initEnv ∷ Env val
initEnv = Env []

instance Functor Env where
  fmap f (Env xs) =
    Env (map (\(x,v) → (x, f v)) xs)

newtype Message = Message String
  deriving Show

failure ∷ String → Either Message a
failure msg = Left (Message msg)

lookupVar ∷ Env val → Name → Either Message val
lookupVar (Env []) (Name x) = failure ("Not found: " ++ x)
lookupVar (Env ((y,v):env')) x
  | y == x    = Right v
  | otherwise = lookupVar (Env env') x

extend ∷ Env val → Name → val → Env val
extend (Env env) x v = Env ((x,v):env)

data Expr = Var Name
          | Lambda Name Expr
          | App Expr Expr
          | Zero
          | Add1 Expr
          | Rec Ty Expr Expr Expr
          | Ann Expr Ty
  deriving Show

data Ty
  = TNat
  | TArr Ty Ty
  deriving (Eq,Show)

type Context = Env Ty

initCtx ∷ Context
initCtx = initEnv

synth ∷ Context → Expr → Either Message Ty
check ∷ Context → Expr → Ty → Either Message ()

synth ctx (Var x) = lookupVar ctx x
synth ctx (App rator rand) =
  do ty ← synth ctx rator
     case ty of
       TArr argT retT →
         do check ctx rand argT
            Right retT
       other → failure ("Not a function type: " ++ show other)
synth ctx (Rec ty tgt base step) =
  do tgtT ← synth ctx tgt
     case tgtT of
       TNat →
         do check ctx base ty
            check ctx step (TArr TNat (TArr ty ty))
            Right ty
       other → failure ("Not the type Nat: " ++ show other)
synth ctx (Ann e t) =
  do check ctx e t
     Right t
synth _ other =
  failure ("Can't find a type for " ++ show other ++ ". " ++
           "Try adding a type annotation.")

check ctx (Lambda x body) t =
  case t of
    TArr arg ret →
      check (extend ctx x arg) body ret
    other → failure ("Lambda requires a function type, but got " ++ show other)
check ctx Zero t =
  case t of
    TNat → Right ()
    other →
      failure ("Zero should be a Nat, but was used where a " ++
               show other ++ " was expected")
check ctx (Add1 n) t =
  case t of
    TNat →
      check ctx n TNat
    other →
      failure ("Add1 should be a Nat, but was used where a " ++
               show other ++ " was expected")
check ctx other t =
  do t' ← synth ctx other
     if t' == t
       then Right ()
       else failure ("Expected " ++ show t ++
                     " but got " ++ show t')

addDefs :: Context → [(Name, Expr)] → Either Message Context
addDefs ctx [ ] = Right ctx
addDefs ctx ((x, e) : defs) =
  do t ← synth ctx e
     addDefs (extend ctx x t) defs

test :: Either Message (Ty, Ty)
test =
  do ctx ← addDefs initCtx
           [(Name "two",
             (Ann (Add1 (Add1 Zero))
              TNat)),
            (Name "three",
             (Ann (Add1 (Add1 (Add1 Zero)))
              TNat)),
            (Name "+",
             (Ann (Lambda (Name "n")
                   (Lambda (Name "k")
                    (Rec TNat (Var (Name "n"))
                     (Var (Name "k"))
                     (Lambda (Name "pred")
                      (Lambda (Name "almostSum")
                       (Add1 (Var (Name "almostSum"))))))))
              (TArr TNat (TArr TNat TNat))))]
     t1 ← synth ctx (App (Var (Name "+")) (Var (Name "three")))
     t2 ← synth ctx (App (App (Var (Name "+")) (Var (Name "three")))
                     (Var (Name "two")))
     Right (t1, t2)

{-
data Expr = Var Name
          | Lambda Name Expr
          | App Expr Expr
          deriving Show

data Value
  = VClosure (Env Value) Name Expr
  | VNeutral Neutral
  deriving (Show)

data Neutral
  = NVar Name
  | NApp Neutral Value
  deriving (Show)

eval ∷ Env Value → Expr → Either Message Value
eval env (Var x) = lookupVar env x
eval env (Lambda x body) = Right (VClosure env x body)
eval env (App rator rand) =
  do fun ← eval env rator
     arg ← eval env rand
     doApply fun arg
doApply ∷ Value → Value → Either Message Value
doApply (VClosure env x body) arg = eval (extend env x arg) body
doApply (VNeutral neu)        arg = Right (VNeutral (NApp neu arg))

freshen ∷ [Name] → Name → Name
freshen used x
  | elem x used = freshen used (nextName x)
  | otherwise = x
nextName ∷ Name → Name
nextName (Name x) = Name (x ++ "'")

readBack ∷ [Name] → Value → Either Message Expr
readBack used (VNeutral (NVar x)) = Right (Var x)
readBack used (VNeutral (NApp fun arg)) =
  do rator ← readBack used (VNeutral fun)
     rand ← readBack used arg
     Right (App rator rand)
readBack used fun@(VClosure _ x _) =
  do let x' = freshen used x
     bodyVal ← doApply fun (VNeutral (NVar x'))
     bodyExpr ← readBack (x' : used) bodyVal
     Right (Lambda x' bodyExpr)

normalize ∷ Expr → Either Message Expr
normalize expr =
  do val ← eval initEnv expr
     readBack [] val

runProgram ∷ [(Name, Expr)] → Expr → Either Message Expr
runProgram defs expr =
  do env ← addDefs initEnv defs
     val ← eval env expr
     readBack (map fst defs) val
addDefs :: Env Value → [(Name, Expr)] → Either Message (Env Value)
addDefs env [] = Right env
addDefs env ((x, e) : defs) =
  do v ← eval env e
     addDefs (extend env x v) defs

churchDefs :: [(Name, Expr)]
churchDefs =
  [ (Name "zero",
     Lambda (Name "f")
      (Lambda (Name "x")
        (Var (Name "x"))))
  , (Name "add1",
      Lambda (Name "n")
      (Lambda (Name "f")
        (Lambda (Name "x")
         (App (Var (Name "f"))
          (App (App (Var (Name "n"))
                (Var (Name "f")))
           (Var (Name "x")))))))
  , (Name "+",
     Lambda (Name "j")
     (Lambda (Name "k")
      (Lambda (Name "f")
       (Lambda (Name "x")
        (App (App (Var (Name "j")) (Var (Name "f")))
         (App (App (Var (Name "k")) (Var (Name "f")))
          (Var (Name "x"))))))))
  ]

toChurch :: Integer -> Expr
toChurch n
  | n <= 0 = Var (Name "zero")
  | otherwise = App (Var (Name "add1")) (toChurch ((-) n 1))

test :: Either Message Expr
test =
  runProgram churchDefs
  (App (App (Var (Name "+"))
        (toChurch 2))
    (toChurch 3))
-}
