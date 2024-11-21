{-# LANGUAGE UnicodeSyntax #-}

import AbsLam
import ParLam   ( pExpr, myLexer )
import PrintLam ( Print, printTree )
import Data.Either.Utils ( fromRight )

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

freshen ∷ [Name] → Name → Name
freshen used x
  | elem x used = freshen used (nextName x)
  | otherwise = x
nextName ∷ Name → Name
nextName (Name x) = Name (x ++ "'")

type Context = Env Ty

initCtx ∷ Context
initCtx = initEnv

data Value
  = VZero
  | VAdd1 Value
  | VClosure (Env Value) Name Expr
  | VNeutral Ty Neutral
  deriving (Show)
data Neutral
  = NVar Name
  | NApp Neutral Normal
  | NRec Ty Neutral Normal Normal
  deriving (Show)
data Normal
  = Normal {normalType  ∷ Ty
           ,normalValue ∷ Value}
    deriving (Show)

eval ∷ Env Value → Expr → Value
eval env (Var x) =
  case lookupVar env x of
    Left msg →
      error ("Internal error: " ++ show msg)
    Right v → v
eval env (Lambda x body) =
  VClosure env x body
eval env (App rator rand) =
  doApply (eval env rator) (eval env rand)
eval env Zero = VZero
eval env (Add1 n) = VAdd1 (eval env n)
eval env (Rec t tgt base step) =
  doRec t (eval env tgt) (eval env base) (eval env step)
eval env (Ann e t) = eval env e

doApply :: Value → Value → Value
doApply (VClosure env x body) arg =
  eval (extend env x arg) body
doApply (VNeutral (TArr t₁ t₂) neu) arg =
  VNeutral t₂ (NApp neu (Normal t₁ arg))
doRec ∷ Ty → Value → Value → Value → Value
doRec t VZero base step = base
doRec t (VAdd1 n) base step =
  doApply (doApply step n)
          (doRec t n base step)
doRec t (VNeutral TNat neu) base step =
  VNeutral t
    (NRec t neu
      (Normal t base)
      (Normal (TArr TNat (TArr t t)) step))

readBackNormal ∷ [Name] → Normal → Expr
readBackNormal used (Normal t v) = readBack used t v
readBack ∷ [Name] → Ty → Value → Expr
readBack used TNat VZero = Zero
readBack used TNat (VAdd1 pred) = Add1 (readBack used TNat pred)
readBack used (TArr t1 t2) fun =
  let x = freshen used (argName fun)
      xVal = VNeutral t1 (NVar x)
  in Lambda x
     (readBack used t2
      (doApply fun xVal))
  where
    argName (VClosure _ x _) = x
    argName _             = Name "x"
readBack used t1 (VNeutral t2 neu) =
  -- Note: checking t1 and t2 for equality here is a good way to find bugs,
  -- but is not strictly necessary.
  if t1 == t2
  then readBackNeutral used neu
  else error "Internal error: mismatched types at readBackNeutral"
readBackNeutral ∷ [Name] → Neutral → Expr
readBackNeutral used (NVar x) = Var x
readBackNeutral used (NApp rator arg) =
  App (readBackNeutral used rator) (readBackNormal used arg)
readBackNeutral used (NRec t neu base step) =
  Rec t (readBackNeutral used neu)
    (readBackNormal used base)
    (readBackNormal used step)

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


type Defs = Env Normal
noDefs ∷ Defs
noDefs = initEnv
defsToContext ∷ Defs → Context
defsToContext defs = fmap normalType defs
defsToEnv ∷ Defs → Env Value
defsToEnv defs = fmap normalValue defs
normWithDefs ∷ Defs → Expr → Either Message Normal
normWithDefs defs e =
  do t ← synth (defsToContext defs) e
     let v = eval (defsToEnv defs) e
     Right (Normal t v)
addDefs ∷ Defs → [(Name, Expr)] → Either Message Defs
addDefs defs [] =
  Right defs
addDefs defs ((x, e) : more) =
  do norm ← normWithDefs defs e
     addDefs (extend defs x norm) more
definedNames ∷ Defs → [Name]
definedNames (Env defs) = map fst defs

normWithTestDefs ∷ Expr → Either Message Expr
normWithTestDefs e =
  do defs ← addDefs noDefs
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
     norm ← normWithDefs defs e
     Right (readBackNormal (definedNames defs) norm)

test1, test2, test3 ∷ Either Message Expr
test1 = normWithTestDefs (Var (Name "+"))
test2 = normWithTestDefs (App (Var (Name "+"))
                              (Var (Name "three")))
test3 = normWithTestDefs (App (App (Var (Name "+"))
                                   (Var (Name "three")))
                              (Var (Name "two")))

two = fromRight $ pExpr . myLexer $ "(add1 (add1 zero)) ∈ Nat"
three = fromRight $ pExpr . myLexer $ "add1 (add1 (add1 zero)) ∈ Nat"
plus = fromRight $ pExpr . myLexer $ "λn.λk.rec[Nat] n k (λpred . λ almostSum . add1 almostSum) ∈ Nat -> Nat -> Nat"

plus3 = fromRight $ pExpr . myLexer $ "+ three"
plus3_2 = fromRight $ pExpr . myLexer $ "+ three two"

normWithTestDefs' ∷ Expr → Either Message Expr
normWithTestDefs' e =
  do defs ← addDefs noDefs
            [(Name "two",two),
             (Name "three",three),
             (Name "+",plus)]
     norm ← normWithDefs defs e
     Right (readBackNormal (definedNames defs) norm)

test1', test2', test3' ∷ Either Message Expr
test1' = normWithTestDefs' $ fromRight $ pExpr . myLexer $ "+"
test2' = normWithTestDefs' plus3
test3' = normWithTestDefs' plus3_2

-- printTree $ fromRight test1'
