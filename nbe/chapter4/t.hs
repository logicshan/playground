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

two = fromRight $ pExpr . myLexer $ "(add1 (add1 zero)) ∈ Nat"
three = fromRight $ pExpr . myLexer $ "add1 (add1 (add1 zero)) ∈ Nat"
plus = fromRight $ pExpr . myLexer $ "λn.λk.rec[Nat] n k (λpred . λ almostSum . add1 almostSum) ∈ Nat -> Nat -> Nat"
plus3 = fromRight $ pExpr . myLexer $ "plus three"
plus3_2 = fromRight $ pExpr . myLexer $ "plus three two"


test' :: Either Message (Ty, Ty)
test' =
  do ctx ← addDefs initCtx
           [(Name "two",two)
           ,(Name "three",three)
           ,(Name "plus",plus)]
     t1 ← synth ctx $ fromRight $ pExpr . myLexer $ "plus three"
     t2 ← synth ctx $ fromRight $ pExpr . myLexer $ "plus three two"
     Right (t1, t2)