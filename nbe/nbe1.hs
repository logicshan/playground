newtype Name = Name String
  deriving (Show, Eq)

newtype Env val = Env [(Name, val)]
  deriving Show

initEnv :: Env val
initEnv = Env []

instance Functor Env where
  fmap f (Env xs) =
    Env (map (\(x,v) -> (x, f v)) xs)

newtype Message = Message String
  deriving Show

failure :: String -> Either Message a
failure msg = Left (Message msg)

lookupVar :: Env val -> Name -> Either Message val
lookupVar (Env []) (Name x) = failure ("Not found: " ++ x)
lookupVar (Env ((y,v):env')) x
  | y == x    = Right v
  | otherwise = lookupVar (Env env') x

extend :: Env val -> Name -> val -> Env val
extend (Env env) x v = Env ((x,v):env)

data Expr = Var Name
          | Lambda Name Expr
          | App Expr Expr
          deriving Show

data Value = VClosure (Env Value) Name Expr
  deriving Show

eval :: Env Value -> Expr -> Either Message Value
eval env (Var x) = lookupVar env x
eval env (Lambda x body) = Right (VClosure env x body)
eval env (App rator rand) =
  do fun <- eval env rator
     arg <- eval env rand
     doApply fun arg
doApply :: Value -> Value -> Either Message Value
doApply (VClosure env x body) arg = eval (extend env x arg) body

runProgram :: [(Name,Expr)] -> Expr -> Either Message Value
runProgram defs expr =
  do env <- addDefs initEnv defs
     eval env expr
addDefs :: Env Value -> [(Name,Expr)] -> Either Message (Env Value)
addDefs env [] = Right env
addDefs env ((x,e):defs) =
  do v <- eval env e
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

test :: Either Message Value
test =
  runProgram churchDefs
  (App (App (Var (Name "+"))
        (toChurch 2))
    (toChurch 3))

freshen :: [Name] -> Name -> Name
freshen used x
  | elem x used = freshen used (nextName x)
  | otherwise = x
nextName :: Name -> Name
nextName (Name x) = Name (x ++ "'")
