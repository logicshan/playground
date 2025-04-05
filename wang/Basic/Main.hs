-- A Haskell Implementation for a Dependent Type Theory with Definitions
-- Chapter 2

data Id = Id String
  deriving (Show, Eq)

type Name = Id

data A =
     EU
  |  EK K
  |  EPi Name A M   -- [x:A]M
  |  EDef D M       -- [x:A=B]M
  deriving Show
type M = A

data K =
     KVar Name      -- x
  |  KApp K M       -- KM
  deriving Show

data D =
     DDef Name A M  -- x:A=M
  deriving Show

data Decl =
     DT Name A      -- x:A
  |  DD D           -- x:A=M
  deriving Show

data P =
     P [Decl]
  deriving Show

data Rho = -- ρ
     RNil                  -- ()
  |  UpVar Rho Name Q      -- (ρ₁,x=q)
  |  UpDec Rho D           -- (ρ₁,x:A=M)
  deriving Show

data Q =  -- q
     QU                  -- U
  |  QK Qk               -- k
  |  QClos Name A M Rho  -- ⟨[x:A]M,ρ⟩
  deriving Show

data Qk =
     QVar Id
  |  QApp Qk Q
  deriving Show

getρ :: Name -> Rho -> Q
getρ x (UpVar ρ x' q) | x == x' = q
                      | otherwise = getρ x ρ
getρ x (UpDec ρ (DDef x' t e)) | x == x' = eval e ρ
                               | otherwise = getρ x ρ
getρ x RNil = error $ "getρ " ++ show x

eval :: M -> Rho -> Q
eval EU ρ = QU
eval (EK k) ρ = evalK k ρ
eval (EPi x t e) ρ = QClos x t e ρ
eval (EDef d m) ρ = eval m (UpDec ρ d)

evalK :: K -> Rho -> Q
evalK (KVar x) ρ = getρ x ρ
evalK (KApp k m) ρ = app (evalK k ρ) (eval m ρ)

app :: Q -> Q -> Q
app (QClos x t e ρ) q = eval e (UpVar ρ x q)
app (QK k) q = QK $ QApp k q
app q₁ q₂ = error $ "app " ++ show q₁ ++ " " ++ show q₂

data Γ =
     ΓNil
  |  ΓDT Γ Name A
  |  ΓDD Γ D

type Locked = [Name]

ϱ :: Locked -> Γ -> Rho
ϱ s ΓNil = RNil
ϱ s (ΓDT γ x t) = ϱ s γ
ϱ s (ΓDD γ d@(DDef x t e)) = if x `elem` s
                             then ρ
                             else UpDec ρ d
  where ρ = ϱ s γ

getType :: Γ -> Locked -> Name -> Q
getType ΓNil          s x             = error $ "getType: " ++ show x
getType (ΓDT γ' x' t) s x | x' == x   = eval t (ϱ s γ')
                          | otherwise = getType γ' s x
getType (ΓDD γ' (DDef x' t e)) s x | x' == x   = eval t (ϱ s γ')
                                   | otherwise = getType γ' s x

data G a = Success a | Fail Name

instance Functor G where
    fmap f (Success x) = Success (f x)
    fmap _ (Fail s) = Fail s

instance Applicative G where
    pure = Success
    (Success f) <*> (Success x) = Success (f x)
    (Fail s) <*> _ = Fail s
    _ <*> (Fail s) = Fail s

instance Monad G where
    (Success x) >>= k = k x
    (Fail s) >>= _ = Fail s

instance MonadFail G where
    fail = Fail . Id


type NS = [Name]

checkConvert :: Q -> Q -> NS -> G Bool
checkConvert QU QU _ = return True
checkConvert (QK (QVar x)) (QK (QVar y)) _ = return $ x == y
checkConvert (QK (QApp k₁ q₁)) (QK (QApp k₂ q₂)) ns =
  do checkConvertK k₁ k₂ ns
     checkConvert  q₁ q₂ ns
checkConvert (QClos x t e ρ) (QClos x' t' e' ρ') ns =
  do checkConvertE (eval t ρ) (eval t' ρ') ns
     checkConvertE (eval e (UpVar ρ x y)) (eval e' (UpVar ρ' x' y)) (y:ns)
     
checkConvert _ _ _ = return False
