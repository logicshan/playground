-----------------------------------------
-- Main module
-----------------------------------------

module Main2 where

import Prelude hiding ((*))

----------------------------------------------------------
-- Expressions
-----------------------------------------------------------

type Name = String

data Exp = -- M,N,A,B
   ELam  Patt Exp       -- λp.M
 | ESet                 -- U
 | EPi   Patt Exp Exp   -- Πp:A.B
 | ESig  Patt Exp Exp   -- Σp:A.B
 | EOne                 -- 𝟙
 | Eunit                -- ₀
 | EPair Exp Exp        -- M,N
 | ECon  Name Exp       -- cM
 | ESum  Branch         -- Sum S
 | EFun  Branch         -- fun S
 | EFst  Exp            -- M.1
 | ESnd  Exp            -- M.2
 | EApp  Exp Exp        -- MN
 | EVar  Name           -- x
 | EVoid
 | EDec  Decl Exp       -- D;M
  deriving (Eq,Ord,Show)

data Decl = -- D
   Def  Patt Exp Exp     -- p:A=M
 | Drec Patt Exp Exp     -- rec p:A=M
  deriving (Eq,Ord,Show)

data Patt = -- p
   PPair Patt Patt       -- p,p
 | Punit                 -- _
 | PVar Name             -- x
  deriving (Eq,Ord,Show)

type Branch = [(Name,Exp)]  -- S ∷= () | (cM,S)

-----------------------------------------------------------
-- Values
-----------------------------------------------------------

data Val = -- u,v,t
     Lam Clos         -- λf
  |  Pair Val Val     -- u,v
  |  Con Name Val     -- cv
  |  Unit             -- ₀
  |  Set              -- U
  |  Pi  Val Clos     -- Πtg
  |  Sig Val Clos     -- Σtg
  |  One              -- 𝟙
  |  Fun SClos        -- fun s
  |  Sum SClos        -- Sum s
  |  Nt Neut          -- [k]
  deriving Show

data Neut = -- k
     Gen Int          -- xₙ
  |  App Neut Val     -- kv
  |  Fst Neut         -- k.1
  |  Snd Neut         -- k.2
  |  NtFun SClos Neut -- sk
  deriving Show

type SClos = (Branch, Rho)   -- s ∷= ⟨S,ρ⟩

-- Function closures
data Clos = -- f,g
     Cl Patt Exp Rho  -- ⟨λp.M,ρ⟩
  |  ClCmp Clos Name  -- f∘c
  deriving Show

-- instantiation of a closure by a value
(*) :: Clos -> Val -> Val
(Cl p e rho) * v = eval e (UpVar rho p v)
(ClCmp f c ) * v = f * Con c v

mkCl :: Patt -> Exp -> Rho -> Clos
mkCl p e rho = Cl p e rho

clCmp :: Clos -> Name -> Clos
clCmp g c = ClCmp g c
{-
get s [] = error ("get " ++ show s)
get s ((s1,u):us) | s == s1 = u
get s ((s1,u):us)           = get s us
-}
app :: Val -> Val -> Val
app (Lam f)                  v = f * v
app (Fun (ces, rho)) (Con c v) = app (eval e rho) v
                                 where e = head [e' | (c',e') <- ces, c == c']
app (Fun s)          (Nt k)    = Nt(NtFun s k)
app (Nt k)                   m = Nt(App k m)
app w u                        = error "app "

vfst :: Val -> Val
vfst (Pair u1 _) = u1
vfst (Nt k)      = Nt(Fst k)
vfst w           = error "vfst "

vsnd :: Val -> Val
vsnd (Pair _ u2) = u2
vsnd (Nt k)      = Nt(Snd k)
vsnd w           = error "vsnd "

---------------------------------------------
-- Environment
---------------------------------------------

data Rho = -- ρ
     RNil                -- ()
  |  UpVar Rho Patt Val  -- ρ,p=v
  |  UpDec Rho Decl      -- ρ,D
  deriving Show

getRho :: Rho -> Name -> Val
getRho (UpVar rho p v) x | x `inPat` p = patProj p x v
                         | otherwise   = getRho rho x
getRho (UpDec rho (Def p _ e)) x
  | x `inPat` p = patProj p x (eval e rho)
  | otherwise = getRho rho x
getRho rho0@(UpDec rho (Drec p _ e)) x
  | x `inPat` p = patProj p x (eval e rho0)
  | otherwise = getRho rho x
getRho RNil _ = error "getRho"

inPat :: Name -> Patt -> Bool
inPat x (PVar y)      = x == y
inPat x (PPair p1 p2) = inPat x p1 || inPat x p2
inPat _ Punit         = False

patProj :: Patt -> Name -> Val -> Val
patProj (PVar y)      x v | x == y       = v
patProj (PPair p1 p2) x v | x `inPat` p1 = patProj p1 x (vfst v)
                          | x `inPat` p2 = patProj p2 x (vsnd v)
patProj _ _ _ = error "patProj"

lRho :: Rho -> Int
lRho RNil            = 0
lRho (UpVar rho _ _) = lRho rho + 1
lRho (UpDec rho _ )  = lRho rho

eval :: Exp -> Rho -> Val
eval e0 rho = case e0 of
  ESet        -> Set
  EDec d e    -> eval e (UpDec rho d)
  ELam p e    -> Lam $ mkCl p e rho
  EPi  p a b  -> Pi  (eval a rho) $ mkCl p b rho
  ESig p a b  -> Sig (eval a rho) $ mkCl p b rho
  EOne        -> One
  Eunit       -> Unit
  EFst e      -> vfst (eval e rho)
  ESnd e      -> vsnd (eval e rho)
  EApp e1 e2  -> app (eval e1 rho) (eval e2 rho)
  EVar x      -> getRho rho x
  EPair e1 e2 -> Pair (eval e1 rho) (eval e2 rho)
  ECon c e1   -> Con c (eval e1 rho)
  ESum cas    -> Sum (cas, rho)
  EFun ces    -> Fun (ces, rho)
  e -> error $ "eval: " ++ show e 

-----------------------------------------------------------
-- Normal forms
data NExp = -- E
     NLam Int NExp        -- λxᵢ.E
  |  NPair NExp NExp      -- E₁,E₂
  |  NCon Name NExp       -- cE
  |  NUnit                -- ₀
  |  NSet                 -- U
  |  NPi  NExp Int NExp   -- Πxᵢ:E₁.E₂
  |  NSig NExp Int NExp   -- Σxᵢ:E₁.E₂
  |  NOne                 -- 𝟙
  |  NFun NSClos          -- fun⟨S,α⟩
  |  NSum NSClos          -- Sum⟨S,α⟩
  |  NNt NNeut            -- [K]
  deriving (Eq,Show)

data NNeut = -- K
     NGen Int             -- xᵢ
  |  NApp NNeut NExp      -- KE
  |  NFst NNeut           -- K.1
  |  NSnd NNeut           -- K.2
  |  NNtFun NSClos NNeut  -- ⟨S,α⟩K
  deriving (Eq,Show)

type NSClos = (Branch, NRho)  -- ⟨S,α⟩

data NRho = -- α
     NRNil                   -- ()
  |  NUpVar NRho Patt NExp   -- (α,p=E)
  |  NUpDec NRho Decl        -- (α,D)
  deriving (Eq,Show)

-------------------------------------------
-- Readback functions
-------------------------------------------

rbV :: Int -> Val -> NExp
rbV k v0 = case v0 of
  Lam f       -> NLam k (rbV (k+1) (f * genV k))
  Pair u v    -> NPair (rbV k u) (rbV k v)
  Con  c v    -> NCon c (rbV k v)
  Unit        -> NUnit
  Set         -> NSet
  Pi  t g     -> NPi  (rbV k t) k (rbV (k+1) (g * genV k))
  Sig t g     -> NSig (rbV k t) k (rbV (k+1) (g * genV k))
  One         -> NOne
  Fun (s,rho) -> NFun (s,rbRho k rho)
  Sum (s,rho) -> NSum (s,rbRho k rho)
  Nt l        -> NNt (rbN k l)

rbN :: Int -> Neut -> NNeut
rbN i k0 = case k0 of
  Gen j           -> NGen j
  App k m         -> NApp (rbN i k) (rbV i m)
  Fst k           -> NFst (rbN i k)
  Snd k           -> NSnd (rbN i k)
  NtFun (s,rho) k -> NNtFun (s,rbRho i rho) (rbN i k)

rbRho :: Int -> Rho -> NRho
rbRho _ RNil            = NRNil
rbRho i (UpVar rho p v) = NUpVar (rbRho i rho) p (rbV i v)
rbRho i (UpDec rho d )  = NUpDec (rbRho i rho) d

------------------------------------------------
-- Error monad and type environment
------------------------------------------------

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
    fail = Fail

type Γ = [(Name,Val)]

lookupG :: (Show a, Eq a) => a -> [(a,b)] -> G b
lookupG s [] = fail ("lookupG " ++ show s)-- should never occur
lookupG s ((s1,u):us) | s == s1 = return u
lookupG s ((s1,u):us)           = lookupG s us

-- Updating type environment Γ ⊢ p : t = u ⇒ Γ'
upG :: Γ -> Patt -> Val -> Val -> G Γ
upG γ Punit         _         _ = return γ
upG γ (PVar x)      t         _ = return $ (x,t):γ
upG γ (PPair p1 p2) (Sig t g) v =
  do γ1 <- upG γ p1 t (vfst v)
     upG γ1 p2 (g * vfst v) (vsnd v)
upG _ p             _         _ =
  fail $ "upG: p = " ++ show p

-------------------------------------------------
-- Type checking rules
-------------------------------------------------

genV :: Int -> Val
genV k = Nt (Gen k)

-- There are four forms of judgements.
--  checkD  ρ,Γ ⊢ₗ D ⇒ Γ'  D is a correct declaration and extends Γ to Γ'
--  checkT  ρ,Γ ⊢ₗ A       A is a correct type expression
--  check   ρ,Γ ⊢ₗ M ⇐ t   M is a correct expression of the given type t
--  checkI  ρ,Γ ⊢ₗ M ⇒ t   M is a correct expression and its type is
--                        inferred to be t

checkD :: Int -> Rho -> Γ -> Decl -> G Γ
checkT :: Int -> Rho -> Γ -> Exp -> G ()
check  :: Int -> Rho -> Γ -> Exp -> Val -> G ()
checkI :: Int -> Rho -> Γ -> Exp -> G Val

checkT k rho gma e0 =
  case e0 of
    EPi  p a b -> do checkT k rho gma a
                     gma1 <- upG gma p (eval a rho) (genV k)
                     checkT (k+1) (UpVar rho p (genV k)) gma1 b
    ESig p a b -> checkT k rho gma (EPi p a b)
    ESet       -> return ()
    a          -> check k rho gma a Set

check k rho gma e0 t0 =
  case (e0, t0) of
    (ELam p e , Pi t g )->
      do let gen = genV k
         gma1 <- upG gma p t gen
         check (k+1) (UpVar rho p gen) gma1 e (g * gen)
    (EPair e1 e2, Sig t g )->
      do check k rho gma e1 t
         check k rho gma e2 (g * eval e1 rho)
    (ECon c e , Sum (cas,rho1))->
      do a <- lookupG c cas
         check k rho gma e (eval a rho1)
    (EFun ces, Pi (Sum (cas, rho1)) g) ->
      if map fst ces == map fst cas
      then sequence_ [check k rho gma e (Pi (eval a rho1) (clCmp g c))
                     | ((c,e), (_,a)) <- zip ces cas]
      else fail "case branches does not match the data type"
    (Eunit , One)-> return ()
    (EOne  , Set)-> return ()
    (EPi p a b , Set)->
      do check k rho gma a Set
         let gen = genV k
         gma1 <- upG gma p (eval a rho) gen
         check (k+1) (UpVar rho p gen) gma1 b Set
    (ESig p a b , Set)-> check k rho gma (EPi p a b) Set
    (ESum cas, Set) ->
      sequence_ [check k rho gma a Set | (_,a) <- cas]
    (EDec d e , t )-> do gma1 <- checkD k rho gma d
                         check k (UpDec rho d) gma1 e t
    (e        , t )-> do t1 <- checkI k rho gma e
                         eqNf k t t1
  where
    eqNf :: Int -> Val -> Val -> G ()
    eqNf i m1 m2
      | e1 == e2 = return ()
      | otherwise = fail $ "eqNf: " ++ show e1 ++ "=/=" ++ show e2
      where e1 = rbV i m1
            e2 = rbV i m2

checkI k rho gma e0 =
  case e0 of
    EVar x     -> lookupG x gma
    EApp e1 e2 -> do t1 <- checkI k rho gma e1
                     (t, g) <- extPiG t1
                     check k rho gma e2 t
                     return (g * eval e2 rho)
    EFst e -> do t <- checkI k rho gma e
                 (a,_) <- extSigG t
                 return a
    ESnd e -> do t <- checkI k rho gma e
                 (_, g) <- extSigG t
                 return (g * vfst (eval e rho))
    e -> fail ("checkI: " ++ show e)
  where
    extPiG :: Val -> G (Val, Clos)
    extPiG (Pi t g) = return (t, g)
    extPiG u = fail ("extPiG " ++ showVal u)

    extSigG :: Val -> G (Val, Clos)
    extSigG (Sig t g) = return (t, g)
    extSigG u = fail ("extSigG " ++ showVal u)

showVal u = show (rbV 0 u)

checkD k rho gma d@(Def p a e) = do
  checkT k rho gma a
  let t = eval a rho
  check k rho gma e t
  upG gma p t (eval e rho)

checkD k rho gma d@(Drec p a e) = do
  checkT k rho gma a
  let t = eval a rho
      gen = genV k
  gma1 <- upG gma p t gen
  check (k+1) (UpVar rho p gen) gma1 e t
  let v = eval e (UpDec rho d)
  upG gma p t v

------------------------------------------------------
-- Main checking routines
------------------------------------------------------

-- The input is checked as an expression of type One.
checkMain :: Exp -> G ()
checkMain e = check 0 RNil [] e One

-- checking a string input
checkStr :: String -> IO()
checkStr s =
  case parseExp $ myLex s of -- parsing using routines
    Fail msg -> putStrLn $ "Parse error: " ++ msg
    Success (e,_) ->
      case checkMain e of
        Fail msg' ->
          putStrLn ("type-checking failed:\n" ++ msg')
        Success _ ->
          putStrLn ("type-checking succeded.")

-- checking the content of a file.
checkFile :: String -> IO()
checkFile file = checkStr =<< readFile file
