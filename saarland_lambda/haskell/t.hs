import AbsLam
import AbsDB
import qualified ParLam   as Lam ( pPreterm, myLexer )
import qualified PrintLam as Lam ( printTree )
import qualified ParDB    as DB  ( pTerm, myLexer )
import qualified PrintDB  as DB  ( printTree )

import Data.List ( genericLength )
import Data.Either.Utils ( fromRight )
import Data.Function ( (&) )

b :: Preterm -> [Integer] -> Term
b' :: [Integer] -> Integer -> Integer

b (Var x) c = DBVar (b' c x)
b (App m n) c = DBApp (b m c) (b n c)
b (Lam x m) c = DBLam (b m (x:c))

b' [] x = x
b' (y:c) x = if y==x then 0 else (+1) $ b' c x

x = [] & (b $ fromRight $ Lam.pPreterm . Lam.myLexer $ "λ100.λ101.λ120.100 101 120")
y = "λ100.λ101.λ120.100 101 120" & Lam.pPreterm . Lam.myLexer & fromRight & b $ []

z = "λλλ2 1 0" & DB.pTerm . DB.myLexer & fromRight

y' = "λ100.λ101.λ102.102 101 100 0" & Lam.pPreterm . Lam.myLexer & fromRight & b $ []

w =  "λ100.λ100.100 100" & Lam.pPreterm . Lam.myLexer & fromRight & b $ []

-- de Bruijn levels
l :: Preterm -> [Integer] -> Term
l' :: [Integer] -> Integer -> Integer

l' [] x = x
l' (y:c) x = if y==x then genericLength c else l' c x

l (Var x) c = DBVar (l' c x)
l (App m n) c = DBApp (l m c) (l n c)
l (Lam x m) c = DBLam (l m (x:c))

w' = "λ100.(λ101.100 101) 100" & Lam.pPreterm . Lam.myLexer & fromRight & b $ []
w'' = "λ100.(λ101.100 101) 100" & Lam.pPreterm . Lam.myLexer & fromRight & l $ []
w''' = "λ100.(λ101.100 101) 10" & Lam.pPreterm . Lam.myLexer & fromRight & l $ []
