module J (J(J), selection, unitJ, functorJ, muJ, module K, morphismJK) where

import K

newtype J r x = J {selection :: (x -> r) -> x}

morphismJK :: J r x -> K r x
morphismJK e = K(\p -> p(selection e p))

unitJ :: x -> J r x
unitJ x = J(\p -> x)

functorJ :: (x -> y) -> J r x -> J r y
functorJ f e = J(\q -> f(selection e (\x -> q(f x))))

muJ :: J r(J r x) -> J r x
muJ e = J(\p -> selection(selection e(\d -> quantifier(morphismJK d) p)) p)

instance Monad (J r) where
  return = unitJ
  e >>= f = muJ(functorJ f e)
