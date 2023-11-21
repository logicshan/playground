import Misc
import Lambda
import IdInt
import Simple
import Unique
import HOAS
import DeBruijn

main :: IO ()
main = interactArgs $
       \ args -> (++ "\n") . show . myNF args . toIdInt . f . read . stripComments
  where f :: LC Id -> LC Id -- just to force the type
        f e = e
        myNF ["U"] = Unique.nf
        myNF ["H"] = HOAS.nf
        myNF ["D"] = DeBruijn.nf
        myNF ["S"] = Simple.nf
