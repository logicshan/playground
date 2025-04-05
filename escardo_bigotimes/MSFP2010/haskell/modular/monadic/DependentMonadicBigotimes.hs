module DependentMonadicBigotimes (varotimes, otimes, bigotimes) where

otimes :: Monad m => m x -> (x -> m y) -> m(x, y)
xm `otimes` ym =
    do x <- xm            
       y <- ym x
       return (x, y)

varotimes :: Monad m => m x -> (x -> m [x]) -> m [x]
xm `varotimes` xsm =
    do x <- xm            
       xs <- xsm x
       return (x : xs)

bigotimes :: Monad m => [[x] -> m x] -> m[x]
bigotimes [] = return []
bigotimes (xm : xms) = 
    do x <- xm []
       xs <- bigotimes[\ys -> ym(x:ys) | ym <- xms]
       return(x : xs)



