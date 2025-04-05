module DependentBigotimes (otimes, bigotimes) where


type J r x = (x -> r) -> x

prefix :: x -> ([x] -> r) -> ([x] -> r)
prefix x p xs = p(x : xs)

otimes :: J r x -> (x -> J r [x]) -> J r [x]
(epsilon `otimes` delta) p = a : b a
    where b x = delta x (prefix x p)
          a = epsilon(\x -> p(x : b x))

bigotimes :: [[x] -> J r x] -> J r [x]
bigotimes [] = \p -> []
bigotimes (epsilon : epsilons) =  
    (epsilon []) `otimes` (\x -> bigotimes (map (prefix x) epsilons))

