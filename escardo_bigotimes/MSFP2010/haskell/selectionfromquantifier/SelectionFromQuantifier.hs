-- This bit hasn't been included in the Escardo--Oliva MSFP'2010 paper
-- for lack of space. Based on "Exhaustible sets in higher-type
-- computation", LMCS'2008 (there are some improvements).
--
-- Haskell program for showing that non-empty exhaustible sets are
-- searchable. We restrict this to certain types in this
-- implementation.


type J r x = (x -> r) -> x 
type K r x = (x -> r) -> r


-- Type of natural numbers:

type N = Integer

least :: Num n => (n -> Bool) -> n
least p = if p 0 then 0 else 1 + least(\n -> p(n+1))

-- See below for remarks & programs regarding avoidance of unbounded
-- search (it is possible, but less effiecient).

-- The intersection of an exhaustible set with a clopen is exaustible:

cap :: K Bool x -> (x -> Bool) -> K Bool x
phi `cap` p = \q -> phi(\x -> q x && p x)

-- We assume that the input is the existential quantifier of some
-- non-empty set of natural numbers:

inhabited :: K Bool x -> Bool
inhabited forsome = forsome(\x -> True)

witnessN :: K Bool N -> N
witnessN forsome = least(\n -> forsome(\m -> n == m))

selectionFromQuantifierN :: K Bool N -> J Bool N
selectionFromQuantifierN forsome p 
   | forsome p  = witnessN (forsome `cap` p) 
   | otherwise  = witnessN forsome

-- This enumerates the elements of an exhaustible set given by an
-- existential quantifier:

enum :: K Bool N -> [N]
enum forsome  
    | inhabited forsome = w : enum(forsome `cap` (\n -> n > w))
    | otherwise         = []                  
 where w = witnessN forsome

-- The above works if the input is guaranteed to be an existential
-- quantifier. Perhaps surprisingly, this condition can be checked,
-- using the fact that predicates N->Bool are elements of the Cantor
-- space, and so we could have included this check to make the
-- functions total:

isExistentialN :: K Bool N -> Bool
isExistentialN phi = 
   phi(\x -> False)==False &&
   foreveryCantor'(\p -> 
   foreveryCantor'(\q -> (phi p || phi q) == phi(\n -> p n || q n)))

-- Moreover, the least number operator can be avoided. If we use the
-- fan functional instead, only total functions are used in the
-- definition, replacing uses least-number search bounded by the
-- fan. Here is just one example:

dependsOn :: K Bool N -> N -> Bool
phi `dependsOn` n = forsomeCantor'(\p -> phi p /= phi (p `flip` n))
  where p `flip` n = \m -> if m == n then not(p m) else p m

enum' :: K Bool N -> [N]
enum' phi = [ n | n<-[0..fan(phi.decode)], phi `dependsOn` n]

-- This is slower, though. But it works also when the input
-- is not an existential quantifier, and is total.

-- Some tests before proceeding with the harder, more interesting stuff:

samplephi p = p 3 || p 7 || p 10
samplephi' p = p 3 && p 7 && p 10
samplephi'' p = False

{--

*Main> samplephi `dependsOn` 3
True

*Main> samplephi `dependsOn` 4
False

*Main> isExistentialN samplephi
True

*Main> isExistentialN samplephi'
False

*Main> isExistentialN samplephi''
True

*Main> enum samplephi            
[3,7,10]

*Main> enum samplephi''
[]

*Main> enum' samplephi
[3,7,10]

*Main> enum' samplephi'
[3,7,10]

--}


-- We now do the same for the Baire space of infinite sequences of
-- natural numbers. That is, we look at exhaustible subsets of the
-- Baire space, and show that they are searchable if they are
-- non-empty. We again assume that the inputs are existential
-- quantifiers (this time we can't decide whether inputs are good):

witnessBaire :: K Bool [N] -> [N]
witnessBaire forsome = [a n | n<-[0..]]
 where a n = least(\k -> 
              forsome(\b -> 
               all (\n -> a n == b !! n) [0..n-1]  &&  b !! n == k))

selectionFromQuantifierBaire :: K Bool [N] -> J Bool [N]
selectionFromQuantifierBaire forsome p 
   | forsome p  = witnessBaire (forsome `cap` p) 
   | otherwise  = witnessBaire forsome


-- We emphasize that again this works for existential quantifiers
-- only. Here is a test:

findBit :: J Bool N
findBit p = if p 0 then 0 else 1

findC :: J Bool [N]
findC = bigotimes (repeat findBit)

forsomeC :: K Bool [N]
forsomeC = overline findC

findC' :: J Bool [N]
findC' = selectionFromQuantifierBaire forsomeC

{--

*Main> take 5 (findC'(\a -> a !! 1 == 1 && a !! 3 == 1))            
[0,1,0,1,0]
(1.14 secs, 90926064 bytes)

--}


-- This is not very efficient (it is how it was defined in the
-- LMCS'2008 paper). Here is a more efficient and structured way of
-- implementing the same algorithm co-inductively:

witnessBaire' :: K Bool [N] -> [N]
witnessBaire' forsome = 
  h : witnessBaire'(kimage tail (forsome `cap` (\a -> head a == h)))
 where h = witnessN(kimage head  forsome)

kimage :: (x -> y) -> K r x -> K r y
kimage f phi = \q -> phi(\x -> q(f x))

selectionFromQuantifierBaire' :: K Bool [N] -> J Bool [N]
selectionFromQuantifierBaire' forsome p 
   | forsome p  = witnessBaire' (forsome `cap` p) 
   | otherwise  = witnessBaire' forsome


-- Again, the least-number operator is not necessary (and so this is
-- definable in system T extended with a recursion equation for the
-- fan functional).

-- Let's test this, using a manifestation of the Cantor space within
-- the Cantor space (called C)

findC'' :: J Bool [N]
findC'' = selectionFromQuantifierBaire' forsomeC

{--

*Main> take 5 (findC''(\a -> a !! 1 == 1 && a !! 3 == 1))
[0,1,0,1,0]
(0.01 secs, 538164 bytes)

--}


-- More general types. We have discussed N and the infinite streams in
-- [N] (the latter is N->N upto coding). The above method can be
-- extended to all types obtained starting from Bool and N and closing
-- under function types, using the so-called Kleene--Kreisel density
-- theorem. An implementation of this theorem is not difficult, but we
-- need a different program for each type (hence we need countably
-- many different programs -- but they can be automatically
-- constructed as a function of the type). However, the resulting
-- functions for finding witnesses from existential quantifiers would
-- probably be extremely inefficient. See the LMCS'2008 paper.


-- END, for the moment. We may include more about this in the future.


-- Tychonoff & related stuff (used above).

overline :: J r x -> K r x
overline e = \p -> p(e p)

image :: (x -> y) -> J r x -> J r y
image f e = \q -> f(e(\x -> q(f x)))

otimes :: J r x -> J r [x] -> J r [x]
otimes e0 e1 p = a0 : a1
  where a0 = e0(\x0 -> overline e1 (\x1 -> p(x0:x1)))
        a1 = e1(\x1 -> p(a0 : x1))

bigotimes :: [J r x] -> J r [x]
bigotimes [] = \p -> []
bigotimes (e:es) = e `otimes` bigotimes es 

findBool :: J Bool Bool
findBool p = p True

findCantor :: J Bool [Bool]
findCantor = bigotimes(repeat findBool)

forsomeCantor, foreveryCantor :: K Bool [Bool]
forsomeCantor = overline findCantor 
foreveryCantor p = not(forsomeCantor(not.p))

code :: (N -> Bool) -> [Bool]
code f = [f i| i<-[0..]]

decode :: [Bool] -> (N -> Bool)
decode xs i =  xs `at` i

at :: [x] -> N -> x
at (x:xs) 0 = x
at (x:xs) (n+1) = at xs n

findCantor' :: J Bool (N -> Bool)
findCantor' = image decode findCantor

forsomeCantor' :: K Bool (N -> Bool)
forsomeCantor' = overline findCantor'

foreveryCantor' :: K Bool (N -> Bool)
foreveryCantor' p = not(forsomeCantor'(not.p))


-- The following definition of the fan functional was given in
-- U. Berger's thesis (1990):

fan :: Num n => Ord n => Eq z => ([Bool] -> z) -> n
fan f = if foreveryCantor(\a -> f a == f(repeat False))
        then 0
        else 1 + max (fan(f.(False:))) (fan(f.(True:)))
