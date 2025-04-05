module Set (isIn, varIsIn, insert, contained, someContained, 
            delete, varDelete, union, bigUnion, disjoint, intersection, 
            setMinus, varSetMinus,
            some, every) 
where

-- Finite sets represented as sorted lists without repetitions.  

isIn :: Ord x => x -> [x] -> Bool
isIn x [] = False
isIn x (y : ys)
   | x <  y    = False
   | x == y    = True
   | otherwise = isIn x ys

insert :: Ord x => x -> [x] -> [x]
insert x [] = [x]
insert x (vs@(y : ys)) 
    | x == y       = vs
    | x <  y       = x : vs
    | otherwise    = y : insert x ys

contained :: Ord x => [x] -> [x] -> Bool
contained [] ys = True
contained xs [] = False
contained (us@(x : xs)) (y : ys) 
    | x == y    = contained xs ys
    | x >= y    = contained us ys
    | otherwise = False

someContained :: Ord x => [[x]] -> [x] -> Bool
someContained [] ys = False
someContained xss [] = False
someContained (xs : xss) ys = contained xs ys || someContained xss ys

delete :: Ord x => x -> [x] -> [x]
delete x [] = []
delete x (vs@(y : ys))
    | x == y    = ys 
    | x <  y    = vs
    | otherwise = y : delete x ys 

union :: Ord x => [x] -> [x] -> [x]
union xs [] = xs
union [] ys = ys
union (us@(x : xs)) (vs@(y : ys)) 
    | x == y       = union xs vs
    | x <  y       = x : union xs vs
    | otherwise    = y : union us ys

bigUnion :: Ord x => [[x]] -> [x] 
bigUnion [] = []
bigUnion (xs : xss) = union xs (bigUnion xss)

disjoint :: Ord x => [x] -> [x] -> Bool
disjoint xs [] = True
disjoint [] ys = True
disjoint (us@(x : xs)) (vs@(y : ys)) 
    | x == y       = False
    | x <  y       = disjoint xs vs
    | otherwise    = disjoint us ys

intersection :: Ord x => [x] -> [x] -> [x]
intersection xs [] = []
intersection [] ys = []
intersection (us@(x : xs)) (vs@(y : ys)) 
    | x == y       = x : intersection xs vs
    | x <  y       = intersection xs vs
    | otherwise    = intersection us ys



-- In one of our applications the second argument ys is not sorted:

setMinus :: Ord x => [x] -> [x] -> [x]
setMinus xs [] = xs
setMinus xs (y : ys) = setMinus (delete y xs) ys

-- In another application neither argument is sorted in the following:

varIsIn :: Ord x => x -> [x] -> Bool
varIsIn x [] = False
varIsIn x (y : ys)
   | x == y    = True
   | otherwise = isIn x ys

varDelete :: Ord x => x -> [x] -> [x]
varDelete x [] = []
varDelete x (y : ys) 
    | x == y    = ys
    | otherwise = y : varDelete x ys 

varSetMinus :: Ord x => [x] -> [x] -> [x]
varSetMinus xs [] = xs
varSetMinus xs (y : ys) = varSetMinus (varDelete y xs) ys

-- Some "logic" now:

some, every  :: [a] -> (a -> Bool) -> Bool
some xs p = any p xs
every xs p = all p xs

