module Interval where

import Cubical.Abs
import Data.List (union,delete)

isTrue :: DisjFormula -> Bool
isTrue = (== fTrue)

isFalse :: DisjFormula -> Bool
isFalse = (== fFalse)

isTrueConj :: ConjFormula -> Bool
isTrueConj (Conj cf) = null cf

{- Directions environment -}

-- A `DirEnv` stores the list of zeros, ones and the diagonals partitions
type DirEnv = ([Ident],[Ident],[[Ident]])

emptyDirEnv :: DirEnv
emptyDirEnv = ([],[],[])

-- A `DirEnv` is inconsistent if there is an identifier
-- which is set both to zero and one
inconsistent :: DirEnv -> Bool
inconsistent (zeros,ones,diags) =
  any (`elem` ones) zeros || any (`elem` zeros) ones

-- Find the partition which contains `s`, if it exists.
-- Otherwise return the fake partition [s]
findPartition :: [[Ident]] -> Ident -> [Ident]
findPartition diags s = case filter (s `elem`) diags of
  [] -> [s]
  l  -> head l

-- Set an identifier to zero. Any eventual identifier which is in the same
-- partition must then be set to zero, and that partition is removed
addZero :: DirEnv -> Ident -> DirEnv
addZero (zeros,ones,diags) s =
  let toadd = findPartition diags s
  in (toadd ++ zeros,ones,delete toadd diags)

-- Set an identifier to one. Any eventual identifier which is in the same
-- partition must then be set to one, and that partition is removed
addOne :: DirEnv -> Ident -> DirEnv
addOne (zeros,ones,diags) s =
  let toadd = findPartition diags s
  in (zeros,toadd ++ ones,delete toadd diags)

addDiag :: DirEnv -> Ident -> Ident -> DirEnv
addDiag dirs@(zeros,ones,diags) s1 s2
  | s1 == s2 = dirs -- Trivial, nothing to do
  | s1 `elem` zeros = addZero dirs s2 -- `s1` already zero -> set `s2` to zero
  | s2 `elem` zeros = addZero dirs s1 -- `s2` already zero -> set `s1` to zero
  | s1 `elem` ones  = addOne  dirs s2 -- `s1` already one -> set `s2` to one
  | s2 `elem` ones  = addOne  dirs s1 -- `s2` already one -> set `s1` to zero
  | otherwise = let
{-
λ> let dirs = ([],[],[[(Ident "i"),(Ident "k")],[(Ident "j"),(Ident "l")]])
λ> addDiag dirs (Ident "i") (Ident "j")
([],[],[[i,k,j,l]])
λ> addDiag dirs (Ident "v") (Ident "w")
([],[],[[i,k],[j,l],[v,w]])
λ> addDiag dirs (Ident "i") (Ident "w")
([],[],[[j,l],[i,k,w]])
-}
      par1 = findPartition diags s1
      par2 = findPartition diags s2
      diags' = delete par2 (delete par1 diags) ++ [par1 `union` par2]
    in (zeros,ones,diags')

-- Add a conjunction to a `DirEnv`
addConj :: DirEnv -> ConjFormula -> DirEnv
addConj dirs (Conj conj) = foldl addAtomic dirs conj
  where
    addAtomic :: DirEnv -> AtomicFormula -> DirEnv
    addAtomic dirs' ff = case ff of
      Eq0 s -> addZero dirs' s
      Eq1 s -> addOne dirs' s
      Diag s s' -> addDiag dirs' s s'

-- Conversion from a conjunction to a `DirEnv`
conjToDirEnv :: ConjFormula -> DirEnv
conjToDirEnv = addConj emptyDirEnv

-- Test if a `DirEnv` makes an atomic formula true.
-- A diagonal is true iff both are zero, or both are true, or if
-- they are in the same partition
makesTrueAtomic :: DirEnv -> AtomicFormula -> Bool
(zeros,ones,diags) `makesTrueAtomic` af = case af of
  Eq0 s -> s `elem` zeros
  Eq1 s -> s `elem` ones
  Diag s1 s2 -> s1 == s2 || bothIn zeros || bothIn ones || any bothIn diags
    where bothIn set = s1 `elem` set && s2 `elem` set

-- A conjunction is true iff all of its atomic formulas are true
makesTrueConj :: DirEnv -> ConjFormula -> Bool
makesTrueConj dirs (Conj cf) = all (dirs `makesTrueAtomic`) cf

-- A disjunction is true iff one of its conjunctive formulas is true
makesTrueDisj :: DirEnv -> DisjFormula -> Bool
makesTrueDisj dirs (Disj df) = any (dirs `makesTrueConj`) df

-- Substitute `s'` for `s` in an atomic formula
substAtomic :: (Ident,Ident) -> AtomicFormula -> AtomicFormula
substAtomic (s,s') af = case af of
  Eq0 x | s == x -> Eq0 s'
  Eq1 x | s == x -> Eq1 s'
  Diag x y -> Diag (if x == s then s' else x) (if y == s then s' else y)
  otherwise -> af

-- Substitute into each atomic formula of the conjunction
substConj :: (Ident,Ident) -> ConjFormula -> ConjFormula
substConj (s,s') (Conj cf) = Conj $ map (substAtomic (s,s')) cf

-- Concatenation (logical AND) between two conjunctive formulas
meet :: ConjFormula -> ConjFormula -> ConjFormula
(Conj cf1) `meet` (Conj cf2) = Conj $ cf1 ++ cf2

{- Implication and equivalence -}

{- A disjunctive formula implies another one if each of its conjunctions
makes the second formula true. The case where the second formula is false
must be handled separately. The first two checks are unnecessary, used only
for efficiency -}
impDisj :: DirEnv -> DisjFormula -> DisjFormula -> Bool
impDisj dirs disj1@(Disj df1) disj2 = isFalse disj1 || isTrue disj2 ||
  if isFalse disj2 then
    all (inconsistent . addConj dirs) df1 -- First formula must be false
  else
    all (\cf1 -> addConj dirs cf1 `makesTrueDisj` disj2) df1

-- Two formulas are equal is each one imply the other
eqFormulas :: DirEnv -> DisjFormula -> DisjFormula -> Bool
eqFormulas dirs disj1 disj2 = impDisj dirs disj1 disj2 && impDisj dirs disj2 disj1
