module ExactCover (gameName, R, Move, p, epsilons) where

import Set
import AESelections

gameName = "exact cover"

-- The game has a set and a collection of subsets as a parameter.

set = [1..7]
collection = [[1,4,7],[1,4],[4,5,7],[3,5,6],[2,3,6,7],[2,7]]


-- The moves are members of the collection.

type Move = [Int]
type R = Bool

p :: [Move] -> R
p = f []
 where f xs [] = xs == set
       f xs (m : ms) = xs == set || (m `disjoint` xs  && f (xs `union` m) ms)
                       

epsilons :: [[Move] -> (Move -> R) -> Move]
epsilons = replicate (length collection) epsilon
  where epsilon played = if p played
                         then epsilonSome [[]] 
                         else epsilonSome (collection `varSetMinus` played)
