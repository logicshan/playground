module ExactHittingSet (gameName, R, Move, p, epsilons) where

import Set
import AESelections
import J

gameName = "exact hitting set"

-- The game has a set and a collection of subsets as a parameter.

set = [1..7]
collection = [[1,4,7],[1,4],[4,5,7],[3,5,6],[2,3,6,7],[2,7]]

-- The moves are members of the collection.

type Move = Int
type R = Bool

p :: [Move] -> R
p ms = every collection (\s -> length(s `intersection` ms) == 1) 
                       

-- I'll use -1 to indicate that nothing is played.

epsilons :: [[Move] -> J R Move]
epsilons = replicate (length collection) epsilon
  where epsilon played = if p played
                         then epsilonSome [-1] 
                         else epsilonSome (set `varSetMinus` played)
