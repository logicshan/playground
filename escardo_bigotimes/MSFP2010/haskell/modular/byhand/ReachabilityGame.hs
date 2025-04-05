module ReachabilityGame (gameName, R, Move, p, epsilons) where

import Set
import AESelections

gameName = "reachability"

-- The game has the following parameters: a directed graph, an origin
-- node, and a destination node

vertices = [1..6]
edges = [ (1,2), (1,5), (2,3), (2,5), (3,4), (4,6) ]
origin = 1
destination = 6
edge x y = (x, y) `varIsIn` edges

-- A solution is a path from origin to destination.  The moves are the
-- vertices, but each vertex can be played only once.

type Move = Int 
type R = Bool

p :: [Move] -> R
p [] = False
p [x] = x == destination 
p (x : xs@(y : ys)) = x == destination || (edge x y && p xs)

-- The first legal move is origin, and then any vertex that hasn't
-- been played yet:

epsilons :: [[Move] -> (Move -> R) -> Move]
epsilons = epsilonOrigin : replicate (length edges - 2) epsilon
  where epsilonOrigin [] = epsilonSome [origin]
        epsilon played = epsilonSome (vertices `varSetMinus` played)
