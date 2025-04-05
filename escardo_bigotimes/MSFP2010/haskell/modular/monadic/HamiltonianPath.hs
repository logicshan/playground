module HamiltonianPath (gameName, R, Move, p, epsilons) where

import Set
import AESelections
import J

gameName = "hamiltonian path"

-- The game has a graph as a parameter.

vertices = [1..6]
edges = [ (1,2), (1,5), (2,3), (2,5), (3,4), (4,6) ]
edge x y = (x, y) `varIsIn` edges

-- A solution is a path.  The moves are the vertices, but each vertex
-- can be played only once.

type Move = Int 
type R = Bool

p :: [Move] -> R
p [] = True
p [x] = True
p (x : xs@(y : ys)) = edge x y  &&  p xs

epsilons :: [[Move] -> J R Move]
epsilons = replicate (length vertices) epsilon
  where epsilon played = epsilonSome (vertices `varSetMinus` played)
