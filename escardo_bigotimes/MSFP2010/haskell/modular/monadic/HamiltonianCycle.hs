module HamiltonianCycle (gameName, R, Move, p, epsilons) where

import Set
import AESelections
import J

gameName = "hamiltonian cycle"

-- The game has a graph as a parameter. Any existing vertex can be
-- chosen as the vertex0.

vertices = [1..4]
edges = [ (1,2), (1,3), (2,3), (3,4), (4,1) ]
edge x y = (x, y) `varIsIn` edges || (y, x) `varIsIn` edges

-- A solution is a path.  The moves are the vertices, but each vertex
-- can be played only once.

type Move = Int 
type R = Bool

p :: [Move] -> R
p [] = True
p [x] = True
p (x : xs@(y : ys)) = edge x y  &&  p xs

epsilons :: [[Move] -> J R Move]
epsilons = replicate (length vertices) epsilon ++ [epsilonLast]
  where epsilon played = epsilonSome (vertices `varSetMinus` played)
        epsilonLast played = epsilonSome [head played]
