module EulerianPath (gameName, R, Move, p, epsilons) where

import Set
import AESelections
import J

gameName = "eulerian path"

-- The game has a graph as a parameter.

edges = edges' ++ edges''
 where edges' = [ (1,2), (1,5), (2,3), (2,5), (3,4), (4,6) ]
       edges'' = map (\(x, y) -> (y, x)) edges'

-- The moves are the edges, and each edge has to be played exactly
-- once.

type Move = (Int, Int)
type R = Bool

p :: [Move] -> R
p [] = True
p [(x,y)] = True
p ((x0,y0) : ms@((x1, y1) : ns)) = y0 == x1  &&  p ms

epsilons :: [[Move] -> J R Move]
epsilons = replicate (length edges) epsilon
  where epsilon played = epsilonSome (edges `varSetMinus` played)
