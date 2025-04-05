module ShortestPath (gameName, R, Move, p, epsilons) where

import Set
import InfSupSelections
import J

gameName = "shortest path"

-- We need to deal with infinity

infty = maxBound
addi :: Int -> Int -> Int
addi x y = if x == infty || y == infty then infty else x + y

-- The game has a directed weighted graph as a parameter.

vertices = [1..6]
 
weight 1 2 = 7
weight 1 3 = 9
weight 1 6 = 14
weight 2 1 = 7
weight 2 3 = 10
weight 2 4 = 15
weight 3 1 = 9
weight 3 2 = 10
weight 3 4 = 11
weight 3 6 = 2
weight 4 2 = 15
weight 4 3 = 11
weight 4 5 = 6
weight 5 4 = 6 
weight 5 6 = 9
weight 6 1 = 14
weight 6 3 = 2
weight 6 5 = 9
weight x y = if x == y then 0 else infty

origin = 1
destination = 5

-- Description of the solution:

type Move = Int 
type R = Int


p :: [Move] -> R
p [] = infty
p (x : xs)  = if x == destination 
              then 0
              else if xs == []
                   then infty
                   else addi (weight x (head xs)) (p xs)

epsilons :: [[Move] -> J R Move]
epsilons = epsilonOrigin : replicate (length vertices - 1) epsilon
  where epsilonOrigin [] = epsilonInfZ [origin]
        epsilon played = epsilonInfZ (vertices `setMinus` played)
