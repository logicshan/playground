module NQueens (gameName, R, Move, p, epsilons) where

import Set
import AESelections
import J

gameName = "n-Queens"

n = 8

-- A solution is a permutation of [0..(n-1)]
-- A move is an element of [0..(n-1)]

type Move = Int 
type Position = (Move, Move)
type R = Bool

attacks :: Position -> Position -> Bool
attacks (x, y) (a, b) = x == a  ||  y == b  ||  abs(x - a) == abs(y - b)

valid :: [Position] -> Bool
valid [] = True
valid (u : vs) =  not(some vs (\v -> attacks u v)) && valid vs


p :: [Move] -> R
p ms = valid (zip ms [0..(n-1)])

epsilons :: [[Move] -> J R Move]
epsilons = replicate n epsilon
  where epsilon played = epsilonSome ([0..(n-1)] `setMinus` played)
