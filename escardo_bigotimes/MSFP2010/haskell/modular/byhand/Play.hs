module Play (gameName, optimalPlay, optimalOutcome, optimalStrategy) where

import DependentBigotimes

-- Choose one of the following games:

import TicTacToe         -- Option 1
-- import NQueens           -- Option 2
-- import SortGame          -- Option 3
-- import ReachabilityGame  -- Option 4
-- import HamiltonianPath   -- Option 5
---import HamiltonianCycle  -- Option 6
-- import ShortestPath      -- Option 7
-- import EulerianPath      -- Option 8
-- import ExactCover        -- Option 9
-- import ExactHittingSet   -- Option 10
-- import Game15            -- Option 11

optimalPlay :: [Move]
optimalPlay = bigotimes epsilons p

optimalOutcome :: R
optimalOutcome = p optimalPlay

optimalStrategy :: [Move] -> Move
optimalStrategy as = head(bigotimes epsilons' p')
   where epsilons' = drop (length as) epsilons
         p' xs = p(as ++ xs)
