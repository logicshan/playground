module Game15 (gameName, R, Move, p, epsilons) where

import Set
import AESelections

gameName = "15"

-- Play the moves [1..9] so that all columns, rows, and diagonals add
-- up to 15:
--
--                                    012
--                                    345
--                                    678

type Move = Int

type R = Bool

p :: [Move] -> R
p ms = every [[0,1,2],[3,4,5],[6,7,8],[0,3,6],[1,4,7],[2,5,8],[0,4,8],[2,4,6]]
         (\indices -> sum [ms !! i | i <- indices] == 15)

-- another game: (\indices -> sum [ms !! i | i <- indices] `mod` 5 == 0)

epsilons :: [[Move] -> (Move -> R) -> Move]
epsilons = replicate 9 epsilon
    where epsilon played = epsilonSome ([1..9] `setMinus` played) 
