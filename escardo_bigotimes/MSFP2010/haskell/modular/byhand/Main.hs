module Main (main) where

import Play

main :: IO ()
main = putStr ("An optimal play for " ++ gameName ++ " is "
             ++ show optimalPlay
             ++ "\nand the optimal outcome is " ++ show optimalOutcome ++ "\n")
