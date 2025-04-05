module SortGame (gameName, R, Move, p, epsilons) where

import Set
import AESelections

gameName = "sort"

-- The game has a parameter, the input to be sorted:

input = reverse [1..18] 

-- A solution is a sorted permutation of the input.  The moves are the
-- elements of the set, but each element can be played only once.

type Move = Int 
type R = Bool

p :: [Move] -> R
p [] = True
p [x] = True
p (x : xs) = x <= head xs && p xs 

epsilons :: [[Move] -> (Move -> R) -> Move]
epsilons = replicate (length input) epsilon
  where epsilon played = epsilonSome (input `varSetMinus` played)

{-- Remark:

There are

  18! = 6.40237371 × 10^15 permutations,

and the last one generated is the solution. If we could check

   10^9 permutations per second, 

it would take 

   20.3 years 

to find it by inspecting one at a time. However,

   our program takes 12.9s

in a 2.1Ghz with ghc 6.10.4 with the compilation option -O2 to find
it. This means that although our program in principle generates all
permutations, lazy evaluation is performing a drastic cut down.

Of course, we are not proposing this algorithm for sorting, but rather
as an illustration of our search method. The crucial fact is that p
forces the evaluation of its whole argument iff it is sorted, but
otherwise it forces the evaluation of the minimal prefix that is
enough to check that it is not sorted.

The list of attempts performed by our program starts like this:

18 (+17 failures)
17 18 (+16 failures)
16 17 18 (+15 failures)
.
.
.
1 18 (+16 failures)
1 17 (+15 failures)
.
.
.
1 2 18 (+15 failures)
1 2 17 18 (+14 failures)
.
.
.
1 2 3 18 (+14 failures)
.
.
.

It should be use to derive a formula to predict the run time, but we
haven't done this yet. But this is certainly much smaller than 18!.


--}