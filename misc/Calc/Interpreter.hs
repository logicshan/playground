module Interpreter where

import AbsCalc

interpret :: Exp -> Integer
interpret x = case x of
  EAdd exp1 exp2 -> interpret exp1 + interpret exp2
  ESub exp1 exp2 -> interpret exp1 - interpret exp2
  EMul exp1 exp2 -> interpret exp1 * interpret exp2
  EDiv exp1 exp2 -> interpret exp1 `div` interpret exp2
  EInt n -> n
