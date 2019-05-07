module Radlang.Polymorphism where

import Control.Monad.Reader
import Control.Monad.State

import Radlang.Types
import Radlang.Error

detype :: TypedExpr -> Expr
detype = \case
  _ -> undefined
  -- TypedVal
