module Radlang.Evaluator where

import Control.Monad.State.Strict
import Data.Map.Strict as M

import Radlang.Types

evalProgram :: Namespace -> Expr -> Data
evalProgram namespace e =
  case e of
    Val a -> case M.lookup a namespace of
      Just x -> x
      Nothing -> error $ "Unbound value: " <> a
    Data d -> d
    Application f arg ->
      case evalProgram namespace f of
        DataLambda ns argname e ->
          evalProgram (M.union namespace
                       (M.insert argname (evalProgram namespace arg) ns)) e
        _ -> error "Application requires lambda"
    Let assgs e -> evalProgram ns e where
      ns = Prelude.foldl (\m (name, _, e) ->
                            M.insert
                            name
                            (evalProgram m e)
                            m
                         ) namespace assgs
    Lambda name e -> DataLambda namespace name e

