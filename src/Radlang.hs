module Radlang
    ( parseProgram
    , module Radlang.Types
    , module Radlang.Evaluator
    ) where

import Data.Bifunctor(first)
import Text.Megaparsec as MP(parse, parseErrorPretty)

import Radlang.Parser(expr)
import Radlang.Evaluator
import Radlang.Types

parseProgram :: String -> String -> Either String Expr
parseProgram filename code = first parseErrorPretty $ MP.parse expr filename code
