module Radlang
    ( parseProgram
    , module Radlang.Types
    , module Radlang.Evaluator
    , module Radlang.Typechecker
    ) where

import Data.Bifunctor(bimap)
import Text.Megaparsec as MP(parse, parseErrorPretty, eof)

import Radlang.Parser(ast, processAST)
import Radlang.Evaluator
import Radlang.Types
import Radlang.Typechecker

parseProgram :: String -> String -> Either String Expr
parseProgram filename code = bimap parseErrorPretty processAST $ MP.parse (ast <* eof) filename code
