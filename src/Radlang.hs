-- |Purely functional programming language inspired by Haskell and OCaml

module Radlang
    ( parseProgram
    , module Radlang.Types
    , module Radlang.Evaluator
    , module Radlang.Typechecker
    , module Radlang.Parser
    ) where

import Data.Bifunctor(bimap)
import Text.Megaparsec as MP(parse, parseErrorPretty, eof)

import Radlang.Parser
import Radlang.Evaluator
import Radlang.Types
import Radlang.Typechecker

-- |Toplevel parser run with desugaring
parseProgram :: String -> String -> Either String Expr
parseProgram filename code = bimap parseErrorPretty processAST $ MP.parse (ast <* eof) filename code
