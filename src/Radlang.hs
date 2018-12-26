-- |Purely functional programming language inspired by Haskell and OCaml

module Radlang
    ( parseProgram
    , module Radlang.Types
    , module Radlang.Evaluator
    , module Radlang.TypecheckerDebug
    , module Radlang.Parser
    ) where

import Data.Bifunctor(bimap)
import Text.Megaparsec as MP(parse, parseErrorPretty, eof)

import Radlang.Parser
import Radlang.Evaluator
import Radlang.Types
import Radlang.TypecheckerDebug

-- |Toplevel parser run with desugaring
parseProgram :: String -> String -> Either String Program
parseProgram filename code = bimap parseErrorPretty id $ MP.parse (program <* eof) filename code
