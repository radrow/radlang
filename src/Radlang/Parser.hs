-- |Reexport of parsing modules

module Radlang.Parser ( module Radlang.Parser.Toplevel
                      , parseProgram
                      , fullProgram
                      ) where

import Data.Bifunctor
import Text.Megaparsec
import Text.Megaparsec.Char

import Radlang.Parser.Toplevel
import Radlang.Parser.General
import Radlang.Types

fullProgram :: Parser RawProgram
fullProgram = (skipMany controlChar *> rawProgram <* eof)

parseProgram :: String -> String -> Either ErrMsg RawProgram
parseProgram file inp = first (ParseError . concat . fmap parseErrorPretty . bundleErrors) $
  parse fullProgram file inp
