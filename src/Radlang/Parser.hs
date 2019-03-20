-- |Reexport of parsing modules

module Radlang.Parser ( module Radlang.Parser.Toplevel
                      , parseProgram
                      , parseRDL
                      ) where

import Data.Bifunctor
import Text.Megaparsec
import Text.Megaparsec.Char

import Radlang.Parser.Toplevel
import Radlang.Parser.General
import Radlang.Types

parseProgram :: Parser RawProgram
parseProgram = (skipMany controlChar *> rawProgram <* eof)

parseRDL :: String -> String -> Either ErrMsg RawProgram
parseRDL file inp = first (ParseError . concat . fmap parseErrorPretty . bundleErrors) $
  parse parseProgram file inp
