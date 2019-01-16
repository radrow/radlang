-- |Reexport of parsing modules

module Radlang.Parser ( module Radlang.Parser.Expr
                      , module Radlang.Parser.Toplevel
                      , parseProgram
                      ) where

import Data.Bifunctor
import Text.Megaparsec
import Text.Megaparsec.Char

import Radlang.Parser.Expr
import Radlang.Parser.Toplevel
import Radlang.Types

parseProgram :: String -> String -> Either ErrMsg RawProgram
parseProgram file inp = first (ParseError . concat . fmap parseErrorPretty . bundleErrors) $
  parse (skipMany controlChar *> rawProgram <* eof) file inp
