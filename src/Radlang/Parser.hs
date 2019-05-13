-- |Reexport of parsing modules
module Radlang.Parser ( module Radlang.Parser.Toplevel
                      , parseProgram
                      , parseRDL
                      ) where

import           Data.Bifunctor
import           Data.Text as T
import           Data.List.NonEmpty (toList)
import           Text.Megaparsec
import           Text.Megaparsec.Char

import           Radlang.Parser.General
import           Radlang.Parser.Toplevel
import           Radlang.Types


-- |Parse whole program file
parseProgram :: Parser RawProgram
parseProgram = (skipMany controlChar *> rawProgram <* eof)


-- |Evaluation of the parser
parseRDL :: String -> String -> Either ErrMsg RawProgram
parseRDL file inp = first (ParseError . T.concat . toList . fmap (T.pack . parseErrorPretty) . bundleErrors) $
  parse parseProgram file inp
