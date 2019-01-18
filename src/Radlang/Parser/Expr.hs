-- |Parser of abstract syntax tree – deals with code

module Radlang.Parser.Expr where

import           Control.Monad
import           Control.Monad.Combinators.NonEmpty
import           Data.List.NonEmpty                 (NonEmpty((:|)), cons, toList)
import           Text.Megaparsec                    hiding (sepBy1, some)
import           Text.Megaparsec.Char

import           Prelude                            hiding (lex)

import           Radlang.Parser.General
import           Radlang.Parser.Type
import           Radlang.Types


