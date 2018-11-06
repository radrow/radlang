module Radlang.Parser.Type where

import           Control.Monad
import           Text.Megaparsec
import qualified Data.Set.Monad as S

import           Prelude                hiding (lex)

import           Radlang.Parser.General
import           Radlang.Types


type_ :: Parser Type
type_ = msum $
  [ mzero
  , try funcT
  , boolT
  , intT
  , valT
  , paren type_
  ]

notFunc :: Parser Type
notFunc = msum $
  [ mzero
  , boolT
  , intT
  , valT
  , paren type_
  ]

intT = word "Int" >> pure TypeInt
boolT = word "Bool" >> pure TypeBool
funcT = do
  from <- notFunc
  operator ("->")
  to <- type_
  pure $ TypeFunc from to
valT = TypeVal <$> generalTypeName
