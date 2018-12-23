-- |Types-related parsing

module Radlang.Parser.Type(type_) where

import           Control.Monad
import           Text.Megaparsec

import           Prelude                hiding (lex)

import           Radlang.Parser.General
import           Radlang.Types


type_ :: Parser Type
type_ = msum $
  [ mzero
  -- , try funcT
  , valT
  , paren type_
  ]

notFunc :: Parser Type
notFunc = msum $
  [ mzero
  , valT
  , paren type_
  ]

-- funcT :: Parser Type
-- funcT = do
--   from <- notFunc
--   operator ("->")
--   to <- type_
--   pure $ TypeFunc from to

valT :: Parser Type
valT = TypeVarRigid . (\v -> TypeVar v KType) <$> generalTypeName
