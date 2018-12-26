-- |Types-related parsing

module Radlang.Parser.Type where

import           Control.Monad.Combinators.NonEmpty
import           Data.List.NonEmpty                 (NonEmpty((:|)))
import           Control.Monad
import           Text.Megaparsec hiding (some)

import           Prelude                hiding (lex)

import           Radlang.Parser.General
import           Radlang.Types
import Radlang.Typedefs

data TypeRaw
  = RawTypeWobbly Name
  | RawTypeRigid Name
  | RawTypeApp TypeRaw (NonEmpty TypeRaw)
  | RawTypeFunc TypeRaw TypeRaw
  deriving (Eq, Show)

processRawType :: TypeRaw -> Type
processRawType = \case
  RawTypeWobbly n -> TypeVarWobbly $ TypeVar n KType
  RawTypeRigid n -> TypeVarRigid $ TypeVar n KType
  RawTypeApp tfun (arg1 :| restargs) ->
    foldl TypeApp (processRawType tfun) (processRawType <$> arg1:restargs)
  RawTypeFunc tfun arg -> fun (processRawType tfun) (processRawType arg)

type_ :: Parser Type
type_ = processRawType <$> typeRaw

qual :: Parser a -> Parser (Qual a)
qual aPars = do
  preds <- sepBy (try predicate) (operator ",")
  when (not (Prelude.null preds)) $ operator ":-"
  a <- aPars
  pure $ preds :=> a

predicate :: Parser Pred
predicate = do
  t <- type_
  word "is"
  cl <- uId
  pure $ IsIn cl t

typeRaw :: Parser TypeRaw
typeRaw = typeComplex <|> typeSimple

typeComplex :: Parser TypeRaw
typeComplex = typeFunc <|> typeApp

typeVar :: Parser TypeRaw
typeVar = typeVarWobbly <|> typeVarRigid

typeVarRigid :: Parser TypeRaw
typeVarRigid = RawTypeRigid <$> typeName
typeVarWobbly :: Parser TypeRaw
typeVarWobbly = RawTypeWobbly <$> generalTypeName

typeSimple :: Parser TypeRaw
typeSimple = msum
  [ mzero
  , typeVar
  , paren typeRaw
  ]

typeFunc :: Parser TypeRaw
typeFunc = do
  f <- try $ typeSimple <* operator "->"
  arg <- typeRaw
  pure $ RawTypeFunc f arg

typeApp :: Parser TypeRaw
typeApp = try $ do
  tfun <- typeSimple
  args <- some typeSimple
  pure $ RawTypeApp tfun args

