{-# LANGUAGE FlexibleContexts #-}
-- |Types-related parsing

module Radlang.Parser.Type where

import           Control.Monad.Combinators.NonEmpty
import           Data.List.NonEmpty                 (NonEmpty((:|)))
import           Control.Monad
import           Control.Monad.Except
import           Text.Megaparsec hiding (some)

import           Prelude                hiding (lex)

import           Radlang.Parser.General
import           Radlang.Types hiding (kind)
import Radlang.Typedefs
import Radlang.Kindchecker


-- processRawType :: Monad m => RawType -> KindcheckerT m Type
-- processRawType tr = getAssumptions >>= \kas -> case tr of
--   RawTypeWobbly n -> pure $ TypeVarWobbly $ TypeVar n KType
--   RawTypeRigid n -> case lookupKind n kas of
--     Just k -> pure $ TypeVarRigid $ TypeVar n k
--     Nothing -> throwError $ "Unknown rigid type " <> n
--   RawTypeApp tfun (arg1 :| restargs) -> do
--     ttfun <- processRawType tfun
--     foldM (\f a -> TypeApp f <$> (processRawType a)) ttfun (arg1:restargs)
--   RawTypeFunc tfun arg -> liftM2 fun (processRawType tfun) (processRawType arg)


qual :: Parser a -> Parser (RawQual a)
qual aPars = paren (qual aPars) <|> do
  preds <- sepBy (try predicate) (operator ",")
  when (not (Prelude.null preds)) $ operator ":-"
  a <- aPars
  pure $ RawQual preds a

predicate :: Parser RawPred
predicate = do
  t <- type_
  word "is"
  cl <- uId
  pure $ RawPred cl t

type_ :: Parser RawType
type_ = typeComplex <|> typeSimple

typeComplex :: Parser RawType
typeComplex = typeFunc <|> typeApp

typeVar :: Parser RawType
typeVar = typeVarWobbly <|> typeVarRigid

typeVarRigid :: Parser RawType
typeVarRigid = RawTypeRigid <$> typeName
typeVarWobbly :: Parser RawType
typeVarWobbly = RawTypeWobbly <$> generalTypeName

typeSimple :: Parser RawType
typeSimple = msum
  [ mzero
  , typeVar
  , paren type_
  ]

typeFunc :: Parser RawType
typeFunc = do
  f <- try $ typeSimple <* operator "->"
  arg <- type_
  pure $ RawTypeFunc f arg

typeApp :: Parser RawType
typeApp = try $ do
  tfun <- typeSimple
  args <- some typeSimple
  pure $ RawTypeApp tfun args


kindSimple :: Parser Kind
kindSimple = paren kind <|> (word "Type" *> pure KType)

kind :: Parser Kind
kind = let kfun = do
             f <- try $ kindSimple <* operator "->"
             arg <- kind
             pure $ KFunc f arg
  in kfun <|> kindSimple
