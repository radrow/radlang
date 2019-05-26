-- |Types-related parsing
{-# LANGUAGE FlexibleContexts #-}
module Radlang.Parser.Type where

import           Control.Monad
import           Control.Monad.Combinators.NonEmpty
import           Text.Megaparsec                    hiding (some)

import           Prelude                            hiding (lex)

import           Radlang.Parser.General
import           Radlang.Types                      hiding (kind)


-- |Wrap parser with predicate qualification
qual :: Parser a -> Parser (RawQual a)
qual aPars = do
  preds <- try $ sepBy predicate (operator ",")
  when (not (Prelude.null preds)) $ operator "|"
  a <- aPars
  pure $ RawQual preds a

-- |Parse predicate
predicate :: Parser RawPred
predicate = do
  t <- try $ type_ <* word "is"
  cl <- className
  pure $ RawPred cl t

-- |Parse type expression
type_ :: Parser RawType
type_ = typeComplex <|> typeSimple


-- |Parse complex type expression, that may require to be surrounded by braces in some cases
typeComplex :: Parser RawType
typeComplex = typeFunc <|> typeApp


-- |Parse named type variable
typeVar :: Parser RawType
typeVar = typeVarWobbly <|> typeVarRigid


-- |Parse rigid type variable
typeVarRigid :: Parser RawType
typeVarRigid = RawTypeRigid <$> typeName


-- |Parse replecable type variable
typeVarWobbly :: Parser RawType
typeVarWobbly = RawTypeWobbly <$> generalTypeName


-- |Parse simple type expression that won't collide with neighbors
typeSimple :: Parser RawType
typeSimple = msum
  [ mzero
  , typeVar
  , paren type_
  ]


-- |Syntactic sugar for functional type
typeFunc :: Parser RawType
typeFunc = do
  f <- try $ (typeApp <|> typeSimple) <* operator "->"
  arg <- type_
  pure $ RawTypeFunc f arg


-- |Parse type application
typeApp :: Parser RawType
typeApp = try $ do
  tfun <- typeSimple
  args <- some typeSimple
  pure $ RawTypeApp tfun args


-- |Parse kind expression
kind :: Parser Kind
kind = let kfun = do
             f <- try $ ksimple <* operator "->"
             arg <- kind
             pure $ KFunc f arg
           ksimple = paren kind <|> (word "Type" *> pure KType)
  in kfun <|> ksimple
