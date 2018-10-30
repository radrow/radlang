module Radlang.Parser.Expr where

import           Control.Monad
import           Text.Megaparsec

import           Prelude                hiding (lex)

import           Radlang.Parser.General
import Radlang.Parser.Type
import           Radlang.Types

expr :: Parser Expr
expr = msum $ map try
  [ mzero
  , applicationE
  , constructorE
  , constantE
  , lambdaE
  , letE
  , caseE
  , valE
  , ifE
  , paren expr
  ]

valE :: Parser Expr
valE = Val <$> valName

lambdaE :: Parser Expr
lambdaE = do
  operator "\\"
  arg <- funArg
  operator "->"
  ex <- expr
  return $ Lambda arg ex

applicationE :: Parser Expr
applicationE = do
  chain <- some $ try (valE <|> constantE <|> paren expr)
  return $ foldl1 Application chain

constructorE :: Parser Expr
constructorE = do
  name <- Val <$> constructorName
  chain <- many $ try (valE <|> constantE <|> paren expr)
  return $ foldl1 Application (name:chain)

letE :: Parser Expr
letE = do
  word "let"
  a <- sepBy1 assignment (operator ";")
  word "in"
  inWhat <- expr
  return $ Let a inWhat

assignment :: Parser (Name, Maybe Type, Expr)
assignment = do
  name <- valName
  typeAnn <- optional $ do
    operator ":"
    type_
  operator ":="
  value <- expr
  pure (name, typeAnn, value)

caseE :: Parser Expr
caseE = do
  word "case"
  e <- expr
  word "of"
  void $ optional $ try $ operator "|"
  cases <- sepBy1 caseMatch (operator "|")
  return $ Case e cases

ifE :: Parser Expr
ifE = do
  word "if"
  c <- expr
  word "then"
  t <- expr
  let
    finito = do
      word "else"
      e <- expr
      pure $ If c t e
    more = do
      mor <- ifE
      pure $ If c t mor
  try finito <|> try more

caseMatch :: Parser (Expr, Expr)
caseMatch = do
  s <- (constructorE <|> constantE <|> valE)
  operator "->"
  e <- expr
  return (s, e)

constantE :: Parser Expr
constantE = msum $ map try
  [ mzero
  , constInt
  , constBool
  ]

constInt :: Parser Expr
constInt = ConstInt <$> signed

constBool :: Parser Expr
constBool = (   try (word "True" >> pure (ConstBool True))
           <|> try (word "False" >> pure (ConstBool False))
           )
