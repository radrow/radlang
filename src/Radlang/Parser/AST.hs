-- |Parser of abstract syntax tree – deals with code

module Radlang.Parser.AST where

import           Control.Monad
import           Control.Monad.Combinators.NonEmpty
import           Data.List.NonEmpty                 ()
import           Text.Megaparsec                    hiding (sepBy1, some)

import           Prelude                            hiding (lex)

import           Radlang.Parser.General
import           Radlang.Parser.Type
import           Radlang.Types

-- |Main AST parser
ast :: Parser AST
ast = astComplex <|> astSimple

-- |Simple expression that usually behave like a single body
astSimple :: Parser AST
astSimple = msum $ fmap try
  [ mzero
  , valE
  , constantE
  , paren ast
  ]
-- |More complex expressions that are too big to be allowed in some places without
-- parenthesses, i.e. arguments for functions.
astComplex :: Parser AST
astComplex = msum $ fmap try
  [ mzero
  , lambdaE
  , applicationE
  , letE
  , ifE
  ]

valE :: Parser AST
valE = ASTVal <$> valName

lambdaE :: Parser AST
lambdaE = do
  operator "\\"
  arg <- some funArg
  operator "->"
  ex <- ast
  pure $ ASTLambda arg ex

applicationE :: Parser AST
applicationE = do
  fun <- astSimple
  chain <- some astSimple
  pure $ ASTApplication fun chain

letE :: Parser AST
letE = do
  word "let"
  assgs <- sepBy1 assignment (operator ";")
  word "in"
  inWhat <- ast
  pure $ ASTLet assgs inWhat

assignment :: Parser (Name, [Name], Maybe Type, AST)
assignment = do
  name <- valName
  args <- many valName
  typeAnn <- optional $ do
    operator ":"
    type_
  operator ":="
  value <- ast
  pure (name, args, typeAnn, value)

ifE :: Parser AST
ifE = do
  ifthens <- some $ do
    word "if"
    c <- ast
    word "then"
    t <- ast
    pure (c, t)
  word "else"
  e <- ast
  pure $ ASTIf ifthens e

constantE :: Parser AST
constantE = msum $ fmap try
  [ mzero
  , constInt
  , constBool
  ]

constInt :: Parser AST
constInt = ASTInt <$> signed

constBool :: Parser AST
constBool = ( try (word "True" >> pure (ASTBool True))
              <|> try (word "False" >> pure (ASTBool False))
            )
