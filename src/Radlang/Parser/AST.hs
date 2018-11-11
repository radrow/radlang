module Radlang.Parser.AST where

import           Control.Monad
import           Control.Monad.Combinators.NonEmpty
import           Data.List.NonEmpty                 ()
import           Text.Megaparsec                    hiding (sepBy1, some)

import           Prelude                            hiding (lex)

import           Radlang.Parser.General
import           Radlang.Parser.Type
import           Radlang.Types

ast :: Parser AST
ast = try applicationE <|> astNonApp

astNonApp :: Parser AST
astNonApp = msum $ fmap try
  [ mzero
  , lambdaE
  , letE
  , ifE
  , constantE
  , valE
  , paren ast
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
  fun <- astNonApp
  chain <- some astNonApp
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
  word "if"
  ifthens <- some $ do
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
