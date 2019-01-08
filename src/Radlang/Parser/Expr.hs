-- |Parser of abstract syntax tree – deals with code

module Radlang.Parser.Expr(expr) where

import           Control.Monad
import           Control.Monad.Combinators.NonEmpty
import           Data.List.NonEmpty                 (NonEmpty((:|)), cons, toList)
import           Text.Megaparsec                    hiding (sepBy1, some)
import           Text.Megaparsec.Char

import           Prelude                            hiding (lex)

import           Radlang.Parser.General
import           Radlang.Parser.Type
import           Radlang.Types


processAST :: AST -> Expr
processAST = \case
  ASTVal v -> Val v
  ASTLit l -> Lit l
  ASTApplication fun args ->
    foldl1 Application (processAST <$> cons fun args)
  -- ASTLet assgs inWhat ->
    -- let postassg (name, args, ttype, val) = case args of
    --       [] -> (name, ttype, processAST val)
    --       (h:t) -> (name, ttype, processAST $
    --                  ASTLambda (h:|t) val
    --                )
    -- in Let (toList $ postassg <$> assgs) (processAST inWhat)
  -- ASTLambda (a:|rest) val -> case rest of
  --   [] -> Lambda a (processAST val)
  --   h:t -> Lambda a (processAST $ ASTLambda (h:|t) val)
  _ -> error "AST processing not implemented"
  -- ASTIf ((c,t):|rest) els -> case rest of
  --   [] -> If (processAST c) (processAST t) (processAST els)
  --   hd:tl -> If
  --     (processAST c)
  --     (processAST t)
  --     (processAST $ ASTIf (hd:|tl) els)


expr :: Parser Expr
expr = processAST <$> ast


-- |Main AST parser
ast :: Parser AST
ast = try astComplex <|> astSimple


-- |Simple expressions that never require parenthess around them
astSimple :: Parser AST
astSimple = msum
  [ mzero
  , valE
  , constantE
  , paren ast
  ]


-- |More complex expressions that are too big to be allowed in some places without
-- parenthesses, i.e. arguments for functions.
astComplex :: Parser AST
astComplex = msum
  [ mzero
  , lambdaE
  , applicationE
  , letE
  , ifE
  ]


valE :: Parser AST
valE = ASTVal <$> (valName <|> constructorName)


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
  assgs <- sepBy1 assignment (operator "|")
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
constantE = fmap ASTLit $ msum $ fmap try
  [ mzero
  , constInt
  , constString
  ]


constInt :: Parser Literal
constInt = LitInt <$> signed


constString :: Parser Literal
constString = LitString <$> between (symbol "\"") (symbol "\"") (many alphaNumChar)
