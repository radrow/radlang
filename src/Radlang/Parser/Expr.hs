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


processRawExpr :: RawExpr -> Expr
processRawExpr = \case
  RawExprVal v -> Val v
  RawExprLit l -> Lit l
  RawExprApplication fun args ->
    foldl1 Application (processRawExpr <$> cons fun args)
  -- RawExprLet assgs inWhat ->
    -- let postassg (name, args, ttype, val) = case args of
    --       [] -> (name, ttype, processRawExpr val)
    --       (h:t) -> (name, ttype, processRawExpr $
    --                  RawExprLambda (h:|t) val
    --                )
    -- in Let (toList $ postassg <$> assgs) (processRawExpr inWhat)
  -- RawExprLambda (a:|rest) val -> case rest of
  --   [] -> Lambda a (processRawExpr val)
  --   h:t -> Lambda a (processRawExpr $ RawExprLambda (h:|t) val)
  _ -> error "RawExpr processing not implemented"
  -- RawExprIf ((c,t):|rest) els -> case rest of
  --   [] -> If (processRawExpr c) (processRawExpr t) (processRawExpr els)
  --   hd:tl -> If
  --     (processRawExpr c)
  --     (processRawExpr t)
  --     (processRawExpr $ RawExprIf (hd:|tl) els)


-- |Main RawExpr parser
expr :: Parser RawExpr
expr = try exprComplex <|> exprSimple


-- |Simple expressions that never require parenthess around them
exprSimple :: Parser RawExpr
exprSimple = msum
  [ mzero
  , valE
  , constantE
  , paren expr
  ]


-- |More complex expressions that are too big to be allowed in some places without
-- parenthesses, i.e. arguments for functions.
exprComplex :: Parser RawExpr
exprComplex = msum
  [ mzero
  , lambdaE
  , applicationE
  , letE
  , ifE
  ]


valE :: Parser RawExpr
valE = RawExprVal <$> (valName <|> constructorName)


lambdaE :: Parser RawExpr
lambdaE = do
  operator "\\"
  arg <- some funArg
  operator "->"
  ex <- expr
  pure $ RawExprLambda arg ex


applicationE :: Parser RawExpr
applicationE = do
  fun <- exprSimple
  chain <- some exprSimple
  pure $ RawExprApplication fun chain


letE :: Parser RawExpr
letE = do
  word "let"
  assgs <- sepBy1 assignment (operator "|")
  word "in"
  inWhat <- expr
  pure $ RawExprLet assgs inWhat


assignment :: Parser (Name, [Name], Maybe RawType, RawExpr)
assignment = do
  name <- valName
  args <- many valName
  typeAnn <- optional $ do
    operator ":"
    type_
  operator ":="
  value <- expr
  pure (name, args, typeAnn, value)


ifE :: Parser RawExpr
ifE = do
  ifthens <- some $ do
    word "if"
    c <- expr
    word "then"
    t <- expr
    pure (c, t)
  word "else"
  e <- expr
  pure $ RawExprIf ifthens e


constantE :: Parser RawExpr
constantE = fmap RawExprLit $ msum $ fmap try
  [ mzero
  , constInt
  , constString
  ]


constInt :: Parser Literal
constInt = LitInt <$> signed


constString :: Parser Literal
constString = LitString <$> between (symbol "\"") (symbol "\"") (many alphaNumChar)
