module Radlang.Parser where

import           Control.Monad
import           Control.Monad.Identity
import           Data.Void
import           Text.Megaparsec
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import           Prelude                    hiding (lex)

import           Radlang.Types

--shit

type Parser = ParsecT Void String Identity

forbiddenIds :: [Name]
forbiddenIds = ["let", "in", "case", "of", "if", "else", "then"]

skipComments :: Parser ()
skipComments = L.space
  (void spaceChar)
  (L.skipLineComment "--")
  (L.skipBlockComment "{-" "-}")

lex :: Parser a -> Parser a
lex = L.lexeme skipComments

symbol :: String -> Parser String
symbol = L.symbol skipComments

signed :: (Integral i) => Parser i
signed = L.signed skipComments (lex L.decimal)

word :: String -> Parser ()
word w = try $ string w >> notFollowedBy alphaNumChar >> skipComments

operator :: String -> Parser ()
operator o = try $ string o >> notFollowedBy (oneOf "=+_-)(*&^%$#@![]{}':;\\\".,<>") >> skipComments

paren :: Parser a -> Parser a
paren = between (symbol "(") (symbol ")")

brac :: Parser a -> Parser a
brac = between (symbol "{") (symbol "}")

lId :: Parser Name
lId = lex $ do
  c <- lowerChar
  rest <- many alphaNumChar
  let i = c : rest
  when (i `elem` forbiddenIds) $ fail ("forbidden identifier: " <> i)
  return $ i

uId :: Parser Name
uId = lex $ do
  c <- upperChar
  rest <- many alphaNumChar
  let i = c : rest
  when (i `elem` forbiddenIds) $ fail ("forbidden identifier: " <> i)
  return $ i


funArg :: Parser Name
funArg = lId
valName :: Parser Name
valName = lId
constructorName :: Parser Name
constructorName = uId
typeName :: Parser Name
typeName = uId

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

constantE :: Parser Expr
constantE = Data <$> constant

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
  operator ":="
  value <- expr
  return (name, Nothing, value)

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
  word "else"
  e <- expr
  pure $ If c t e

caseMatch :: Parser (Expr, Expr)
caseMatch = do
  s <- (constructorE <|> constantE <|> valE)
  operator "->"
  e <- expr
  return (s, e)

constant :: Parser Data
constant = msum $ map try
  [ mzero
  , dataInt
  ]

dataInt :: Parser Data
dataInt = DataInt <$> signed
