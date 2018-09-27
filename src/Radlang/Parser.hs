module Radlang.Parser where

import Control.Monad
import Control.Monad.Identity
import Data.Void
import Text.Megaparsec
import Text.Megaparsec.Char
import Text.Megaparsec.Error
import qualified Text.Megaparsec.Char.Lexer as L

import Prelude hiding (lex)

import Radlang.Types
import Data.Either

type Parser = ParsecT Void String Identity

parseProgram :: FilePath -> String -> Either ErrMsg Program
parseProgram = undefined

-- print = putStrLn . either parseErrorPretty show
parseExpr = parse expr "test"
pex = fromRight (Val "None") . parseExpr

forbiddenIds :: [Name]
forbiddenIds = ["let", "in"]

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


funArg = lId
valName = lId


expr :: Parser Expr
expr = msum $ map try
  [ mzero
  , applicationE
  , constantE
  , lambdaE
  , letE
  , valE
  , paren expr
  ]

valE :: Parser Expr
valE = Val <$> valName

constantE :: Parser Expr
constantE = Data <$> msum
  [ constInt
  , constBool
  ]

constInt :: Parser Data
constInt = DataInt <$> signed

constBool :: Parser Data
constBool = fmap DataBool $
  (word "True" >> return True) <|> (word "False" >> return False)

lambdaE :: Parser Expr
lambdaE = do
  operator "\\"
  arg <- funArg
  operator "->"
  ex <- expr
  return $ Lambda arg ex

applicationE :: Parser Expr
applicationE = do
  chain <- some (valE <|> constantE <|> paren expr)
  return $ foldl1 Application chain

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
