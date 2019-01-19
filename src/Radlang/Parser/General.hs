-- |Parsers collection used by other parsing modules

module Radlang.Parser.General where

import Control.Applicative (liftA2)
import           Control.Monad
import           Control.Monad.Identity
import           Data.Void
import           Text.Megaparsec
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import           Prelude                    hiding (lex)

import           Radlang.Types


type Parser = ParsecT Void String Identity


forbiddenIds :: [Name]
forbiddenIds = ["let", "in", "match", "with", "if", "else", "then", "for"]

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
className :: Parser Name
className = uId
generalTypeName :: Parser Name
generalTypeName = liftA2 (:) (char '~') uId
