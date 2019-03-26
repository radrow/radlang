-- |Parsers collection used by other parsing modules

module Radlang.Parser.General where

import           Control.Applicative        (liftA2)
import           Control.Monad
import           Control.Monad.Identity
import           Data.Void
import           Text.Megaparsec
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import           Prelude                    hiding (lex)

import           Radlang.Types


-- |Main parser monad
type Parser = ParsecT Void String Identity


-- |List of ids that cannot be used as variable names
forbiddenIds :: [Name]
forbiddenIds = ["let", "in", "match", "with", "if", "else", "then", "for"]


-- |Comments skip
skipComments :: Parser ()
skipComments = L.space
  (void spaceChar)
  (L.skipLineComment "--")
  (L.skipBlockComment "{-" "-}")


-- |Lexer definition
lex :: Parser a -> Parser a
lex = L.lexeme skipComments


-- |Any symbol
symbol :: String -> Parser String
symbol = L.symbol skipComments


-- |Signed number
signed :: (Integral i) => Parser i
signed = L.signed skipComments (lex L.decimal)


-- |Specific word
word :: String -> Parser ()
word w = try $ string w >> notFollowedBy alphaNumChar >> skipComments


-- |Specific operator
operator :: String -> Parser ()
operator o = try $ string o >> notFollowedBy (oneOf "=+_-*&^%$#@![]{}':\\;\".,<\'>") >> skipComments


-- |Surround parser with parentheses
paren :: Parser a -> Parser a
paren = between (symbol "(") (symbol ")")


-- |Surround parser with curly brackets
brac :: Parser a -> Parser a
brac = between (symbol "{") (symbol "}")


-- |Surround parser with suqare brackets
sqbrac :: Parser a -> Parser a
sqbrac = between (symbol "[") (symbol "]")


-- |Identifier starting with lower-case character
lId :: Parser Name
lId = lex $ do
  c <- lowerChar
  rest <- many alphaNumChar
  let i = c : rest
  when (i `elem` forbiddenIds) $ fail ("forbidden identifier: " <> i)
  return $ i


-- |Identifier starting with upper-case character
uId :: Parser Name
uId = lex $ do
  c <- upperChar
  rest <- many alphaNumChar
  let i = c : rest
  when (i `elem` forbiddenIds) $ fail ("forbidden identifier: " <> i)
  return $ i


-- Some aliasses
funArg :: Parser Name
funArg = lId
valName :: Parser Name
valName = lId
constructorName :: Parser Name
constructorName = uId
typeName :: Parser Name
typeName = uId
interfaceName :: Parser Name
interfaceName = uId
generalTypeName :: Parser Name
generalTypeName = liftA2 (:) (char '~') uId
