-- |Parsers collection used by other parsing modules

module Radlang.Parser.General where

import           Control.Applicative        (liftA2)
import           Control.Monad
import           Control.Monad.Identity
import           Data.Void
import           Data.Text as T
import           Data.List as DL
import           Text.Megaparsec
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import           Prelude                    hiding (lex)

import           Radlang.Types


-- |Main parser monad
type Parser = ParsecT Void String Identity


-- |List of ids that cannot be used as variable names
forbiddenIds :: [String]
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
word w = lex $ try $ string w >> notFollowedBy alphaNumChar >> skipComments


-- |Specific operator
operator :: String -> Parser ()
operator o = lex $ try $ string o >> notFollowedBy (oneOf ("=+_-*&^%$#@![]{}':\\;\".,<\'>" :: String)) >> skipComments


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
lId :: Parser String
lId = lex $ do
  i <- (:) <$> lowerChar <*> (many alphaNumChar)
  when (i `elem` forbiddenIds) $ fail ("forbidden identifier: " <> i)
  return $ i


-- |Identifier starting with upper-case character
uId :: Parser String
uId = lex $ do
  i <- (:) <$> upperChar <*> (many alphaNumChar)
  when (i `elem` forbiddenIds) $ fail ("forbidden identifier: " <> i)
  return $ i


-- Some aliasses
funArg :: Parser Name
funArg = T.pack <$> lId
valName :: Parser Name
valName = T.pack <$> lId
constructorName :: Parser Name
constructorName = T.pack <$> uId
typeName :: Parser Name
typeName = T.pack <$> uId
className :: Parser Name
className = T.pack <$> uId
interfaceName :: Parser Name
interfaceName = T.pack <$> uId
generalTypeName :: Parser Name
generalTypeName = T.pack <$> liftA2 (:) (char '~') uId
