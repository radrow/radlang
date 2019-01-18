module Radlang.Parser.Toplevel where

import Data.List.NonEmpty as DLNE
import Control.Monad
import           Control.Monad.Combinators.NonEmpty
import Text.Megaparsec hiding (sepBy1, some)
import Text.Megaparsec.Char

import qualified Data.Set as S

import Radlang.Types hiding(kind)
import Radlang.Parser.General
import Radlang.Parser.Type
-- import Radlang.ClassEnvBuild



rawProgram :: Parser RawProgram
rawProgram = do
  parts <- many $ rawProgramPart <* (operator ";;")
  pure $ foldl insertPart (RawProgram [] [] [] [] []) parts where
    insertPart rp = \case
      RPNewType nt -> rp {rawprgNewTypes = nt : rawprgNewTypes rp}
      RPTypeDecl td -> rp {rawprgTypeDecls = td : rawprgTypeDecls rp}
      RPDataDef dd -> rp {rawprgDataDefs = dd : rawprgDataDefs rp}
      RPClassDef cd -> rp {rawprgClassDefs = cd : rawprgClassDefs rp}
      RPImplDef imd -> rp {rawprgImplDefs = imd : rawprgImplDefs rp}

rawProgramPart :: Parser RawProgramPart
rawProgramPart = msum
  [ RPNewType <$> newType
  , RPTypeDecl <$> typeDecl
  , RPDataDef <$> dataDef
  , RPClassDef <$> classDef
  , RPImplDef <$> implDef
  ]

newType :: Parser RawNewType
newType = do
  word "newtype"
  name <- typeName
  typeParams <- many . paren $ do
    tn <- generalTypeName
    operator ":"
    k <- kind
    pure (tn, k)
  operator ":="
  constructors <- sepBy constructorDef (operator "|")
  pure $ RawNewType name typeParams constructors

constructorDef :: Parser RawConstructorDef
constructorDef = do
  name <- constructorName
  params <- many typeSimple
  pure $ RawConstructorDef name params


typeDecl :: Parser RawTypeDecl
typeDecl = try $ do
  name <- valName
  operator ":"
  t <- qual type_
  pure $ RawTypeDecl name t

dataDef :: Parser RawDataDef
dataDef = try $ do
  name <- valName
  pats <- many pattern
  operator ":="
  def <- expr
  pure $ RawDataDef name pats def

pattern :: Parser Pattern
pattern = msum $ fmap try
  [ PLit <$> literal
  , pure PWildcard <* operator "_"
  , PAs <$> valName <*> (char '@' >> brac pattern)
  , PVar <$> valName
  --, PNPlusK
  , PConstructor <$> constructorName <*> many pattern
  , paren pattern
  ]

literal :: Parser Literal
literal = msum $ fmap try
  [ LitInt <$> signed
  , LitString <$> between
    (symbol "\"") (symbol "\"") (many escapedChar)
  ]

escapedChar :: Parser Char
escapedChar = do
  c <- printChar
  if c /= '\\'
    then pure c
    else printChar >>= \case
    'n' -> pure '\n'
    't' -> pure '\t'
    '\\' -> pure '\\'
    'r' -> pure '\r'
    'v' -> pure '\v'
    'b' -> pure '\b'
    'f' -> pure '\f'
    '0' -> pure '\0'
    bad -> fail $ "Cannot escape char '" <> [bad] <> "'"


classDef :: Parser RawClassDef
classDef = do
  try $ word "interface"
  name <- className
  (arg, knd) <- paren $ do
    liftM2 (,) (generalTypeName <* operator ":") kind
  sups <- do
    s <- optional $ word "implies" *> (DLNE.toList <$> sepBy1 className (operator ","))
    pure $ maybe S.empty S.fromList s
  methods <- brac $ many $ typeDecl <* (operator ";;")
  pure $ RawClassDef name arg knd sups methods


implDef :: Parser RawImplDef
implDef = do
  try $ word "impl"
  arg <- qual type_
  word "for"
  cname <- className
  methods <- brac $ many (dataDef <* (operator ";;"))
  pure $ RawImplDef cname arg methods


-- |Main RawExpr parser
expr :: Parser RawExpr
expr = try exprComplex <|> exprSimple


-- |Simple expressions that never require parenthess around them
exprSimple :: Parser RawExpr
exprSimple = msum
  [ mzero
  , valE
  , litE
  , paren expr
  ]


-- |More complex expressions that are too big to be allowed in some places without
-- parenthesses, i.e. arguments for functions.
exprComplex :: Parser RawExpr
exprComplex = msum
  [ mzero
  , lambdaE
  , letE
  , ifE
  , caseE
  , applicationE
  ]


valE :: Parser RawExpr
valE = RawExprVal <$> (valName <|> constructorName)


lambdaE :: Parser RawExpr
lambdaE = do
  operator "\\"
  arg <- some pattern
  operator "->"
  ex <- expr
  pure $ RawExprLambda arg ex


applicationE :: Parser RawExpr
applicationE = do
  fun <- try exprSimple
  chain <- some $ try exprSimple
  pure $ RawExprApplication fun chain


letE :: Parser RawExpr
letE = do
  word "let"
  assgs <- sepBy1 assignment (operator "|")
  word "in"
  inWhat <- expr
  pure $ RawExprLet assgs inWhat


assignment :: Parser (Either RawTypeDecl RawDataDef)
assignment =
  Left <$> typeDecl <|> Right <$> dataDef


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


litE :: Parser RawExpr
litE = fmap RawExprLit $ msum $ fmap try
  [ mzero
  , constInt
  , constString
  ]


constInt :: Parser Literal
constInt = LitInt <$> signed


constString :: Parser Literal
constString = LitString <$> between (symbol "\"") (symbol "\"") (many alphaNumChar)


caseE :: Parser RawExpr
caseE = do
  word "match"
  e <- expr
  word "with"
  matches <- some $ do
    operator "|"
    p <- pattern
    operator "->"
    em <- expr
    pure (p, em)
  pure $ RawExprCase e matches
