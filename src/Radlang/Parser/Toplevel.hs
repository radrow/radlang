module Radlang.Parser.Toplevel where

import           Control.Monad
import           Control.Monad.Combinators.NonEmpty
import           Data.List.NonEmpty                 as DLNE
import           Text.Megaparsec                    hiding (sepBy1, some)
import           Text.Megaparsec.Char

import           Data.Functor
import qualified Data.Set                           as S

import           Radlang.Parser.General
import           Radlang.Parser.Type
import           Radlang.Types                      hiding (kind)


-- |Parse whole program
rawProgram :: Parser RawProgram
rawProgram = do
  skipComments
  parts <- many $ rawProgramPart <* operator ";;"
  pure $ foldl insertPart (RawProgram [] [] [] [] []) parts where
    insertPart rp = \case
      RPNewType nt -> rp {rawprgNewTypes = nt : rawprgNewTypes rp}
      RPTypeDecl td -> rp {rawprgTypeDecls = td : rawprgTypeDecls rp}
      RPDataDef dd -> rp {rawprgDataDefs = dd : rawprgDataDefs rp}
      RPInterfaceDef cd -> rp {rawprgInterfaceDefs = cd : rawprgInterfaceDefs rp}
      RPImplDef imd -> rp {rawprgImplDefs = imd : rawprgImplDefs rp}


-- |Parse single component of a program
rawProgramPart :: Parser RawProgramPart
rawProgramPart = msum
  [ RPNewType <$> newType
  , RPTypeDecl <$> typeDecl
  , RPDataDef <$> dataDef
  , RPInterfaceDef <$> interfaceDef
  , RPImplDef <$> implDef
  ]


-- |Parse definition of new type
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


-- |Parse new type's constructor definition
constructorDef :: Parser RawConstructorDef
constructorDef = do
  name <- constructorName
  params <- many typeSimple
  pure $ RawConstructorDef name params


-- |Parse type declaration
typeDecl :: Parser RawTypeDecl
typeDecl = do
  name <- try $ valName <* operator ":"
  t <- qual type_
  pure $ RawTypeDecl name t


-- |Parse value definition
dataDef :: Parser RawDataDef
dataDef = do
  (name, pats) <- try $ liftM2 (,) valName (many patternSimple <* operator ":=")
  def <- expr
  pure $ RawDataDef name pats def


-- |Parse pattern
pattern :: Parser Pattern
pattern = patternComplex <|> patternSimple


-- |Parse simple pattern that won't collide with neighbors
patternSimple :: Parser Pattern
patternSimple = msum $
  [ PLit <$> literal
  , pure PWildcard <* operator "_"
  , try $ PAs <$> valName <*> (char '@' >> brac pattern)
  , PVar <$> valName
  , flip PConstructor [] <$> constructorName
  , patternList
  , paren pattern
  ]


-- |Parse pattern that may collidie with neighbors and sometimes will need to be surrounded by braces
patternComplex :: Parser Pattern
patternComplex = msum
  [ try $ PConstructor <$> constructorName <*> many pattern
  --, PNPlusK
  ]


-- |Parse list pattern
patternList :: Parser Pattern
patternList = sqbrac $ sepBy pattern (symbol ",") <&>
  Prelude.foldr (\a b -> PConstructor "Cons" [a, b]) (PConstructor "Nil" [])


-- |Parse literal value
literal :: Parser Literal
literal = msum $ fmap try
  [ LitInt <$> signed
  , LitString <$> between (symbol "\"") (symbol "\"") (many escapedChar)
  , LitChar <$> between (symbol "'") (symbol "'") escapedChar
  ]


-- |Parse character with respect to common escaping rules
escapedChar :: Parser Char
escapedChar = do
  c <- try (printChar >>= \cc -> when (cc == '"') mzero >> pure cc)
  if c /= '\\'
    then pure c
    else printChar >>= \case
    'n'  -> pure '\n'
    't'  -> pure '\t'
    '\\' -> pure '\\'
    'r'  -> pure '\r'
    'v'  -> pure '\v'
    'b'  -> pure '\b'
    'f'  -> pure '\f'
    '0'  -> pure '\0'
    bad  -> fail $ "Cannot escape char '" <> [bad] <> "'"


-- |Parse definition of a interface
interfaceDef :: Parser RawInterfaceDef
interfaceDef = do
  try $ word "interface"
  name <- interfaceName
  (arg, knd) <- paren $ do
    liftM2 (,) (generalTypeName <* operator ":") kind
  sups <- do
    s <- optional $ word "implies" *> (DLNE.toList <$> sepBy1 interfaceName (operator ","))
    pure $ maybe S.empty S.fromList s
  methods <- brac $ many $ typeDecl <* (operator ";;")
  pure $ RawInterfaceDef name arg knd sups methods


-- |Parse instance definition
implDef :: Parser RawImplDef
implDef = do
  try $ word "impl"
  arg <- qual type_
  word "for"
  cname <- interfaceName
  methods <- brac $ many (dataDef <* (operator ";;"))
  pure $ RawImplDef cname arg methods


-- |Parse raw language expression
expr :: Parser RawExpr
expr = try exprComplex <|> exprSimple


-- |Parse simple expressions that never require parenthess around them
exprSimple :: Parser RawExpr
exprSimple = msum
  [ mzero
  , valE
  , litE
  , listE
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
  , matchE
  , forE
  , applicationE
  ]


-- |Parse named value or variable
valE :: Parser RawExpr
valE = RawExprVal <$> (valName <|> constructorName)


-- |Parse lambda expression
lambdaE :: Parser RawExpr
lambdaE = do
  operator "\\"
  arg <- some pattern
  operator "->"
  ex <- expr
  pure $ RawExprLambda arg ex


-- |Parse application expression
applicationE :: Parser RawExpr
applicationE = do
  fun <- try exprSimple
  chain <- some $ try exprSimple
  pure $ RawExprApplication fun chain


-- |Parse let expression
letE :: Parser RawExpr
letE = do
  word "let"
  assgs <- sepBy1 assignment (operator "|")
  word "in"
  inWhat <- expr
  pure $ RawExprLet assgs inWhat


-- |Parse single assignmen used in `let` expression
assignment :: Parser (Either RawTypeDecl RawDataDef)
assignment =
  Left <$> typeDecl <|> Right <$> dataDef


-- |Parse `if` expression
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


-- |Parse literal as expression
litE :: Parser RawExpr
litE = RawExprLit <$> literal


-- |Parse pattern match
matchE :: Parser RawExpr
matchE = do
  word "match"
  e <- expr
  word "with"
  matches <- some $ do
    operator "|"
    p <- pattern
    operator "->"
    em <- expr
    pure (p, em)
  pure $ RawExprMatch e matches


-- |Parse for comprehension
forE :: Parser RawExpr
forE = do
  word "for"
  comphrs <- brac $ sepBy (msum
    [ try valName >>= \n -> operator "<-" *> expr >>= \e -> pure (ForBind n e)
    , ForVal <$> expr
    ]) (operator "|")
  e <- expr
  pure $ RawExprFor comphrs e


-- |Parse list expression
listE :: Parser RawExpr
listE = sqbrac $ RawExprList <$> sepBy expr (symbol ",")
