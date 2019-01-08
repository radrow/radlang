module Radlang.Parser.Toplevel where

import Data.List.NonEmpty as DLNE
import Control.Monad
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.State
import           Control.Monad.Combinators.NonEmpty
import Text.Megaparsec hiding (sepBy1, some)
import Text.Megaparsec.Char

import qualified Data.Map.Strict as M
import qualified Data.Set.Monad as S

import Radlang.Types
import Radlang.Parser.General
import Radlang.Parser.Type
import Radlang.Parser.Expr
import Radlang.DependencyAnalysis
import Radlang.Typesystem.Typesystem
import Radlang.ClassEnvBuild


data RawProgramPart
  = RPNewType NewType
  | RPTypeAlias TypeAlias
  | RPTypeDecl TypeDecl
  | RPDataDef DataDef
  | RPClassDef ClassDef
  | RPImplDef ImplDef
  deriving (Eq, Show)


data RawProgram = RawProgram
  { rawprgNewTypes :: [NewType]
  , rawprgTypeAliases :: [TypeAlias]
  , rawprgTypeDecls :: [TypeDecl]
  , rawprgDataDefs :: [DataDef]
  , rawprgClassDefs :: [ClassDef]
  , rawprgImplDefs :: [ImplDef]
  }
  deriving (Eq, Show)


groupImplicits :: Program -> Program
groupImplicits p =
  p { prgBindings = flip fmap (prgBindings p) $ \case
        (es, [im]) -> (es, groupBindings im)
        (es, []) -> (es, [])
        _ -> error "Implicits already grouped"
    }


toplevelBindings :: [Either TypeDecl DataDef] -> [BindingGroup]
toplevelBindings = pure . Prelude.foldl ins (M.empty, [M.empty]) where
  ins :: BindingGroup -> Either TypeDecl DataDef -> BindingGroup
  ins (exs, [imps]) tl = case tl of
    Left (TypeDecl n qt) -> case (M.lookup n exs, M.lookup n imps) of
      (Nothing, Nothing) ->
        (M.insert n (quantify (S.toList $ free qt) qt, []) exs, [imps])
      (Nothing, Just alts) -> let
        e = M.insert n (quantify (S.toList $ free qt) qt, alts) exs
        i = M.delete n imps
        in (e, [i])
      (Just _, _) -> error "Typedecl duplicate"
    Right (DataDef n args body) -> case (M.lookup n exs, M.lookup n imps) of
      (Nothing, Nothing) -> let
        i = M.insert n [(args, body)] imps
        in (exs, [i])
      (Just (t, alts), Nothing) -> let
        e = M.insert n (t, (args, body):alts) exs
        in (e, [imps])
      (Nothing, Just alts) -> let
        i = M.insert n ((args, body):alts) imps
        in (exs, [i])
      _ -> error "Impossible happened: binding both explicit and implicit"
  ins _ _ = error "toplevelBindings process error: imps not a singleton"


processProgram :: RawProgram -> Either ErrMsg Program
processProgram (RawProgram newtypes typealiases typedecls datadefs classdefs impldefs) = do
  ce <- buildClassEnv classdefs impldefs
  pure $ Program
    { prgBindings = toplevelBindings $ fmap Left typedecls ++ fmap Right datadefs
    , prgTypespace = undefined
    , prgClassEnv = ce
    , prgTypeEnv = undefined
    }


program :: Parser (Either ErrMsg Program)
program = processProgram <$> rawProgram


rawProgram :: Parser RawProgram
rawProgram = do
  parts <- many $ rawProgramPart <* (operator ";;")
  pure $ foldl insertPart (RawProgram [] [] [] [] [] []) parts where
    insertPart rp = \case
      RPNewType nt -> rp {rawprgNewTypes = nt : rawprgNewTypes rp}
      RPTypeAlias ta -> rp {rawprgTypeAliases = ta : rawprgTypeAliases rp}
      RPTypeDecl td -> rp {rawprgTypeDecls = td : rawprgTypeDecls rp}
      RPDataDef dd -> rp {rawprgDataDefs = dd : rawprgDataDefs rp}
      RPClassDef cd -> rp {rawprgClassDefs = cd : rawprgClassDefs rp}
      RPImplDef imd -> rp {rawprgImplDefs = imd : rawprgImplDefs rp}

rawProgramPart :: Parser RawProgramPart
rawProgramPart = msum
  [ RPNewType <$> newType
  , RPTypeAlias <$> typeAlias
  , RPTypeDecl <$> typeDecl
  , RPDataDef <$> dataDef
  , RPClassDef <$> classDef
  , RPImplDef <$> implDef
  ]

newType :: Parser NewType
newType = do
  word "newtype"
  name <- typeName
  typeParams <- many generalTypeName
  operator ":="
  constructors <- sepBy constructorDef (operator "|")
  pure $ NewType name typeParams constructors

constructorDef :: Parser ConstructorDef
constructorDef = do
  name <- constructorName
  params <- many type_
  pure $ ConstructorDef name params

typeAlias :: Parser TypeAlias
typeAlias = do
  word "type"
  word "alias"
  newname <- typeName
  operator ":="
  oldname <- type_
  pure $ TypeAlias newname oldname

typeDecl :: Parser TypeDecl
typeDecl = try $ do
  name <- valName
  operator ":"
  t <- qual type_
  pure $ TypeDecl name t

dataDef :: Parser DataDef
dataDef = try $ do
  name <- valName
  pats <- many pattern
  operator ":="
  def <- expr
  pure $ DataDef name pats def

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
  c <- anyChar
  if c /= '\\'
    then pure c
    else anyChar >>= \case
    'n' -> pure '\n'
    't' -> pure '\t'
    '\\' -> pure '\\'
    'r' -> pure '\r'
    'v' -> pure '\v'
    'b' -> pure '\b'
    'f' -> pure '\f'
    '0' -> pure '\0'
    bad -> fail $ "Cannot escape char '" <> [bad] <> "'"


classDef :: Parser ClassDef
classDef = do
  word "interface"
  name <- className
  arg <- generalTypeName
  sups <- do
    s <- optional $ word "implies" *> (DLNE.toList <$> sepBy1 className (operator ","))
    pure $ maybe S.empty S.fromList s
  methods <- brac $ many $ typeDecl <* (operator ";;")
  pure $ ClassDef name arg sups methods


implDef :: Parser ImplDef
implDef = do
  word "impl"
  arg <- qual type_
  word "for"
  cname <- className
  methods <- brac $ many (dataDef <* (operator ";;"))
  pure $ ImplDef cname arg methods
