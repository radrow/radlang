module Radlang.Parser.Toplevel where

import Control.Monad
import Control.Monad.Except
import Control.Monad.State
import Text.Megaparsec
import Text.Megaparsec.Char

import qualified Data.Map.Strict as M
import qualified Data.Set.Monad as S

import Radlang.Types
import Radlang.Parser.General
import Radlang.Parser.Type
import Radlang.Parser.Expr
import Radlang.Parser.AST
import Radlang.TypecheckerDebug
import Radlang.DependencyAnalysis


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
  ins _ _ = error "ins not implemented for this case"


processProgram :: RawProgram -> Program
processProgram (RawProgram newtypes typealiases typedecls datadefs) =
  Program (toplevelBindings $ fmap Left typedecls ++ fmap Right datadefs)
  typealiases newtypes


data Program = Program
  { prgBindings :: [BindingGroup]
  , prgTypeAliases :: [TypeAlias]
  , prgNewTypes :: [NewType]
  } deriving (Eq, Show)

data RawProgramPart
  = RPNewType NewType
  | RPTypeAlias TypeAlias
  | RPTypeDecl TypeDecl
  | RPDataDef DataDef
  deriving (Eq, Show)

data RawProgram = RawProgram
  { rawprgNewTypes :: [NewType]
  , rawprgTypeAliases :: [TypeAlias]
  , rawprgTypeDecls :: [TypeDecl]
  , rawprgDataDefs :: [DataDef]
  }
  deriving (Eq, Show)

data NewType = NewType Name [Name] [ConstructorDef]
  deriving (Eq, Ord, Show)

data ConstructorDef = ConstructorDef Name [Type]
  deriving (Eq, Ord, Show)

data TypeAlias = TypeAlias Name Type
  deriving (Eq, Ord, Show)

data TypeDecl = TypeDecl Name (Qual Type)
  deriving (Eq, Ord, Show)

data DataDef = DataDef Name [Pattern] Expr
  deriving (Eq, Show)

program :: Parser Program
program = processProgram <$> rawProgram

rawProgram :: Parser RawProgram
rawProgram = do
  parts <- many $ rawProgramPart <* (operator ";;")
  pure $ foldl insert (RawProgram [] [] [] []) parts where
    insert rp = \case
      RPNewType nt -> rp {rawprgNewTypes = nt : rawprgNewTypes rp}
      RPTypeAlias ta -> rp {rawprgTypeAliases = ta : rawprgTypeAliases rp}
      RPTypeDecl td -> rp {rawprgTypeDecls = td : rawprgTypeDecls rp}
      RPDataDef dd -> rp {rawprgDataDefs = dd : rawprgDataDefs rp}

rawProgramPart = msum $ fmap try
  [ RPNewType <$> newType
  , RPTypeAlias <$> typeAlias
  , RPTypeDecl <$> typeDecl
  , RPDataDef <$> dataDef
  ]

newType = do
  word "newtype"
  name <- typeName
  typeParams <- many generalTypeName
  operator ":="
  constructors <- sepBy1 constructorDef (operator "|")
  pure $ NewType name typeParams constructors

constructorDef = do
  name <- constructorName
  params <- many type_
  pure $ ConstructorDef name params

typeAlias = do
  word "type"
  word "alias"
  newname <- typeName
  operator ":="
  oldname <- type_
  pure $ TypeAlias newname oldname

typeDecl = do
  name <- valName
  operator ":"
  t <- qual type_
  pure $ TypeDecl name t

dataDef = do
  name <- valName
  pats <- many pattern
  operator ":="
  def <- processAST <$> ast
  pure $ DataDef name pats def

pattern = msum $ fmap try
  [ PLit <$> literal
  , pure PWildcard <* operator "_"
  , PAs <$> valName <*> (char '@' >> brac pattern)
  , PVar <$> valName
  --, PNPlusK
  , PConstructor <$> constructorName <*> many pattern
  , brac pattern
  ]

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

-- tt :: IO ()
tt = runTypecheckerT $ execTypeInfer $ void . inferTypeExpr $
  Application (Application (Val "eq") (Lit $ LitString "")) (Lit $ LitInt 3)

test :: IO ()
test = do
  f <- readFile "examples/toplevel.rdl"
  case parse (program <* eof) "XD" f of
    Left a -> putStrLn $ parseErrorPretty a
    Right p -> (either id printTypeEnv <$> typecheck (prgBindings p)) >>= putStrLn


printTypeEnv :: TypeEnv -> String
printTypeEnv (TypeEnv te) =
  let l :: [(String, TypePoly)]
      l = M.toList te
  in
  unlines $ fmap (\(v, t) -> v <> " : " <> show t) l

{-
toplevelBindings :: [Toplevel] -> BindingGroup
toplevelBindings = Prelude.foldl ins (M.empty, [M.empty]) where
  ins :: BindingGroup -> Toplevel -> BindingGroup
  ins (exs, [imps]) tl = case tl of
    TopTypeDecl n qt -> case (M.lookup n exs, M.lookup n imps) of
      (Nothing, Nothing) ->
        (M.insert n (quantify (S.toList $ free qt) qt, []) exs, [imps])
      (Nothing, Just alts) -> let
        e = M.insert n (quantify (S.toList $ free qt) qt, alts) exs
        i = M.delete n imps
        in (e, [i])
      (Just _, _) -> error "Typedecl duplicate"
    TopValDef n args body -> case (M.lookup n exs, M.lookup n imps) of
      (Nothing, Nothing) -> let
        i = M.insert n [(args, processAST body)] imps
        in (exs, [i])
      (Just (t, alts), Nothing) -> let
        e = M.insert n (t, (args, processAST body):alts) exs
        in (e, [imps])
      (Nothing, Just alts) -> let
        i = M.insert n ((args, processAST body):alts) imps
        in (exs, [i])
      _ -> error "Impossible happened: binding both explicit and implicit"
  ins _ _ = error "ins not implemented for this case"

data Toplevel
  = TopTypeDecl Name (Qual Type)
  | TopValDef Name [Pattern] AST
  deriving (Eq, Show)

program :: Parser [Toplevel]
program =
  sepBy (msum $ fmap try [typeDecl, valDef]) (operator ";;")

typeDecl :: Parser Toplevel
typeDecl = do
  n <- lId
  operator ":"
  t <- qual type_
  pure $ TopTypeDecl n t

qual :: Parser a -> Parser (Qual a)
qual aPars = do
  preds <- sepBy (try predicate) (operator ",")
  when (not (Prelude.null preds)) $ operator ":-"
  a <- aPars
  pure $ preds :=> a

predicate :: Parser Pred
predicate = do
  t <- type_
  word "is"
  cl <- uId
  pure $ IsIn cl t

valDef :: Parser Toplevel
valDef = do
  n <- lId
  args <- many pattern
  operator ":="
  body <- ast
  pure $ TopValDef n args body


pattern :: Parser Pattern
pattern = msum $ fmap try
  [ mzero
  , val
  , wildcard
  , as
  , literalPattern
  -- , nplusk
  , constructor
  ]

val :: Parser Pattern
val = PVar <$> lId

wildcard :: Parser Pattern
wildcard = operator "_" >> pure PWildcard

as :: Parser Pattern
as = do
  n <- lId
  operator "="
  p <- pattern
  pure $ PAs n p

literalPattern :: Parser Pattern
literalPattern = msum $ fmap try
  [ PLit . LitInt <$> signed
  , PLit . LitString <$>
      between (symbol "\"") (symbol "\"") (many alphaNumChar)
  ]

constructor :: Parser Pattern
constructor = do
  cname <- constructorName
  args <- many pattern
  pure $ PConstructor cname args

-}
