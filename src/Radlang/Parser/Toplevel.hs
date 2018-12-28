{-#LANGUAGE OverloadedLists #-}

module Radlang.Parser.Toplevel where

import Control.Monad
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.State
import Text.Megaparsec
import Text.Megaparsec.Char

import qualified Data.Map.Strict as M
import qualified Data.Set.Monad as S

import Radlang.Types
import Radlang.Parser.General
import Radlang.Parser.Type
import Radlang.Parser.Expr
import Radlang.DependencyAnalysis
import Radlang.Typechecker


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


processProgram :: RawProgram -> Program
processProgram (RawProgram newtypes typealiases typedecls datadefs classdefs impldefs) =
  Program
  { prgBindings = toplevelBindings $ fmap Left typedecls ++ fmap Right datadefs
  , prgTypespace = undefined
  , prgClassEnv = buildClassEnv classdefs impldefs
  , prgTypeEnv = undefined
  }



-- |Inserts new class to env
updateClassEnv :: Name -> Class -> ClassEnvBuilder ()
updateClassEnv n c = modify $ \ce -> ce {classes = M.insert n c (classes ce)}


-- |Empty class environment
emptyClassEnv :: ClassEnv
emptyClassEnv = ClassEnv
  { classes = []
  , defaults = [] -- TODO: defaults!
  }

-- |Introduces new class extending given superclasses
addClass :: Name -> Set Name -> ClassEnvBuilder ()
addClass n sups = do
  nDefined <- classDefined n
  when nDefined (throwError $ "Class already defined: " <> n)
  notDefs <- mapM (\ss -> not <$> classDefined ss) (S.toList sups)
  when (not (null notDefs)) $
    throwError $ "Superclasses not defined: " <> show notDefs
  updateClassEnv n (Class sups S.empty)


-- |Declares new instance with qualification
addInst :: [Pred] -> Pred -> ClassEnvBuilder ()
addInst ps p@(IsIn i _) = do
  iDefined <- classDefined i
  when (not iDefined) (throwError $ "Class not defined: " <> i)
  its <- instances i
  c <- super i
  let overlaps prd q = catchError (mguPred prd q >> pure True) (const $ pure False)
      qs = fmap (\(_ :=> q) -> q) its
  filterM (overlaps p) (S.toList qs) >>= \case
    [] -> pure ()
    (IsIn h _):_ -> throwError $ "Instances overlap: " <> i <> " with " <> h
  updateClassEnv i (Class c $ S.insert (ps :=> p) its)


runClassEnvBuilderT :: Monad m
                    => ClassEnv
                    -> ClassEnvBuilderT m ()
                    -> Either ErrMsg (m ClassEnv)
runClassEnvBuilderT ce (ClassEnvBuilder cb) =
  flip execStateT (pure ce) . runExceptT $ pure cb


runClassEnvBuilder :: ClassEnv -> ClassEnvBuilder () -> Either ErrMsg ClassEnv
runClassEnvBuilder ce cb = runIdentity <$> runClassEnvBuilderT ce cb


matchMethodName :: TypeDecl -> DataDef -> Bool
matchMethodName (TypeDecl tn _ _) (DataDef dn _ _) = tn == dn


buildClassEnv :: [ClassDef] -> [ImplDef] -> Either ErrMsg ClassEnv
buildClassEnv cses impls = runClassEnvBuilder emptyClassEnv $ do
  let groupOn :: Ord b => (a -> b) -> [a] -> M.Map b [a]
      groupOn f =
        let fld m a = case M.lookup (f a) m of
              Nothing -> M.insert (f a) [a] m
              Just as -> M.insert (f a) (a:as) m
        in foldl fld M.empty

      instmap = groupOn (\(ImplDef cname _ _) -> cname) impls

  forM_ cses $ \c@(ClassDef cname _ supers _) -> do
    cls <- flip evalStateT (Class supers S.empty) $ do
      forM_ (maybe [] id $ M.lookup cname instmap) $ \i -> do
        checkInstanceFoundation i c
    updateClassEnv cname cls




-- |Check whether instance does not define methods outside interface DAG
checkInstanceFoundation :: ImplDef -> ClassDef -> ClassEnvBuilder ()
checkInstanceFoundation (ImplDef _ _ ddf) c =
  all (isMethodIn c) ddf

  -- forM cses $ \c@(ClassDef cname _ cmethods supers) -> do
  --   let cmethodSet = S.fromList $ fmap (\(TypeDecl n _) -> n) cmethods
  --       cls = flip runStateT (Class)
  --   forM_ (maybe [] id $ M.lookup cname instmap) $ \inst@(ImplDef iname _ imethods) -> do
  --     let imethodSet = S.fromList $ fmap (\(DataDef n _ _) -> n) imethods
  --     when (imethodSet /= cmethodSet) $
  --       throwError $ "Methods mismatch: should be " <> show (S.toList cmethodSet)
  --       <> ", but is " <> show (S.toList imethodSet)

      





program :: Parser Program
program = processProgram <$> rawProgram


rawProgram :: Parser RawProgram
rawProgram = do
  parts <- many $ rawProgramPart <* (operator ";;")
  pure $ foldl insert (RawProgram [] [] [] [] [] []) parts where
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
  , RPClassDef <$> classDef
  , RPImplDef <$> implDef
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
  def <- expr
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


classDef :: Parser ClassDef
classDef = do
  word "interface"
  name <- className
  arg <- generalTypeName
  methods <- brac $ many $ typeDecl <* (operator ";;")
  pure $ ClassDef name arg methods


implDef :: Parser ImplDef
implDef = do
  word "impl"
  cname <- className
  arg <- type_
  methods <- brac $ many $ dataDef <* (operator ";;")
  pure $ ImplDef cname arg methods
