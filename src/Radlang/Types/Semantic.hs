{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GADTs #-}

-- |Types related to internal program definition and evaluation

module Radlang.Types.Semantic where

import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State.Strict
import Control.Lens hiding(Lazy, Strict)
import           Data.Map.Strict            (Map)
import           Data.Set                   as S

import           Radlang.Types.General
import           Radlang.Types.Syntax
import           Radlang.Types.Typesystem


type Stacktrace = [String]
type EvalStacktrace = [String]


-- |Desugared expression tree
data Expr
  = Val Name
  | Lit Literal
  | Application Expr Expr
  | Let BindingGroup Expr
  deriving (Eq, Show, Ord)


-- |Expression tree decorated with type annotations
data TypedExpr where
 TypedVal :: Name -> TypedExpr
 TypedLit :: Literal -> TypedExpr
 TypedApplication :: TypedExpr -> TypedExpr -> TypedExpr
 TypedLet :: (Map Name (Type, [([Pattern], TypedExpr)])) -> TypedExpr -> TypedExpr
  deriving (Eq, Show, Ord)


-- |Value stored in the dataspace. May be evaluated or not
data Data
  = Lazy Namespace Stacktrace DataId (Evaluator Data)
  | Strict StrictData
  | Ref DataId


instance Show Data where
  show = \case
    Lazy _ _ i _ -> "<lazy " <> show i <> ">"
    Strict d -> show d
    Ref i -> "<ref " <> show i <> ">"


-- |Value that is in weak-head-normal-form
data StrictData
  = DataInt Integer
  | DataChar Char
  | DataADT Name [Data]
  | DataFunc Name (Data -> Evaluator Data)

instance Show StrictData where
  show = \case
    DataInt i -> show i
    DataChar c -> show c
    DataADT n args -> n <> (((" "<>) . show) =<< args)
    DataFunc n _ -> "<func " <> n <> ">"


-- |Left and right side of function definition
type Alt = ([Pattern], Expr)
type TypedAlt = ([Pattern], TypedExpr)


-- |Explicitly typed binding
type ExplBinding = (Name, (TypePoly, [Alt]))


-- |Implicitly typed binding
type ImplBinding = (Name, [Alt])


-- |Collection of explicitly typed bindings for given name
type ExplBindings = Map Name (TypePoly, [Alt])


-- |Collection of implicitly typed bindings for given name
type ImplBindings = Map Name [Alt]


type TypedBindings = Map Name (Type, [TypedAlt])

-- |Collection of bindings splitted into explicitly typed and implicitly typed
-- grouped as strongly connected components in dependency graph and thopologically
-- sorted
type BindingGroup = (ExplBindings, [ImplBindings])


-- |Full program representation
data Program = Program
  { prgBindings :: [BindingGroup]
  , prgClassEnv :: ClassEnv
  , prgTypeEnv  :: TypeEnv
  , prgDataspace  :: Dataspace
  , prgNamespace  :: Namespace
  } deriving (Show)


data TypedProgram = TypedProgram
  { tprgBindings :: TypedBindings
  , tprgTypeEnv :: TypeEnv
  , tprgDataspace  :: Dataspace
  , tprgNamespace  :: Namespace
  } deriving (Show)


-- |Declaration that binding has certain type
data TypeDecl = TypeDecl
  { tdeclName :: Name
  , tdeclType :: Qual Type}
  deriving (Eq, Ord, Show)


-- |Class definition
data ClassDef = ClassDef
  { classdefName    :: Name
  , classdefArg     :: Name
  , classdefKind    :: Kind
  , classdefSuper   :: (Set Name)
  , classdefMethods :: [TypeDecl]}
  deriving (Eq, Show)


-- |Binding value to name
data DataDef = DataDef
  { datadefName :: Name
  , datadefArgs :: [Pattern]
  , datadefVal  :: Expr}
  deriving (Eq, Show)


-- |Implementation of interface
data ImplDef = ImplDef
  { impldefClass :: Name
  , impldefType :: Qual Type
  , impldefMethods :: [DataDef]}
  deriving (Eq, Show)

-- |`newtype` definition
data NewType = NewType
  { ntName :: Name
  , ntType :: Type
  , ntContrs :: [ConstructorDef]}
  deriving (Eq, Ord, Show)


-- |Definition of constructor
data ConstructorDef = ConstructorDef
  { condefName :: Name
  , condefArgs :: [Type]}
  deriving (Eq, Ord, Show)


type Namespace = Map Name DataId

-- |Map of value names into ids
data Env = Env { _envNamespace :: Namespace
               , _envTypespace :: TypeEnv
               , _envDefStacktrace :: Stacktrace
               , _envEvalStacktrace :: EvalStacktrace
               }
  deriving (Show)

-- |Map of ids into real data
data Dataspace = Dataspace { _dsMap :: Map DataId Data
                           , _dsIdSupply :: DataId
                           } deriving (Show)


-- |Transformer responsible for expression evaluation and error handling
newtype Evaluator a = Evaluator (ExceptT ErrMsg (ReaderT Env (State Dataspace)) a)
  deriving ( Functor, Applicative, Monad, MonadReader Env, MonadState Dataspace
           , MonadError ErrMsg)


makeLenses ''Dataspace
makeLenses ''Env


instance IdSupply Evaluator where
  newId = gets _dsIdSupply <* modify (over dsIdSupply (+1))

