{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE TemplateHaskell            #-}

-- |Types related to internal program definition and evaluation

module Radlang.Types.Semantic where

import           Control.Lens               hiding (Lazy, Strict)
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State.Strict
import           Data.Map.Strict            (Map)
import           Data.Set                   as S

import           Radlang.Types.General
import           Radlang.Types.Syntax
import           Radlang.Types.Typesystem


-- |Stacktrace that follows runtime by definition of the data
type DefStacktrace = [String]
-- |Stacktrace that follows runtime by evaluation of the data
type EvalStacktrace = [String]


-- |Desugared expression tree
data Expr
  = Val Name
  | Lit Literal
  | Application Expr Expr
  | Let BindingGroup Expr
  deriving (Show)


-- |Expression tree decorated with type annotations
data TypedExpr where
  TypedVal :: Type -> Name -> TypedExpr
  TypedLit :: Type -> Literal -> TypedExpr
  TypedApplication :: Type -> TypedExpr -> TypedExpr -> TypedExpr
  TypedLet :: Type -> (Map Name (Type, [([Pattern], TypedExpr)])) -> TypedExpr -> TypedExpr
  deriving (Eq, Ord)

instance Show TypedExpr where
  show = \case
    TypedVal t v -> "(" <> v <> " : " <> show t <> ")"
    TypedLit t l -> "(" <> show l <> " : " <> show t <> ")"
    TypedApplication _ f a -> "(" <> show f <> ") " <> show a
    TypedLet _ bn e -> "let " <> show bn <> " in " <> show e

instance IsType TypedExpr where
  free = free . getExprType
  substitute s = \case
    TypedVal t v -> TypedVal (substitute s t) v
    TypedLit t l -> TypedLit (substitute s t) l
    TypedApplication t f a -> TypedApplication (substitute s t)
      (substitute s f) (substitute s a)
    TypedLet t bn e -> TypedLet (substitute s t)
      (flip fmap bn $ \(ta, alts) -> (substitute s ta, flip fmap alts $ \(pts, ea) -> (pts, substitute s ea))) (substitute s e)


-- |Extracts `Type` from `TypedExpr`
getExprType :: TypedExpr -> Type
getExprType = \case
  TypedVal t _ -> t
  TypedLit t _ -> t
  TypedApplication t _ _ -> t
  TypedLet t _ _ -> t


-- |Value stored in the dataspace. May be evaluated or not
data Data
  = Lazy Namespace Typespace Substitution DefStacktrace DataId (Evaluator Data)
  | Strict StrictData

instance Show Data where
  show = \case
    Lazy _ _ _ _ i _ -> "<lazy " <> show i <> ">"
    Strict d -> show d


-- |Value that is in weak-head-normal-form
data StrictData
  = DataInt Integer
  | DataChar Char
  | DataADT Name [Data]
  | DataFuncSub Name (Substitution -> Data -> Evaluator Data)
  | DataFunc Name (Data -> Evaluator Data)

instance Show StrictData where
  show = \case
    DataInt i -> show i
    DataChar c -> show c
    DataADT n args -> n <> (((" "<>) . show) =<< args)
    DataFunc n _ -> "<func " <> n <> ">"
    DataFuncSub n _ -> "<func " <> n <> ">"


-- |Left and right side of a value/function definition
type Alt = ([Pattern], Expr)
-- |Left and right side of a typed value/function definition
type TypedAlt = ([Pattern], TypedExpr)


-- |Explicitly typed binding
type ExplBinding = (Name, (TypePoly, [Alt]))


-- |Implicitly typed binding
type ImplBinding = (Name, [Alt])


-- |Collection of explicitly typed bindings for given name
type ExplBindings = Map Name (TypePoly, [Alt])


-- |Collection of implicitly typed bindings for given name
type ImplBindings = Map Name [Alt]


-- |Collection of bindings that belong to interface. First `TypePoly` describes general type of method,
-- the other ones are about the specific implementations
type InterfaceBindings = Map Name (TypePoly, [(TypePoly, [Alt])])


-- |Collection of bindings splitted into explicitly typed and implicitly typed
-- grouped as strongly connected components in dependency graph and thopologically
-- sorted
type BindingGroup = (InterfaceBindings, ExplBindings, [ImplBindings])


-- |Explicitly typed bindings with typed expressions
type TypedBindings = Map Name (Type, [TypedAlt])


-- |Typed bindings for polymorphic data
type PolyBindings = Map Name [(Type, [TypedAlt])]


-- |Full program representation
data Program = Program
  { prgDatamap      :: Map Name Data
  , prgBindings     :: [BindingGroup]
  , prgInterfaceEnv :: InterfaceEnv
  , prgTypeEnv      :: TypeEnv
  } deriving (Show)


-- |Program decorated with type annotations
data TypedProgram = TypedProgram
  { tprgDataspace    :: Dataspace
  , tprgNamespace    :: Namespace
  , tprgPolyBindings :: PolyBindings
  , tprgBindings     :: TypedBindings
  } deriving (Show)


-- |Declaration that binding has certain type
data TypeDecl = TypeDecl
  { tdeclName :: Name
  , tdeclType :: Qual Type}
  deriving (Show)


-- |Interface definition
data InterfaceDef = InterfaceDef
  { interfacedefName    :: Name
  , interfacedefArg     :: Name
  , interfacedefKind    :: Kind
  , interfacedefSuper   :: (Set Name)
  , interfacedefMethods :: [TypeDecl]}
  deriving (Show)


-- |Binding value to name
data DataDef
  = DataDef
    { datadefName :: Name
    , datadefArgs :: [Pattern]
    , datadefVal  :: Expr}
  deriving (Show)


-- |Implementation of interface
data ImplDef = ImplDef
  { impldefInterface   :: Name
  , impldefType    :: Qual Type
  , impldefMethods :: [DataDef]}
  deriving (Show)

-- |`newtype` definition
data NewType = NewType
  { ntName   :: Name
  , ntType   :: Type
  , ntContrs :: [ConstructorDef]}
  deriving (Show)


-- |Definition of constructor
data ConstructorDef = ConstructorDef
  { condefName :: Name
  , condefArgs :: [Type]}
  deriving (Show)


-- |Mapping from variable names to their place in dataspace
type Namespace = Map Name DataId


-- |Mapping from variable names to their data regarding their type
type Polyspace = Map Name [(Type, DataId)]


-- |Store for data
type Dataspace = Map DataId Data


-- |Forced state of varaible types
type Typespace = Map Name Type


-- |Map of value names into ids
data EvaluationEnv = EvaluationEnv
  { _evenvNamespace      :: Namespace
  , _evenvPolyspace      :: Polyspace
  , _evenvSubst          :: Substitution
  , _evenvTypespace      :: Typespace
  , _evenvDefStacktrace  :: DefStacktrace
  , _evenvEvalStacktrace :: EvalStacktrace
  } deriving (Show)


-- |Map of ids into real data
data EvaluationState = EvaluationState
  { _evstDataspace :: Map DataId Data
  , _evstIdSupply  :: DataId
  } deriving (Show)


-- |Transformer responsible for expression evaluation and error handling
newtype Evaluator a =
  Evaluator (ExceptT ErrMsg (ReaderT EvaluationEnv (State EvaluationState)) a)
  deriving ( Functor, Applicative, Monad, MonadReader EvaluationEnv
           , MonadState EvaluationState, MonadError ErrMsg)


makeLenses ''EvaluationState
makeLenses ''EvaluationEnv


instance IdSupply Evaluator where
  newId = gets _evstIdSupply <* modify (over evstIdSupply (+1))

