{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE StrictData                 #-}

-- |Types related to internal program definition and evaluation

module Radlang.Types.Semantic where

import           Control.Lens               hiding (Lazy, Strict)
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State.Strict
import           Data.Map.Strict            (Map, keys)
import           Data.Set                   as S
import           Data.Text as T

import           Radlang.Types.General
import           Radlang.Types.Syntax
import           Radlang.Types.Typesystem


-- |Stacktrace that follows runtime by definition of the data
type DefStacktrace = [Text]
-- |Stacktrace that follows runtime by evaluation of the data
type EvalStacktrace = [Text]


-- |Desugared expression tree
data UntypedExpr
  = UntypedVal Name
  | UntypedLit Literal
  | UntypedApplication UntypedExpr UntypedExpr
  | UntypedLet BindingGroup UntypedExpr


-- |Expression tree decorated with type annotations
data TypedExpr
  = TypedVal (Qual Type) Name
  | TypedLit (Qual Type) Literal
  | TypedApplication (Qual Type) TypedExpr TypedExpr
  | TypedLet (Qual Type) (Map Name (Qual Type, [([Pattern], TypedExpr)])) TypedExpr
  deriving (Eq, Ord)

data EvalExpr
  = Val Name
  | Lit Literal
  | Application EvalExpr EvalExpr
  | Let Bindings EvalExpr
  | Dict Name

instance Show UntypedExpr where
  show = \case
    UntypedVal v -> T.unpack v
    UntypedLit l -> show l
    UntypedApplication f a -> "(" <> show f <> " " <> show a <> ")"
    UntypedLet bn e -> "let " <> show bn <> " in " <> show e

instance Show TypedExpr where
  show = \case
    TypedVal t v -> "(" <> T.unpack v <> " : " <> show t <> ")"
    TypedLit t l -> "(" <> show l <> " : " <> show t <> ")"
    TypedApplication _ f a -> "(" <> show f <> ") " <> show a
    TypedLet _ bn e -> "let " <> show bn <> " in " <> show e

complex :: EvalExpr -> Bool
complex = \case
  Application _ _ -> True
  Let _ _ -> True
  _ -> False
instance Show EvalExpr where
  show = \case
    Val v -> T.unpack v
    Lit l -> show l
    Application f a ->
      (if complex f then "(" <> show f <> ")" else show f) <> " " <>
      (if complex a then "(" <> show a <> ")" else show a)
    Let bn e -> "let " <> show bn <> " in " <> show e
    Dict d -> "@" <> T.unpack d

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
getExprType :: TypedExpr -> Qual Type
getExprType = \case
  TypedVal t _ -> t
  TypedLit t _ -> t
  TypedApplication t _ _ -> t
  TypedLet t _ _ -> t


-- |Value stored in the dataspace. May be evaluated or not
data Data
  = Lazy Namespace DefStacktrace DataId (Evaluator Data)
  | Strict StrictData
  | PolyDict [(Name, DataId)] [Name] (Map Name Name)

instance Show Data where
  show = \case
    Lazy _ _ i _ -> "<lazy " <> show i <> ">"
    Strict d -> show d
    PolyDict _ sup ns -> "<dict containing " <> show (keys ns) <> " sups: " <> show sup <> ">"


-- |Value that is in weak-head-normal-form
data StrictData
  = DataInt Int
  | DataChar Char
  | DataADT Name [Data]
  | DataFunc Name (Data -> Evaluator Data)
  | DataPolyDict [(Name, DataId)] [Name] (Map Name Name)

instance Show StrictData where
  show = \case
    DataInt i -> show i
    DataChar c -> show c
    DataADT n args ->
      (if Prelude.null args then "" else "(") <>
      T.unpack n <> (((" "<>) . show) =<< args) <>
      (if Prelude.null args then "" else ")")
    DataFunc n _ -> "<func " <> T.unpack n <> ">"
    DataPolyDict load _ ns -> "<dict containing " <> show (keys ns) <> " load: " <> show load <> ">"


-- |Left and right side of a value/function definition
type Alt = ([Pattern], UntypedExpr)
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
type InterfaceBindings = Map Name (Name, (TypeVar, Qual Type), TypePoly, [(TypePoly, [Alt])])


-- |Collection of bindings splitted into explicitly typed and implicitly typed
-- grouped as strongly connected components in dependency graph and thopologically
-- sorted
type BindingGroup = (InterfaceBindings, ExplBindings, [ImplBindings])


-- |Explicitly typed bindings with typed expressions
type TypedBindings = Map Name (Qual Type, [TypedAlt])


-- |Typed bindings for polymorphic data
type PolyBindings = Map Name (Name, (TypeVar, Qual Type), Qual Type, [(Qual Type, [TypedAlt])])


type Bindings = Map Name [([Pattern], EvalExpr)]


type DataMap = Map Name Data


-- |Full program representation
data UntypedProgram = UntypedProgram
  { uprgDataMap      :: DataMap
  , uprgBindings     :: [BindingGroup]
  , uprgInterfaceEnv :: InterfaceEnv
  , uprgTypeEnv      :: TypeEnv
  } deriving (Show)


-- |Program decorated with type annotations
data TypedProgram = TypedProgram
  { tprgDataMap       :: DataMap
  , tprgPolyBindings  :: PolyBindings
  , tprgBindings      :: TypedBindings
  , tprgInterfaceEnv  :: InterfaceEnv
  } deriving (Show)


data Program = Program
  { prgDataMap      :: DataMap
  , prgPolyBindings :: PolyBindings
  , prgBindings     :: Bindings
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
    , datadefVal  :: UntypedExpr}
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


-- |Store for data
type Dataspace = Map DataId Data


-- |Forced state of varaible types
type Typespace = Map Name (Qual Type)


-- |Map of value names into ids
data EvaluationEnv = EvaluationEnv
  { _evenvNamespace      :: Namespace
  , _evenvDefStacktrace  :: DefStacktrace
  , _evenvEvalStacktrace :: EvalStacktrace
  } deriving (Show)


-- |Map of ids into real data
data EvaluationState = EvaluationState
  { _evstDataspace :: Dataspace
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

