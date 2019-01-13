-- |Types related to internal program definition and evaluation

module Radlang.Types.Semantic where

import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State.Strict
import           Data.Map.Strict            (Map)
import           Data.Set                   as S

import           Radlang.Types.General
import           Radlang.Types.Syntax
import           Radlang.Types.Typesystem


-- |Map of value names into ids
newtype Namespace = Namespace {namespaceMap :: Map Name DataId}


-- |Map of ids into real data
data Dataspace = Dataspace {dataspaceMap :: Map DataId Data
                           , nextId :: DataId
                           }


-- |Transformer responsible for expression evaluation and error handling
type Evaluator = ExceptT String (ReaderT Namespace (State Dataspace))


-- |Desugared expression tree ready for evaluation
data Expr
  = Val Name
  | Lit Literal
  | Constant (Name, TypePoly)
  | Application Expr Expr
  | Let BindingGroup Expr
  deriving (Eq, Show, Ord)


-- |Single part of function definition – for example `f a 3 _ = some_expr`
newtype Alternative = Alt (Set Pattern, Expr)
  deriving (Eq, Show, Ord)



-- |Value stored in the dataspace. May be evaluated or not
data Data = Lazy Namespace DataId Expr | Strict StrictData


-- |Value that is in weak-head-normal-form
data StrictData
  = DataInt Integer
  | DataBool Bool
  | DataLambda Namespace Name Expr
  | DataInternalFunc (Data -> Evaluator Data)

instance Show StrictData where
  show = \case
    DataInt i -> show i
    DataBool b -> show b
    DataLambda _ n e -> "\\" <> n <> " -> " <> show e
    DataInternalFunc _ -> "internal func"

instance Eq StrictData where
  (DataInt a) == (DataInt b) = a == b
  (DataBool a) == (DataBool b) = a == b
  _ == _ = error "Somebody wanted to illegally compare functions" -- we don't compare functions.


-- |Left and right side of function definition
type Alt = ([Pattern], Expr)


-- |Explicitly typed binding
type ExplBinding = (Name, (TypePoly, [Alt]))


-- |Implicitly typed binding
type ImplBinding = (Name, [Alt])


-- |Collection of explicitly typed bindings for given name
type ExplBindings = Map Name (TypePoly, [Alt])


-- |Collection of implicitly typed bindings for given name
type ImplBindings = Map Name [Alt]


-- |Collection of bindings splitted into explicitly typed and implicitly typed
-- grouped as strongly connected components in dependency graph and thopologically
-- sorted
type BindingGroup = (ExplBindings, [ImplBindings])


-- |Full program representation
data Program = Program
  { prgBindings :: [BindingGroup]
  , prgClassEnv :: ClassEnv
  , prgTypeEnv  :: TypeEnv
  } deriving (Eq, Show)


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
