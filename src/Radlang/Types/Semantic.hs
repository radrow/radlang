-- |Types related to program definition and evaluation

module Radlang.Types.Semantic where

import Data.List.NonEmpty
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State.Strict
import  Data.Map.Strict(Map)
import Data.Set.Monad as S

import Radlang.Types.Typesystem
import Radlang.Types.General


-- |Map of value names into ids
type Namespace = Map Name DataId


-- |Map of ids into real data
type Dataspace = (Map DataId Data, Int)


-- |Transformer responsible for expression evaluation and error handling
type Evaluator = ExceptT String (ReaderT Namespace (State Dataspace))


-- |Literal like "" or 2138 or 0.42
data Literal
  = LitInt Integer
  | LitString String
  deriving (Eq, Show, Ord)


-- |Desugared expression tree ready for evaluation
data Expr
  = Val Name
  | Lit Literal
  | Constant (Name, TypePoly)
  | Application Expr Expr
  | Let BindingGroup Expr
  deriving (Eq, Show, Ord)


-- |Possible pattern variations for pattern matching
data Pattern
  = PVar Name
  | PWildcard
  | PAs Name Pattern
  | PLit Literal
  | PConstructor Name [Pattern]
  deriving (Eq, Show, Ord)


-- |Single part of function definition – for example `f a 3 _ = some_expr`
newtype Alternative = Alt (Set Pattern, Expr)
  deriving (Eq, Show, Ord)


-- |Abstract syntax tree that faithfully represents code. Layer between text and Expr
data AST
  = ASTVal Name
  | ASTLit Literal
  | ASTApplication AST (NonEmpty AST)
  | ASTLet (NonEmpty (Name, [Name], Maybe Type, AST)) AST
  | ASTLambda (NonEmpty Name) AST
  | ASTIf (NonEmpty (AST, AST)) AST
  deriving(Eq, Show)


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


data Program = Program
  { prgBindings :: [BindingGroup]
  , prgTypespace :: Typespace
  , prgClassEnv :: ClassEnv
  , prgTypeEnv :: TypeEnv
  } deriving (Eq, Show)

data NewType = NewType
  { ntName :: Name
  , ntArgs :: [Name]
  , ntContrs :: [ConstructorDef]}
  deriving (Eq, Ord, Show)

data ConstructorDef = ConstructorDef
  { condefName :: Name
  , condefArgs :: [Type]}
  deriving (Eq, Ord, Show)

data TypeAlias = TypeAlias
  {taliasName :: Name
  , taliasTarget :: Type}
  deriving (Eq, Ord, Show)

data TypeDecl = TypeDecl
  { tdeclName :: Name
  , tdeclType :: (Qual Type)}
  deriving (Eq, Ord, Show)

data DataDef = DataDef
  { datadefName :: Name
  , datadefArgs :: [Pattern]
  , datadefVal :: Expr}
  deriving (Eq, Show)

data ClassDef = ClassDef
  {classdefName :: Name
  , classdefArg :: Name
  , classdefSuper :: (Set Name)
  , classdefMethods :: [TypeDecl]}
  deriving (Eq, Show)


data ImplDef = ImplDef
  { impldefClass :: Name
  , impldefType :: Type
  , impldefQual :: [Pred]
  , impldefMethods :: [DataDef]}
  deriving (Eq, Show)
