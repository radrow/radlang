module Radlang.Types where

import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State.Strict
import qualified Data.Map.Strict            as M
import  Data.Map.Strict(Map)
import qualified Data.Set.Monad as S
import Data.Set.Monad(Set)

type ErrMsg = String
type Name = String

type DataId = Int

type Namespace = Map Name DataId
type Dataspace = (Map DataId Data, Int)
newtype Typespace = Typespace { getTypespaceMap :: Map Name TypePoly }
  deriving (Eq, Show, Ord)

type Evaluator = ExceptT String (ReaderT Namespace (State Dataspace))
type Typechecker = ExceptT String (ReaderT Typespace (State TypecheckerState))
data TypecheckerState = TypecheckerState { tsSub :: Substitution, tsSupply :: Int}

data Expr
  = Val Name
  | ConstInt Int
  | ConstBool Bool
  | Application Expr Expr
  | Let [(Name, Maybe Type, Expr)] Expr
  | Lambda Name Expr
  | Case Expr [(Expr, Expr)]
  | If Expr Expr Expr
  deriving (Eq, Show)

-- |Primitive type definition
data Type
  = TypeVal Name
  | TypeInt
  | TypeBool
  | TypeFunc Type Type
  deriving (Eq, Show, Ord)

-- |Type served along with polymorphic names used inside
data TypePoly = Poly (Set Name) Type
  deriving (Eq, Show, Ord)

-- |Substitution of polymorphic types
newtype Substitution = Subst { getSubstMap :: Map Name Type }
  deriving (Eq, Show, Ord)

-- |Types that may be considered as free types carriers
class Ord t => IsType t where -- Ord is needed because use of Set
  free :: t -> Set Name
  substitute :: Substitution -> t -> t

instance IsType t => IsType (Set t) where
  free s = s >>= free
  substitute s = S.map (substitute s)

instance IsType Type where
  free = \case
    TypeInt -> S.empty
    TypeBool -> S.empty
    TypeFunc a v -> S.union (free a) (free v)
    TypeVal v -> S.singleton v
  substitute s@(Subst sm) = \case
    TypeInt -> TypeInt
    TypeBool -> TypeBool
    TypeFunc a v -> TypeFunc (substitute s a) (substitute s v)
    TypeVal n -> case M.lookup n sm of
      Just t -> t
      Nothing -> TypeVal n

instance IsType TypePoly where
  free (Poly vars t) = free t S.\\ vars
  substitute (Subst s) (Poly vars t) =
    Poly vars $ substitute (Subst $ foldr M.delete s vars) t

instance IsType Typespace where
  free (Typespace ts) = free $ S.fromList (M.elems ts)
  substitute s (Typespace ts) = Typespace $
    M.map (substitute s) ts

instance Semigroup Substitution where
  (<>) s@(Subst s1) (Subst s2) =
    Subst $ M.map (substitute s) s2 `M.union` s1

instance Monoid Substitution where
  mempty = Subst M.empty

data Data
  = DataInt Int
  | DataBool Bool
  | DataLambda Namespace Name Expr
  | DataInternalFunc (Data -> Data)

instance Show Data where
  show = \case
    DataInt i -> show i
    DataBool b -> show b
    DataLambda n nn e -> "lambda in (" <> show n <> ") \\" <> nn <> " -> " <> show e
    DataInternalFunc _ -> "internal func"

instance Eq Data where
  (DataInt a) == (DataInt b) = a == b
  (DataBool a) == (DataBool b) = a == b
  _ == _ = False -- we don't compare functions.
