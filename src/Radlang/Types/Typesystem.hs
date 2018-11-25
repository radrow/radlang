-- |Types related to typechecking

module Radlang.Types.Typesystem where

import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State.Strict
import qualified Data.Map.Strict as M
import  Data.Map.Strict(Map)
import qualified Data.Set.Monad as S
import Data.Set.Monad(Set)

import Radlang.Types.General

---- DEFINITIONS ----

-- |Typechecker state currently contains only count of runtime generated types
data TypecheckerState = TypecheckerState { tsSupply :: Int}
  deriving (Eq, Show)

-- |Map of typenames into real types
newtype Typespace = Typespace { getTypespaceMap :: Map Name TypePoly }
  deriving (Eq, Show, Ord)

-- |Transformer responsible for typechecking expressions and error handling
type Typechecker = ExceptT String (ReaderT Typespace (State TypecheckerState))


-- |Primitive type definition
data Type
  = TypeVal Name
  | TypeValRigid Name
  | TypeInt
  | TypeBool
  | TypeFunc Type Type
  deriving (Eq, Ord)

-- |Type served along with polymorphic names used inside
data TypePoly = Poly (Set Name) Type
  deriving (Eq, Show, Ord)

-- |Substitution of polymorphic types
newtype Substitution = Subst { getSubstMap :: Map Name Type }
  deriving (Eq, Show, Ord)

-- |Types that may be considered as free types carriers
class Ord t => IsType t where -- Ord is needed because use of Set
  -- |Free type variables in t
  free :: t -> Set Name
  -- |Application of substitution
  substitute :: Substitution -> t -> t


---- INSTANCES ----

instance IsType t => IsType (Set t) where
  free s = s >>= free
  substitute s = S.map (substitute s)

instance IsType Type where
  free = \case
    TypeInt -> S.empty
    TypeBool -> S.empty
    TypeFunc a v -> S.union (free a) (free v)
    TypeVal v -> S.singleton v
    TypeValRigid v -> S.singleton v
  substitute s@(Subst sm) = \case
    TypeInt -> TypeInt
    TypeBool -> TypeBool
    TypeFunc a v -> TypeFunc (substitute s a) (substitute s v)
    TypeVal n -> case M.lookup n sm of
      Just t -> t
      Nothing -> TypeVal n
    TypeValRigid n -> case M.lookup n sm of
      Just t -> t
      Nothing -> TypeValRigid n

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

instance Show Type where
  show = \case
    TypeVal a -> a
    TypeValRigid a -> a
    TypeInt -> "Int"
    TypeBool -> "Bool"
    TypeFunc a v ->
      let sa = case a of
            TypeFunc _ _ -> "(" <> show a <> ")"
            _ -> show a
      in sa <> " -> " <> show v

