{-# LANGUAGE TypeOperators #-}

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
  = TypeVarWobbly TypeVar -- Inferred type variable
  | TypeVarRigid TypeVar -- User specified polymorphic type
  | TypeInt
  | TypeADT Int -- ADT with given arity
  | TypeApp Type Type
  deriving (Eq, Ord)

data TypeVar = TypeVar {tName :: Name, tKind :: Kind}
  deriving (Eq, Show, Ord)

data Kind = KType | KFunc Kind Kind
  deriving (Eq, Show, Ord)


-- |Type served along with polymorphic names used inside
data TypePoly = Poly (Set Name) Type
  deriving (Eq, Show, Ord)


data Pred = IsIn Name Type
  deriving (Eq, Ord)


data Qual t = Set Pred :=> t
  deriving (Eq, Ord)


type Inst = Qual Pred


type Class = (Set Name, Set Inst)


data ClassEnv = ClassEnv { classes :: Map Name Class
                         , defaults :: Set Type
                         }


-- |Substitution of polymorphic types
newtype Substitution = Subst { getSubstMap :: Map Name Type }
  deriving (Eq, Show, Ord)


-- |Types that may be considered as free types carriers
class Ord t => IsType t where -- Ord is needed because use of Set
  -- |Free type variables in t
  free :: t -> Set Name
  -- |Application of substitution
  substitute :: Substitution -> t -> t


class HasKind t where
  kind :: t -> Kind


---- INSTANCES ----

instance IsType t => IsType (Set t) where
  free s = s >>= free
  substitute s = S.map (substitute s)


instance IsType Type where
  free = \case
    TypeInt -> S.empty
    TypeApp a v -> S.union (free a) (free v)
    TypeVarWobbly (TypeVar v _) -> S.singleton v
    TypeVarRigid (TypeVar v _) -> S.singleton v
    TypeADT _ -> undefined
  substitute s@(Subst sm) = \case
    TypeInt -> TypeInt
    TypeApp a v -> TypeApp (substitute s a) (substitute s v)
    TypeVarWobbly (TypeVar n k) -> case M.lookup n sm of
      Just t -> t
      Nothing -> TypeVarWobbly $ TypeVar n k
    TypeVarRigid (TypeVar n k) -> case M.lookup n sm of
      Just t -> t
      Nothing -> TypeVarRigid $ TypeVar n k
    TypeADT _ -> undefined


instance IsType Pred where
  free (IsIn _ t) = free t
  substitute s (IsIn i t) = IsIn i (substitute s t)


instance IsType t => IsType (Qual t) where
  free (ps :=> t) = free ps `S.union` free t
  substitute s (ps :=> t) = substitute s ps :=> substitute s t


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
    TypeVarWobbly (TypeVar a _) -> a
    TypeVarRigid (TypeVar a _) -> a
    TypeInt -> "Int"
    TypeApp a b -> show a <> " " <> show b
    TypeADT _ -> undefined


instance HasKind Type where
  kind (TypeVarWobbly tv) = kind tv
  kind (TypeVarRigid tv) = kind tv
  kind TypeInt = KType
  kind (TypeADT _) = undefined
  kind (TypeApp f _) = case kind f of
    (KFunc _ k) -> k
    _ -> error "Kindcheck failed"


instance HasKind TypeVar where
  kind (TypeVar _ k) = k
