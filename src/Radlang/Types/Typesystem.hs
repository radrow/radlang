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
data TypecheckerState = TypecheckerState { tsSupply :: Int, tsSubst :: Substitution}
  deriving (Eq, Show)


-- |Transformer responsible for typechecking expressions and error handling
type Typechecker = ExceptT String (ReaderT () (State TypecheckerState))


-- |Primitive type definition
data Type
  = TypeVarWobbly TypeVar -- Inferred type variable
  | TypeVarRigid TypeVar -- User specified polymorphic type
  | TypeInt
  | TypeGeneric Int -- ADT with given arity
  | TypeApp Type Type
  deriving (Eq, Ord)

data TypeVar = TypeVar {tName :: Name, tKind :: Kind}
  deriving (Eq, Show, Ord)

data Kind = KType | KFunc Kind Kind
  deriving (Eq, Show, Ord)


-- |Type scheme for polymorphic types
data Scheme = Forall [Kind] (Qual Type)
  deriving (Eq, Ord, Show)


-- |Predicate that type is in class
data Pred = IsIn Name Type
  deriving (Eq, Ord, Show)


-- |Object with qualified with predicates
data Qual t = [Pred] :=> t
  deriving (Eq, Ord, Show)


-- |Turn this into map
data Assumption = Name :>: Scheme
  deriving (Eq, Ord, Show)


-- |Instance declaration
type Inst = Qual Pred


-- |Typeclass!
type Class = (Set Name, Set Inst)


-- |Main container for classes
data ClassEnv = ClassEnv { classes :: Map Name Class
                         , defaults :: Set Type
                         }


-- |Substitution of polymorphic types
newtype Substitution = Subst { getSubstMap :: Map Name Type }
  deriving (Eq, Show, Ord)


-- |Types that may be considered as free types carriers
class Ord t => IsType t where -- Ord is needed because use of Set
  -- |Free type variables in t
  free :: t -> Set TypeVar
  -- |Application of substitution
  substitute :: Substitution -> t -> t


class HasKind t where
  kind :: t -> Kind


class Instantiate t where
  -- |Replace each occurence of generic var in any TypeGeneric n in t with ts !! n
  instantiate :: [Type] -> t -> t


---- INSTANCES ----

instance IsType t => IsType (Set t) where
  free s = s >>= free
  substitute s = S.map (substitute s)



instance IsType t => IsType [t] where
  free s = S.unions $ fmap free s
  substitute s = fmap (substitute s)


instance IsType Type where
  free = \case
    TypeInt -> S.empty
    TypeApp a v -> S.union (free a) (free v)
    TypeVarWobbly tv -> S.singleton tv
    _ -> S.empty
  substitute s@(Subst sm) = \case
    TypeInt -> TypeInt
    TypeApp a v -> TypeApp (substitute s a) (substitute s v)
    TypeVarWobbly (TypeVar n k) -> case M.lookup n sm of
      Just t -> t
      Nothing -> TypeVarWobbly $ TypeVar n k
    TypeVarRigid (TypeVar n k) -> case M.lookup n sm of
      Just t -> t
      Nothing -> TypeVarRigid $ TypeVar n k
    t -> t


instance IsType Pred where
  free (IsIn _ t) = free t
  substitute s (IsIn i t) = IsIn i (substitute s t)


instance IsType t => IsType (Qual t) where
  free (ps :=> t) = free ps `S.union` free t
  substitute s (ps :=> t) = substitute s ps :=> substitute s t


instance IsType Scheme where
  substitute s (Forall ks qt) = Forall ks (substitute s qt)
  free (Forall _ qt) = free qt


instance IsType Assumption where
  free (_ :>: sc) = free sc
  substitute s (i :>: sc) = i :>: substitute s sc


-- instance IsType Typespace where
  -- free (Typespace ts) = free $ S.fromList (M.elems ts)
  -- substitute s (Typespace ts) = Typespace $
  --   M.map (substitute s) ts


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
    TypeGeneric n -> "Generic" <> show n


instance HasKind Type where
  kind (TypeVarWobbly tv) = kind tv
  kind (TypeVarRigid tv) = kind tv
  kind TypeInt = KType
  kind (TypeGeneric _) = error "kindcheck generic"
  kind (TypeApp f _) = case kind f of
    (KFunc _ k) -> k
    _ -> error "Kindcheck failed"


instance HasKind TypeVar where
  kind (TypeVar _ k) = k


instance Instantiate Type where
  instantiate ts (TypeApp l r) = TypeApp (instantiate ts l) (instantiate ts r)
  instantiate ts (TypeGeneric n) = ts !! n
  instantiate _ t = t


instance Instantiate a => Instantiate [a] where
  instantiate ts = fmap (instantiate ts)


instance Instantiate a => Instantiate (Set a) where
  instantiate ts = fmap (instantiate ts)



instance Instantiate t => Instantiate (Qual t) where
  instantiate ts (ps :=> t) = instantiate ts ps :=> instantiate ts t


instance Instantiate Pred where
  instantiate ts (IsIn c t) = IsIn c (instantiate ts t)
