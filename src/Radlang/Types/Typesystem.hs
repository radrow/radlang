{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE LambdaCase #-}

-- |Types related to typechecking

module Radlang.Types.Typesystem where

import           Data.Foldable
import           Control.Monad.Identity
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State.Strict
import qualified Data.Map.Strict as M
import           Data.Map.Strict(Map)
import qualified Data.Set as S
import           Data.Set(Set)

import Radlang.Types.General


---- CLASSES ----


-- |Types that may be considered as free types carriers
class Ord t => IsType t where -- Ord is needed because use of Set
  -- |Free type variables in t
  free :: t -> [TypeVar]
  -- |Application of substitution
  substitute :: Substitution -> t -> t


instance IsType t => IsType (Set t) where
  free s = join . S.toList $ S.map free s
  substitute s = S.map (substitute s)


instance IsType t => IsType [t] where
  free s = free =<< s
  substitute s = fmap (substitute s)


instance (Ord k, IsType t) => IsType (Map k t) where
  free = fold . fmap (free . snd) . M.toList
  substitute s te = fmap (substitute s) te


-- |Object that has kind defined
class HasKind t where
  kind :: t -> Kind


-- |Object that carries generic values
class Instantiate t where
  -- |Replace each occurence of generic var in any TypeGeneric n in t with
  -- typevar of respective kind
  instantiate :: [Type] -> t -> t


instance (Instantiate a, Ord a) => Instantiate [a] where
  instantiate ts = fmap (instantiate ts)


instance (Instantiate a, Ord a) => Instantiate (Set a) where
  instantiate ts = S.map (instantiate ts)


-- |Computation that has access to class environment
class (MonadError ErrMsg m) => HasClassEnv m where
  getClassEnv :: m ClassEnv


-- |Computation that has access to type environment
class (MonadError ErrMsg m) => HasTypeEnv m where
  getTypeEnv :: m TypeEnv


-- |Computation that carries and modifies `Substitution`
class (MonadError ErrMsg m) => Substitutor m where
  getSubst :: m Substitution
  setSubst :: Substitution -> m ()


-- |Computation that has built-in `Int` generator
class (MonadError ErrMsg m) => IdSupply m where
  newId :: m DataId


---- DEFINITIONS ----


-- |Main configuration datatype for typechecker
newtype TypecheckerConfig = TypecheckerConfig
  { monomorphismRestriction :: Bool
  }


-- |Mutable state of the typechecker
data TypecheckerState = TypecheckerState
  { tcSupply :: Int
  , tcSubst :: Substitution
  } deriving (Eq, Show)


-- |Immutable environment of typechecker
data TypecheckerEnv = TypecheckerEnv
  { classEnv :: ClassEnv
  , typeEnv :: TypeEnv
  , tcConfig :: TypecheckerConfig
  }


-- |Main container for classes
data ClassEnv = ClassEnv { classes :: Map Name Class
                         , defaults :: Map Name [Type]
                         }
  deriving (Eq, Ord, Show)


-- |Map from data names to their most general inferred types
newtype TypeEnv = TypeEnv {types :: Map Name TypePoly}
  deriving (Eq, Ord)


instance Show TypeEnv where
  show (TypeEnv te) = showTypes (M.toList te) where
    showTypes [] = ""
    showTypes ((n, t):tl) = n <> " :\t" <> show t <> "\n" <> showTypes tl


instance Semigroup TypeEnv where
  (TypeEnv t1) <> (TypeEnv t2) = TypeEnv (M.union t1 t2)


instance Monoid TypeEnv where
  mempty = TypeEnv M.empty
  mappend = (<>)


instance IsType TypeEnv where
  free = free . types
  substitute s te = TypeEnv $ fmap (substitute s) (types te)


-- |Computation that builds class environment
newtype ClassEnvBuilderT m a =
  ClassEnvBuilder (StateT ClassEnv (ExceptT ErrMsg m) a)
  deriving ( Functor, Applicative, Monad
           , MonadError ErrMsg, MonadState ClassEnv)
type ClassEnvBuilder = ClassEnvBuilderT Identity


deriving instance MonadIO (ClassEnvBuilderT IO)


instance Monad m => HasClassEnv (ClassEnvBuilderT m) where
  getClassEnv = get


-- |Transformer responsible for typechecking whole program and error handling
newtype TypecheckerT m a =
  Typechecker (ExceptT ErrMsg (ReaderT TypecheckerEnv (StateT TypecheckerState m)) a)
  deriving ( Functor, Applicative, Monad
           , MonadError ErrMsg, MonadReader TypecheckerEnv, MonadState TypecheckerState)
type Typechecker = TypecheckerT Identity


deriving instance MonadIO (TypecheckerT IO)


instance Monad m => HasClassEnv (TypecheckerT m) where
  getClassEnv = asks classEnv


instance Monad m => HasTypeEnv (TypecheckerT m) where
  getTypeEnv = asks typeEnv


instance Monad m => Substitutor (TypecheckerT m) where
  getSubst = gets tcSubst
  setSubst s = modify $ \tc -> tc{tcSubst = s}


instance Monad m => IdSupply (TypecheckerT m) where
  newId = gets tcSupply <* modify (\ts -> ts{tcSupply = tcSupply ts + 1})


-- |Primitive type definition
data Type
  = TypeVarWobbly TypeVar -- Inferred type variable
  | TypeVarRigid TypeVar -- Non generalizable type
  | TypeGeneric Int -- Generic type with it's index on TypePoly list
  | TypeApp Type Type
  deriving (Eq, Ord)


instance HasKind Type where
  kind (TypeVarWobbly tv) = kind tv
  kind (TypeVarRigid tv) = kind tv
  kind (TypeGeneric _) = error "kindcheck generic"
  kind (TypeApp f _) = case kind f of
    (KFunc _ k) -> k
    _ -> error $ "Kindcheck failed: expected " <> show f
      <> " to be functional kind, but got KType"


instance Show Type where
  show = \case
    TypeVarWobbly (TypeVar a _) -> a
    TypeVarRigid (TypeVar a _) -> a
    TypeApp (TypeApp (TypeVarRigid (TypeVar "Func" _)) arg)
      val -> let aa = case arg of
                   TypeVarRigid _ -> show arg
                   TypeVarWobbly _ -> show arg
                   _ -> "(" <> show arg <> ")"
             in aa <> " -> " <> show val
    TypeApp a b -> show a <> " " <> show b
    TypeGeneric n ->
      let (prims, letter) = divMod n 25
      in "~" <> pure (['A'..] !! letter) <> foldr (<>) "" (take prims (repeat "'"))


instance Instantiate Type where
  instantiate ts (TypeApp l r) = TypeApp (instantiate ts l) (instantiate ts r)
  instantiate ts (TypeGeneric n) = ts !! n
  instantiate _ t = t


instance IsType Type where
  free = \case
    TypeApp a v -> (free a) ++ (free v)
    TypeVarWobbly tv -> [tv]
    _ -> []
  substitute s@(Subst sm) = \case
    TypeApp a v -> TypeApp (substitute s a) (substitute s v)
    TypeVarWobbly (TypeVar n k) -> case M.lookup n sm of
      Just t -> t
      Nothing -> TypeVarWobbly $ TypeVar n k
    TypeVarRigid (TypeVar n k) -> case M.lookup n sm of
      Just t -> t
      Nothing -> TypeVarRigid $ TypeVar n k
    t -> t


-- |Kind – the type of type
data Kind = KType | KFunc Kind Kind
  deriving (Eq, Ord)

instance Show Kind where
  show KType = "Type"
  show (KFunc k1 k2) = "(" <> show k1 <> " -> " <> show k2 <> ")"


-- |Type variable
data TypeVar = TypeVar {tName :: Name, tKind :: Kind}
  deriving (Eq, Ord)


instance Show TypeVar where
  show (TypeVar t KType) = show t
  show (TypeVar t k) = "(" <> show t <> " : " <> show k <> ")"


instance HasKind TypeVar where
  kind (TypeVar _ k) = k


-- |Predicate that type is in class
data Pred = IsIn Name Type
  deriving (Eq, Ord)


instance Show Pred where
  show (IsIn c t) = show t <> " is " <> c


instance IsType Pred where
  free (IsIn _ t) = free t
  substitute s (IsIn i t) = IsIn i (substitute s t)


instance Instantiate Pred where
  instantiate ts (IsIn c t) = IsIn c (instantiate ts t)


-- |Object with qualified with predicates
data Qual t = [Pred] :=> t
  deriving (Eq, Ord)


instance Show t => Show (Qual t) where
  show ([] :=> t) = show t where
  show (ps :=> t) = showPs ps <> " :- " <> show t where
    showPs [] = undefined
    showPs [p] = show p
    showPs (p:pt) = "(" <> show p <> ", " <> showPs pt <> ")"
instance Instantiate t => Instantiate (Qual t) where
  instantiate ts (ps :=> t) = instantiate ts ps :=> instantiate ts t


instance IsType t => IsType (Qual t) where
  free (ps :=> t) = free ps ++ free t
  substitute s (ps :=> t) = substitute s ps :=> substitute s t


-- |Instance declaration
type Inst = Qual Pred


-- |Type scheme for polymorphic types
data TypePoly = Forall [Kind] (Qual Type)
  deriving (Eq, Ord)


instance Show TypePoly where
  show (Forall [] t) = show t
  show (Forall ks t) = show t <> " where " <>
    concatMap (\i -> "\n  " <> show (TypeGeneric i) <> " : " <> show (ks !! i)) [0..length ks -1]

instance IsType TypePoly where
  substitute s (Forall ks qt) = Forall ks (substitute s qt)
  free (Forall _ qt) = free qt


-- |Typeclass ambiguity
type Ambiguity = (TypeVar, [Pred])


-- |Typeclass is a set of its superclasses and instances
data Class = Class
  { classSuper :: Set Name -- superclasses of class
  , classInstances :: Set Inst -- instances of class
  }
  deriving (Eq, Ord, Show)


-- |Substitution of polymorphic types
newtype Substitution = Subst { getSubstMap :: Map Name Type }
  deriving (Eq, Show, Ord)


instance Semigroup Substitution where
  (<>) s@(Subst s1) (Subst s2) =
    Subst $ M.map (substitute s) s2 `M.union` s1


instance Monoid Substitution where
  mempty = Subst M.empty
