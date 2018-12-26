{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}

-- |Types related to typechecking

module Radlang.Types.Typesystem where

import Data.Foldable
import Control.Applicative
import Control.Monad.Identity
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State.Strict
import qualified Data.Map.Strict as M
import  Data.Map.Strict(Map)
import qualified Data.Set.Monad as S
import Data.Set.Monad(Set)

import Radlang.Types.General


---- DEFINITIONS ----


data TypeInferState = TypeInferState
  { tiSupply :: Int
  , tiSubst :: Substitution
  } deriving (Eq, Show)

data TypecheckerState = TypecheckerState
  { tcSupply :: Int
  , tcSubst :: Substitution
  , tcTypeEnv :: TypeEnv
  } deriving (Eq, Show)

-- |Main container for classes
data ClassEnv = ClassEnv { classes :: Map Name Class
                         , defaults :: Map Name [Type]
                         }
  deriving (Eq, Ord, Show)


newtype TypeEnv = TypeEnv {types :: Map Name TypePoly}
  deriving (Eq, Ord, Show)


newtype ClassEnvBuilderT m a =
  ClassEnvBuilder (ExceptT ErrMsg (StateT ClassEnv m) a)
  deriving ( Functor, Applicative, Monad, Alternative, MonadPlus
           , MonadError ErrMsg, MonadState ClassEnv)
deriving instance MonadIO (ClassEnvBuilderT IO)
type ClassEnvBuilder = ClassEnvBuilderT Identity

newtype TypeInferT m a =
  TypeInfer (ExceptT ErrMsg (ReaderT (TypeEnv, ClassEnv) (StateT TypeInferState m)) a)
  deriving ( Functor, Applicative, Monad, Alternative, MonadPlus
           , MonadError ErrMsg, MonadReader (TypeEnv, ClassEnv), MonadState TypeInferState)
deriving instance MonadIO (TypeInferT IO)
type TypeInfer = TypeInferT Identity

-- |Transformer responsible for typechecking expressions and error handling
newtype TypecheckerT m a =
  Typechecker (ExceptT ErrMsg (ReaderT ClassEnv (StateT TypecheckerState m)) a)
  deriving ( Functor, Applicative, Monad, Alternative, MonadPlus
           , MonadError ErrMsg, MonadReader ClassEnv, MonadState TypecheckerState)
deriving instance MonadIO (TypecheckerT IO)
type Typechecker = TypecheckerT Identity

class (MonadError ErrMsg m, MonadPlus m) => HasClassEnv m where
  getClassEnv :: m ClassEnv

instance Monad m => HasClassEnv (ClassEnvBuilderT m) where
  getClassEnv = get
instance Monad m => HasClassEnv (TypeInferT m) where
  getClassEnv = asks snd
instance Monad m => HasClassEnv (TypecheckerT m) where
  getClassEnv = ask

class (MonadError ErrMsg m, MonadPlus m) => HasTypeEnv m where
  getTypeEnv :: m TypeEnv
instance Monad m => HasTypeEnv (TypeInferT m) where
  getTypeEnv = asks fst
instance Monad m => HasTypeEnv (TypecheckerT m) where
  getTypeEnv = gets tcTypeEnv

class (MonadError ErrMsg m, MonadPlus m) => Substitutor m where
  getSubst :: m Substitution
  setSubst :: Substitution -> m ()

instance Monad m => Substitutor (TypeInferT m) where
  getSubst = gets tiSubst
  setSubst s = modify $ \ti -> ti{tiSubst = s}
instance Monad m => Substitutor (TypecheckerT m) where
  getSubst = gets tcSubst
  setSubst s = modify $ \tc -> tc{tcSubst = s}

class (MonadError ErrMsg m, MonadPlus m) => IdSupply m where
  newId :: m Int
instance Monad m => IdSupply (TypeInferT m) where
  newId = gets tiSupply >>= \i -> modify (\s -> s{tiSupply = i + 1}) >> pure (i + 1)
instance Monad m => IdSupply (TypecheckerT m) where
  newId = gets tcSupply >>= \i -> modify (\s -> s{tcSupply = i + 1}) >> pure (i + 1)



-- |Primitive type definition
data Type
  = TypeVarWobbly TypeVar -- Inferred type variable
  | TypeVarRigid TypeVar -- Non generalizable type
  | TypeGeneric Int -- Generic type with it's index on TypePoly list
  | TypeApp Type Type
  deriving (Eq, Ord)


-- |Type variable
data TypeVar = TypeVar {tName :: Name, tKind :: Kind}
  deriving (Eq, Ord)


-- |Kind – the type of type
data Kind = KType | KFunc Kind Kind
  deriving (Eq, Ord)


-- |Type scheme for polymorphic types
data TypePoly = Forall [Kind] (Qual Type)
  deriving (Eq, Ord)


-- |Predicate that type is in class
data Pred = IsIn Name Type
  deriving (Eq, Ord)


-- |Object with qualified with predicates
data Qual t = [Pred] :=> t
  deriving (Eq, Ord)


-- |Instance declaration
type Inst = Qual Pred


-- |Typeclass is a set of its superclasses and instances
data Class = Class
  { classSuper :: Set Name -- superclasses of class
  , classInstances :: Set Inst -- instances of class
  }
  deriving (Eq, Ord, Show)


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
    TypeApp a v -> S.union (free a) (free v)
    TypeVarWobbly tv -> S.singleton tv
    _ -> S.empty
  substitute s@(Subst sm) = \case
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


instance IsType TypePoly where
  substitute s (Forall ks qt) = Forall ks (substitute s qt)
  free (Forall _ qt) = free qt


instance (Ord k, IsType t) => IsType (Map k t) where
  free = fold . fmap (free . snd) . M.toList
  substitute s te = fmap (substitute s) te


instance IsType TypeEnv where
  free = free . types
  substitute s te = TypeEnv $ fmap (substitute s) (types te)


-- instance IsType Typespace where
  -- free (Typespace ts) = free $ S.fromList (M.elems ts)
  -- substitute s (Typespace ts) = Typespace $
  --   M.map (substitute s) ts


instance Semigroup Substitution where
  (<>) s@(Subst s1) (Subst s2) =
    Subst $ M.map (substitute s) s2 `M.union` s1


instance Monoid Substitution where
  mempty = Subst M.empty


-- deriving instance Show Type
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


instance HasKind Type where
  kind (TypeVarWobbly tv) = kind tv
  kind (TypeVarRigid tv) = kind tv
  kind (TypeGeneric _) = error "kindcheck generic"
  kind (TypeApp f _) = case kind f of
    (KFunc _ k) -> k
    _ -> error $ "Kindcheck failed: expected " <> show f
      <> " to be functional kind, but got KType"


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


---- SHOWS

instance Show Pred where
  show (IsIn c t) = show t <> " is " <> c

instance Show t => Show (Qual t) where
  show ([] :=> t) = show t where
  show (ps :=> t) = showPs ps <> " :- " <> show t where
    showPs [] = undefined
    showPs [p] = show p
    showPs (p:pt) = "(" <> show p <> ", " <> showPs pt <> ")"

instance Show Kind where
  show KType = "Type"
  show (KFunc k1 k2) = "(" <> show k1 <> " -> " <> show k2 <> ")"

instance Show TypeVar where
  show (TypeVar t KType) = show t
  show (TypeVar t k) = "(" <> show t <> " : " <> show k <> ")"

instance Show TypePoly where
  show (Forall [] t) = show t
  show (Forall ks t) = show t <> " where " <>
    concatMap (\i -> "\n  " <> show (TypeGeneric i) <> " : " <> show (ks !! i)) [0..length ks -1]

