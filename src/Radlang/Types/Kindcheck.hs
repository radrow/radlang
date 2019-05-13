-- |Type definitions used in kindchecking algorithm
module Radlang.Types.Kindcheck where

import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State.Strict
import qualified Data.Map.Strict            as M
import qualified Data.Set                   as S
import           Data.Text as T

import           Radlang.Types.General
import           Radlang.Types.Typesystem   hiding (TypePoly, free, getSubstMap,
                                             substitute)


-- |Kindchecker state currently contains only count of runtime generated types
data KindcheckerState = KindcheckerState { tsSupply :: Int}
  deriving (Eq, Show)


-- |Map of typenames into their kinds
newtype Kindspace = Kindspace { getKindspaceMap :: M.Map Name KindVar }
  deriving (Eq, Show, Ord)


-- |Map of kinds of interface impls
newtype InterfaceKinds = InterfaceKinds { getInterfaceKindsMap :: M.Map Name Kind }
  deriving (Eq, Show, Ord)


-- |Transformer responsible for typechecking expressions and error handling
type Kindchecker = ExceptT ErrMsg (ReaderT (Kindspace, InterfaceKinds) (State KindcheckerState))


-- |Type wrapper for kind variable names. Prevents from lots of mistakes
newtype KName = KName {kstr :: Name}
  deriving (Eq, Show, Ord)


-- |Primitive type definition
data KindVar
  = KindVar KName
  | KindVarType
  | KindVarFunc KindVar KindVar
  deriving (Eq, Ord)


-- |KindSubstitution of polymorphic types
newtype KindSubstitution = KSubst { getKSubstMap :: M.Map KName KindVar }
  deriving (Eq, Show, Ord)


-- |Kinds that may be considered as free kinds carriers
class Ord t => IsKind t where -- Ord is needed because use of Set
  -- |Free type variables in t
  freeKinds :: t -> S.Set KName
  -- |Application of substitution
  substituteKinds :: KindSubstitution -> t -> t


---- IMPLS ----

instance IsKind t => IsKind (S.Set t) where
  freeKinds s = S.unions $ S.map freeKinds s
  substituteKinds s = S.map (substituteKinds s)


instance IsKind KindVar where
  freeKinds = \case
    KindVar v -> S.singleton v
    KindVarType -> S.empty
    KindVarFunc k1 k2 -> S.union (freeKinds k1) (freeKinds k2)
  substituteKinds s@(KSubst sm) = \case
    KindVarType -> KindVarType
    KindVarFunc a v -> KindVarFunc (substituteKinds s a) (substituteKinds s v)
    KindVar n -> case M.lookup n sm of
      Just t  -> t
      Nothing -> KindVar n


instance IsKind Kindspace where
  freeKinds (Kindspace ts) = freeKinds $ S.fromList (M.elems ts)
  substituteKinds s (Kindspace ts) = Kindspace $
    M.map (substituteKinds s) ts


instance Semigroup KindSubstitution where
  (<>) s@(KSubst s1) (KSubst s2) =
    KSubst $ M.map (substituteKinds s) s2 `M.union` s1


instance Monoid KindSubstitution where
  mempty = KSubst M.empty


instance Show KindVar where
  show = \case
    KindVar a -> T.unpack $ kstr a
    KindVarType -> "Type"
    KindVarFunc a v ->
      let sa = case a of
            KindVarFunc _ _ -> "(" <> show a <> ")"
            _               -> show a
      in sa <> " -> " <> show v
