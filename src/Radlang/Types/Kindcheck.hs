module Radlang.Types.Kindcheck where

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State.Strict

import Radlang.Types.General
import Radlang.Types.Typesystem hiding (free, substitute, TypePoly, getSubstMap)

-- |Kindchecker state currently contains only count of runtime generated types
data KindcheckerState = KindcheckerState { tsSupply :: Int}
  deriving (Eq, Show)

-- |Map of typenames into their kinds
newtype Kindspace = Kindspace { getKindspaceMap :: M.Map Name KindVar }
  deriving (Eq, Show, Ord)
-- newtype KindAssumptions = KindAssumptions (M.Map Name Kind)
--   deriving (Show, Eq)
newtype ClassKinds = ClassKinds { getClassKindsMap :: M.Map Name Kind }
  deriving (Eq, Show, Ord)

-- |Transformer responsible for typechecking expressions and error handling
type Kindchecker = ExceptT String (ReaderT (Kindspace, ClassKinds) (State KindcheckerState))

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


---- INSTANCES ----

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
      Just t -> t
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
    KindVar a -> kstr a
    KindVarType -> "Type"
    KindVarFunc a v ->
      let sa = case a of
            KindVarFunc _ _ -> "(" <> show a <> ")"
            _ -> show a
      in sa <> " -> " <> show v

