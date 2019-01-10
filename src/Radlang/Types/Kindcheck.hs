module Radlang.Types.Kindcheck where

import Data.List.NonEmpty
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State.Strict

import Radlang.Types.General
import Radlang.Types.Typesystem hiding (free, substitute, TypePoly, getSubstMap)
-- import Radlang.Parser.Expr
import Radlang.ClassEnvBuild
-- import qualified Radlang.Types as RT
import Radlang.Typesystem.Typesystem hiding (mgu, bindVar)

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
lookupClassKind n = M.lookup n . getClassKindsMap

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
newtype KindSubstitution = KSubst { getSubstMap :: M.Map KName KindVar }
  deriving (Eq, Show, Ord)

-- |Kinds that may be considered as free types carriers
class Ord t => IsKind t where -- Ord is needed because use of Set
  -- |Free type variables in t
  free :: t -> S.Set KName
  -- |Application of substitution
  substitute :: KindSubstitution -> t -> t


---- INSTANCES ----

instance IsKind t => IsKind (S.Set t) where
  free s = S.unions $ S.map free s
  substitute s = S.map (substitute s)

instance IsKind KindVar where
  free = \case
    KindVar v -> S.singleton v
    KindVarType -> S.empty
    KindVarFunc k1 k2 -> S.union (free k1) (free k2)
  substitute s@(KSubst sm) = \case
    KindVarType -> KindVarType
    KindVarFunc a v -> KindVarFunc (substitute s a) (substitute s v)
    KindVar n -> case M.lookup n sm of
      Just t -> t
      Nothing -> KindVar n

instance IsKind Kindspace where
  free (Kindspace ts) = free $ S.fromList (M.elems ts)
  substitute s (Kindspace ts) = Kindspace $
    M.map (substitute s) ts

instance Semigroup KindSubstitution where
  (<>) s@(KSubst s1) (KSubst s2) =
    KSubst $ M.map (substitute s) s2 `M.union` s1

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

