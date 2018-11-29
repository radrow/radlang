module Radlang.Typedefs where

import Data.Set.Monad as S
import Data.Map.Strict as M

import Radlang.Types.General
import Radlang.Types

tUnit :: Type
tUnit = TypeVarRigid $ TypeVar "Unit" KType
tInt :: Type
tInt = TypeVarRigid $ TypeVar "Int" KType

tList :: Type
tList = TypeVarRigid $ TypeVar "List" (KFunc KType KType)
tFunc :: Type
tFunc = TypeVarRigid $ TypeVar "Func" (KFunc KType (KFunc KType KType))

fun :: Type -> Type -> Type
a `fun` b = TypeApp (TypeApp tFunc a) b

numClasses :: Set Name
numClasses = S.fromList ["Num", "Integral"]

stdClasses :: Set Name
stdClasses = S.fromList ["Eq", "Ord", "Show", "Functor", "Monad", "MonadPlus"] `S.union` numClasses


stdPreds :: [Qual Pred]
stdPreds =
  [ [] :=> IsIn "Num" tInt
  , [] :=> IsIn "Integral" tInt
  , [] :=> IsIn "Eq" tInt
  , [] :=> IsIn "Ord" tInt
  , [] :=> IsIn "Show" tInt
  ]

ofClass n = S.fromList $ Prelude.filter (\(_ :=> IsIn k _) -> k == n) stdPreds
envPart s n = (n, s, ofClass n)


-- initClassEnv :: ClassEnv
-- initClassEnv = M.fromList
--   [ envPart S.empty "Num"
--   ]
