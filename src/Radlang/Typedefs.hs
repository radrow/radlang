module Radlang.Typedefs where

import Data.Set.Monad

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
numClasses = fromList ["Num", "Integral"]

stdClasses :: Set Name
stdClasses = fromList ["Eq", "Ord", "Show", "Functor", "Monad", "MonadPlus"] `union` numClasses
