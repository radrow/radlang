module Radlang.Typedefs where

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
