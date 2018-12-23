module Radlang.Typedefs where

import Data.Set.Monad as S
import Data.Map.Strict as M

import Radlang.Helpers
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


stdPreds :: [Qual Pred]
stdPreds =
  [ [] :=> IsIn "Num" tInt
  , [] :=> IsIn "Integral" tInt
  , [] :=> IsIn "Eq" tInt
  , [] :=> IsIn "Ord" tInt
  , [] :=> IsIn "Show" tInt
  ]

ofClass :: Name -> Set (Qual Pred)
ofClass n = S.fromList $ Prelude.filter (\(_ :=> IsIn k _) -> k == n) stdPreds
envPart :: b -> [Char] -> ([Char], b, Set (Qual Pred))
envPart s n = (n, s, ofClass n)

num :: Class
num = Class S.empty $ S.fromList
  [ [] :=> IsIn "Num" (TypeVarRigid $ TypeVar "Int" KType)
  ]

eq :: Class
eq = Class S.empty $ S.fromList
  [ [] :=> IsIn "Eq" (TypeVarRigid $ TypeVar "Int" KType)
  ]

ord :: Class
ord = Class (S.singleton "Eq") $ S.fromList
  [ [] :=> IsIn "Ord" (TypeVarRigid $ TypeVar "Int" KType)
  ]

stdClasses :: Map Name Class
stdClasses = M.fromList
  [ "Num" <~ num
  , "Eq" <~ eq
  , "Ord" <~ ord
  ]


stdDefaults :: Map Name [Type]
stdDefaults = M.map (Prelude.map (\tn -> TypeVarRigid $ TypeVar tn KType)) $ M.fromList
  [ "Num" <~ ["Int"]
  ]


stdClassEnv :: ClassEnv
stdClassEnv = ClassEnv stdClasses stdDefaults
