{-# LANGUAGE OverloadedLists #-}

module Radlang.Typedefs where

import Data.Set as S
import Data.Map.Strict as M

import Radlang.Helpers
import Radlang.Types.General
import Radlang.Types
import Radlang.Typesystem.Typesystem
import Radlang.Kindchecker

tRigid :: Name -> Type
tRigid n = TypeVarRigid $ TypeVar n KType
tWobbly :: Name -> Type
tWobbly n = TypeVarWobbly $ TypeVar n KType

tUnit :: Type
tUnit = tRigid "Unit"
tInt :: Type
tInt = tRigid "Int"
tChar :: Type
tChar = tRigid "Char"
tBool :: Type
tBool = tRigid "Bool"

tList :: Type
tList = TypeVarRigid $ TypeVar "List" (KFunc KType KType)
tListOf :: Type -> Type
tListOf = TypeApp tList
tFunc :: Type
tFunc = TypeVarRigid $ TypeVar "Func" (KFunc KType (KFunc KType KType))

tString :: Type
tString = tListOf tChar


fun :: Type -> Type -> Type
a `fun` b = TypeApp (TypeApp tFunc a) b


stdPreds :: [Qual Pred]
stdPreds = concat $ fmap unpack (M.toList stdClasses) where
  unpack (_, (Class _ insts)) = (S.toList insts)
ofClass :: Name -> Set (Qual Pred)
ofClass n = S.fromList $ Prelude.filter (\(_ :=> IsIn k _) -> k == n) stdPreds
envPart :: b -> [Char] -> ([Char], b, Set (Qual Pred))
envPart s n = (n, s, ofClass n)


num :: Class
num = Class S.empty $ S.fromList
  [ [] :=> IsIn "Num" tInt
  ]

eq :: Class
eq = Class S.empty $ S.fromList
  [ [] :=> IsIn "Eq" tInt
  , [] :=> IsIn "Eq" tChar
  , [] :=> IsIn "Eq" tBool
  , [IsIn "Eq" (tWobbly "A")] :=> IsIn "Eq" (tListOf (tWobbly "A"))
  ]

ord :: Class
ord = Class (S.singleton "Eq") $ S.fromList
  [ [] :=> IsIn "Ord" tInt
  , [] :=> IsIn "Ord" tBool
  , [] :=> IsIn "Ord" tChar
  , [IsIn "Ord" (tWobbly "A")] :=> IsIn "Ord" (tListOf (tWobbly "A"))
  ]

isString :: Class
isString = Class S.empty $ S.fromList
  [ [] :=> IsIn "IsString" tString
  ]


stdNumClasses :: Map Name Class
stdNumClasses = M.fromList
  [ "Num" <~ num
  ]


stdClasses :: Map Name Class
stdClasses = M.fromList
  [ "Eq" <~ eq
  , "Ord" <~ ord
  , "IsString" <~ isString
  ] `M.union` stdNumClasses


stdDefaults :: Map Name [Type]
stdDefaults = M.map (Prelude.map (\tn -> TypeVarRigid $ TypeVar tn KType)) $ M.fromList
  [ "Num" <~ ["Int"]
  ]


stdTypeEnv :: TypeEnv
stdTypeEnv = TypeEnv $ M.fromList
 [ "eq" <~ quantify [TypeVar "~E" KType] ([IsIn "Eq" $ tWobbly "~E"] :=>
                                          fun (tWobbly "~E")
                                          (fun (tWobbly "~E") tBool)
                                         )
  , "plusInt" <~ Forall [] ([] :=> fun tInt (fun tInt tInt))
 ]


stdKindspace :: Kindspace
stdKindspace = Kindspace $ fmap toKindVar $ M.fromList
  [ "Bool" <~ KType
  , "Int" <~ KType
  , "Func" <~ KFunc KType (KFunc KType KType)
  ]


stdClassEnv :: ClassEnv
stdClassEnv = ClassEnv stdClasses stdDefaults
