{-# LANGUAGE OverloadedLists #-}
-- |Collection of some useful aliasses and predefined environments
module Radlang.Typedefs where

import           Data.Text as T
import           Data.Map.Strict       as M
import           Data.Set              as S

import           Radlang.Kindchecker
import           Radlang.Types


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
stdPreds = Prelude.concat $ fmap unpackPreds (M.toList stdInterfaces) where
  unpackPreds (_, (Interface _ insts)) = (S.toList insts)
ofInterface :: Name -> Set (Qual Pred)
ofInterface n = S.fromList $ Prelude.filter (\(_ :=> IsIn k _) -> k == n) stdPreds
envPart :: b -> [Char] -> ([Char], b, Set (Qual Pred))
envPart s n = (n, s, ofInterface $ T.pack n)


num :: Interface
num = Interface S.empty $ S.fromList
  [ [] :=> IsIn "Num" tInt
  ]

eq :: Interface
eq = Interface S.empty $ S.fromList
  [ [] :=> IsIn "Eq" tInt
  , [] :=> IsIn "Eq" tChar
  , [] :=> IsIn "Eq" tBool
  , [IsIn "Eq" (tWobbly "A")] :=> IsIn "Eq" (tListOf (tWobbly "A"))
  ]

ord :: Interface
ord = Interface (S.singleton "Eq") $ S.fromList
  [ [] :=> IsIn "Ord" tInt
  , [] :=> IsIn "Ord" tBool
  , [] :=> IsIn "Ord" tChar
  , [IsIn "Ord" (tWobbly "A")] :=> IsIn "Ord" (tListOf (tWobbly "A"))
  ]

isString :: Interface
isString = Interface S.empty $ S.fromList
  [ [] :=> IsIn "IsString" tString
  ]


(<~) :: a -> b -> (a, b)
(<~) = (,)

stdNumInterfaces :: Map Name Interface
stdNumInterfaces = M.fromList
  [ "Num" <~ num
  ]


stdInterfaces :: Map Name Interface
stdInterfaces = M.fromList
  [ "Eq" <~ eq
  , "Ord" <~ ord
  , "IsString" <~ isString
  ] `M.union` stdNumInterfaces


stdDefaults :: Map Name [Type]
stdDefaults = M.map (Prelude.map (\tn -> TypeVarRigid $ TypeVar tn KType)) $ M.fromList
  [ "Num" <~ ["Int"]
  ]

stdKindspace :: Kindspace
stdKindspace = Kindspace $ fmap toKindVar $ M.fromList
  [ "Int" <~ KType
  , "Char" <~ KType
  , "Func" <~ KFunc KType (KFunc KType KType)
  ]


stdInterfaceEnv :: InterfaceEnv
stdInterfaceEnv = InterfaceEnv stdInterfaces stdDefaults
