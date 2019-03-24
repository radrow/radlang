{-# LANGUAGE QuasiQuotes #-}
module Radlang.Intro(primitiveSpace, withIntro) where

import qualified Data.Map as M

import Radlang.Types
import Radlang.Typedefs
import Radlang.Typesystem.Typesystem
import Radlang.QQ
import Radlang.Error
import Radlang.Evaluator
import Radlang.Desugar

func2 :: Name -> (Data -> Data -> Evaluator Data) -> StrictData
func2 name f2 = DataFunc name $ \a1 ->
  pure $ Strict $ DataFunc (name <> "#2") $ \a2 -> f2 a1 a2


strictFunc2 :: Name -> (StrictData -> StrictData -> Evaluator Data) -> StrictData
strictFunc2 name sf2 = DataFunc name $ \a1 ->
  pure $ Strict $ DataFunc (name <> "#2") $ \a2 -> do
  a1f <- force a1
  a2f <- force a2
  sf2 a1f a2f

primitives :: [(Name, Qual Type, StrictData)]
primitives =
  [ ("plusInt"
    , [] :=> fun tInt (fun tInt tInt)
    , strictFunc2 "plusInt" $ \(DataInt a) (DataInt b) -> pure $ Strict $ DataInt (a + b)
    )
  , ("negInt"
    , [] :=> fun tInt tInt
    , DataFunc "negInt" $ \a -> force a >>= \(DataInt af) -> pure $ Strict $ DataInt (-af)
    )
  , ("mulInt"
    , [] :=> fun tInt (fun tInt tInt)
    , strictFunc2 "mulInt" $ \(DataInt a) (DataInt b) -> pure $ Strict $ DataInt (a * b)
    )
  , ("divInt"
    , [] :=> fun tInt (fun tInt tInt)
    , strictFunc2 "plusInt" $ \(DataInt a) (DataInt b) ->
        if b == 0 then runtimeError "Division by zero"
        else pure $ Strict $ DataInt (a `div` b)
    )
  , ("eqInt"
    , [] :=> fun tInt (fun tInt tBool)
    , strictFunc2 "eqInt" $ \(DataInt a) (DataInt b) ->
        pure $ Strict $ DataADT (if a == b then "True" else "False") []
    )

  , ( "if"
    , [] :=> fun tBool (fun (tWobbly "~A") (fun (tWobbly "~A") (tWobbly "~A")))
    , DataFunc "if expression" $ \bb -> force bb >>= \(DataADT b []) ->
        pure $ Strict $ DataFunc "if#true" $ \onTrue ->
        pure $ Strict $ DataFunc "if#false" $ \onFalse ->
        pure $ if b == "True" then onTrue else onFalse
    )
  , ( "withForced"
    , [] :=> fun (tWobbly "~A") (fun (tWobbly "~B") (tWobbly "~B"))
    , DataFunc "manual force" $ \a ->
        force a >> pure (Strict $ DataFunc "return after manual force" pure)
    )
  , ( "withDeepForced"
    , [] :=> fun (tWobbly "~A") (fun (tWobbly "~B") (tWobbly "~B"))
    , DataFunc "manual deep force" $ \a ->
        deepForce a >> pure (Strict $ DataFunc "return after manual deep force" pure)
    )
  ]


intro :: Program
intro = either (error . showError) id $ buildProgram [rawrdl|
newtype List (~A : Type) := Nil | Cons ~A (List ~A);;
newtype Pair (~A : Type) (~B : Type) := Pair ~A ~B;;
newtype Bool := True | False;;
newtype Option (~A : Type) := None | Some ~A;;

bot : ~A;;
id t := t;;
const c _ := c;;
minusIntTets test:= id test;;
minusInt a b := plusInt a (negInt b);;
fix f := let x := f x in x;;

|]

primitiveSpace :: (Namespace, M.Map DataId Data, TypeEnv)
primitiveSpace = foldr folder (M.empty, M.empty, TypeEnv M.empty) primitives where
  folder (name, typ, def) (ns, ds, ts) =
    let nextId = -(M.size ns) - 1 -- FIXME ANDRZEJ TO JEBNIE
    in ( M.insert name nextId ns
       , M.insert nextId (Strict def) ds
       , TypeEnv $ M.insert name (quantifyAll typ) (types ts))

mergeClassEnv :: ClassEnv -> ClassEnv -> ClassEnv
mergeClassEnv c1 c2 = ClassEnv
  { classes = M.union (classes c1) (classes c2)
  , defaults = M.union (defaults c1) (defaults c2)
  }

mergePrograms :: Program -> Program -> Program
mergePrograms r1 r2 = Program
 { prgBindings = prgBindings r2 ++ prgBindings r1
 , prgClassEnv = prgClassEnv r1 `mergeClassEnv` prgClassEnv r2
 , prgTypeEnv = TypeEnv $ M.union (types $ prgTypeEnv r1) (types $ prgTypeEnv r2)
 , prgNamespace = M.union (prgNamespace r1) (prgNamespace r2)
 , prgDataspace = Dataspace
   { _dsMap = M.union (_dsMap $ prgDataspace r1) (_dsMap $ prgDataspace r2)
   , _dsIdSupply = _dsIdSupply (prgDataspace r1) + _dsIdSupply (prgDataspace r2)
   }
 }

withIntro :: Program -> Program
withIntro p =
  let (_, _, ts) = primitiveSpace
      merged = mergePrograms p intro
  in merged {prgTypeEnv = TypeEnv $ M.union (types $ prgTypeEnv merged) (types ts)}
