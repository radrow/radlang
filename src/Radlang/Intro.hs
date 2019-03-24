{-# LANGUAGE QuasiQuotes #-}
-- |Standard library, prelude, invocation – call it whatever you like,
--for me it is "intro"
module Radlang.Intro(primitiveSpace, withIntro) where

import qualified Data.Map                      as M

import           Radlang.ClassEnvBuild         (mergeClassEnv)
import           Radlang.Desugar
import           Radlang.Error
import           Radlang.Evaluator
import           Radlang.QQ
import           Radlang.Typedefs
import           Radlang.Types
import           Radlang.Typesystem.Typesystem


-- |Lift 2 argumented function from Haskell into Radlang
func2 :: Name -> (Data -> Data -> Evaluator Data) -> StrictData
func2 name f2 = DataFunc (name <> "#0") $ \a1 ->
  pure $ Strict $ DataFunc (name <> "#1") $ \a2 -> f2 a1 a2


-- |Same as 'func2', but with strict arguments
strictFunc2 :: Name -> (StrictData -> StrictData -> Evaluator Data) -> StrictData
strictFunc2 name sf2 = DataFunc (name <> "#0") $ \a1 ->
  pure $ Strict $ DataFunc (name <> "#1") $ \a2 -> do
  a1f <- force a1
  a2f <- force a2
  sf2 a1f a2f


-- |Primitive functions that cannot be defined within the language
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
    , DataFunc "if expression" $ \bb -> force bb >>= \(DataADT b []) -> pure $ Strict $
        func2 "if evaluation" $ \onTrue onFalse ->
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


-- |Spaces that include all primitives
primitiveSpace :: (Namespace, M.Map DataId Data, TypeEnv)
primitiveSpace = foldr folder (M.empty, M.empty, TypeEnv M.empty) primitives where
  folder (name, typ, def) (ns, ds, ts) =
    let nextId = -(M.size ns) - 1 -- FIXME ANDRZEJ TO JEBNIE
    in ( M.insert name nextId ns
       , M.insert nextId (Strict def) ds
       , TypeEnv $ M.insert name (quantifyAll typ) (types ts))


-- |Library that will be included as a prelludium to any user's program
intro :: Program
intro = either (error . showError) id $ buildProgram [rawrdl|
newtype List (~A : Type) := Nil | Cons ~A (List ~A);;
newtype Pair (~A : Type) (~B : Type) := Pair ~A ~B;;
newtype Bool := True | False;;
newtype Option (~A : Type) := None | Some ~A;;

head (Cons h _) := h;;
bot : ~A;;
id t := t;;
const c _ := c;;
minusInt a b := plusInt a (negInt b);;
fix f := let x := f x in x;;

tail (Cons _ t) := t;;

or False False := False;;
or _ _ := True;;

and True True := True;;
and _ _ := False;;

forced a := withForced a a;;
deepForced a := withDeepForced a a;;
|]


-- |Merge two programs. Currently used only here to add Intro.
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


-- |Extend program with Intro
withIntro :: Program -> Program
withIntro p =
  let (_, _, ts) = primitiveSpace
      merged = mergePrograms p intro
  in merged {prgTypeEnv = TypeEnv $ M.union (types $ prgTypeEnv merged) (types ts)}