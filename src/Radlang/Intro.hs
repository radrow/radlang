{-# LANGUAGE StrictData #-}
{-# LANGUAGE QuasiQuotes #-}
-- |Standard library, prelude, invocation – call it whatever you like,
--for me it is "intro"
module Radlang.Intro(primitiveSpace, withIntro) where

import qualified Data.Text as T
import Control.Monad
import Control.Monad.Except
import Data.Functor
import Data.Char as DC
import qualified Data.Map                      as M

import           Radlang.Error
import           Radlang.Evaluator
import           Radlang.QQ
import           Radlang.Typedefs
import           Radlang.Types
import           Radlang.Typesystem.Typesystem
import           Radlang.EvaluationUtils


makeBool :: Bool -> StrictData
makeBool t = DataADT (T.pack $ show t) []


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
    , strictFunc2 "divInt" $ \(DataInt a) (DataInt b) ->
        if b == 0 then runtimeError "Division by zero"
        else pure $ Strict $ DataInt (a `div` b)
    )
  , ("eqInt"
    , [] :=> fun tInt (fun tInt tBool)
    , strictFunc2 "eqInt" $ \(DataInt a) (DataInt b) ->
        pure $ Strict $ makeBool (a == b)
    )
  , ("eqChar"
    , [] :=> fun tChar (fun tChar tBool)
    , strictFunc2 "eqChar" $ \(DataChar a) (DataChar b) ->
        pure $ Strict $ makeBool (a == b)
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
  , ( "error"
    , [] :=> (fun (tWobbly "~A") (tWobbly "~B"))
    , DataFunc "error" $ \a ->
        deepForce a >>= \d -> runtimeError ("thrown by the user: " <> T.pack (show d))
    )
  , ( "catch"
    , [] :=> fun (tWobbly "~A") (fun (tWobbly "~A") (tWobbly "~A"))
    , func2 "catch" $ \d c -> fmap Strict $ catchError (force d) (const $ force c)
    )
  ]

extendedPrimitives :: [(Name, Qual Type, StrictData)]
extendedPrimitives = primitives ++
  [ ( "bruteEq"
    , [] :=> fun (tWobbly "~A") (fun (tWobbly "~A") tBool)
    , strictFunc2 "bruteEq" $
      let cmp a b = case (a, b) of
                    (DataInt q, DataInt w) -> pure . Strict $ makeBool (q == w)
                    (DataChar q, DataChar w) -> pure . Strict $ makeBool (q == w)
                    (DataADT q ql, DataADT w wl) -> do
                      blsD <- mapM (\(x, y) -> do
                                       xx <- force x
                                       yy <- force y
                                       cmp xx yy >>= force) (zip ql wl)
                      let bls = blsD <&> (\(DataADT bb []) -> bb == "True")
                      pure . Strict $ makeBool ((q == w) && (length ql == length wl) && and bls)
                    _ -> runtimeError $ "Invalid comparison: " <> T.pack (show a) <> " == " <> T.pack (show b)
          cmp :: StrictData -> StrictData -> Evaluator Data
      in cmp
    )
  , ( "charToInt"
    , [] :=> fun tChar tInt
    , DataFunc "charToInt" $ \d -> force d >>= \(DataChar c) -> pure $ Strict $ DataInt (DC.ord c)
    )
  , ( "isDigit"
    , [] :=> fun tChar tBool
    , DataFunc "isDigit" $ \d -> force d >>= \(DataChar c) ->
        pure $ Strict $ makeBool (c >= '0' && c <= '9')
    )
  , ( "isLower"
    , [] :=> fun tChar tBool
    , DataFunc "charToInt" $ \d -> force d >>= \(DataChar c) ->
        pure $ Strict $ makeBool (c >= 'a' && c <= 'z')
    )
  , ( "isUpper"
    , [] :=> fun tChar tBool
    , DataFunc "charToInt" $ \d -> force d >>= \(DataChar c) ->
        pure $ Strict $ makeBool (c >= 'A' && c <= 'Z')
    )
  , ( "isWhite"
    , [] :=> fun tChar tBool
    , DataFunc "charToInt" $ \d -> force d >>= \(DataChar c) ->
        pure $ Strict $ makeBool (c `elem` (" \t\n" :: String))
    )
  , ( "readInt"
    , [] :=> fun (tListOf tChar) tInt
    , DataFunc "readInt" $ \l -> do
        ll <- deepForce l
        case ll of
          (DataADT "Nil" []) -> runtimeError "Empty input for int read"
          _ -> let go (DataADT "Nil" _) acc = acc
                   go (DataADT "Cons" [Strict (DataChar c), Strict next]) acc =
                     go next (acc * 10 + DC.ord c - DC.ord '0')
                   go _ _ = wtf "readInt exploit"
               in pure $ Strict $ DataInt $ go ll 0
    )
  ]


-- |Spaces that include all primitives
primitiveSpace :: (M.Map Name Data, TypeEnv)
-- primitiveSpace = (M.empty, TypeEnv M.empty)
primitiveSpace = foldr folder (M.empty, TypeEnv M.empty) extendedPrimitives where
  folder (name, typ, def) (ps, ts) =
    ( M.insert name (Strict def) ps
    , TypeEnv $ M.insert name (quantifyAll typ) (types ts))


-- |Library that will be included as a prelludium to any user's program
intro :: RawProgram
intro = [rawrdl|
newtype List (~A : Type) := Nil | Cons ~A (List ~A);;
newtype Pair (~A : Type) (~B : Type) := Pair ~A ~B;;
newtype Bool := True | False;;
newtype Option (~A : Type) := None | Some ~A;;

head (Cons h _) := h;;
tail (Cons _ t) := t;;

bot : ~A;;
id t := t;;
const c _ := c;;
minusInt a b := plusInt a (negInt b);;

fix : (~A -> ~A) -> ~A;;
-- fix f := let x := f x in x;;

or False False := False;;
or _ _ := True;;

and True True := True;;
and _ _ := False;;

forced a := withForced a a;;
deepForced a := withDeepForced a a;;
|]


-- |Merge two programs. Currently used only here to add Intro.
mergePrograms :: RawProgram -> RawProgram -> RawProgram
mergePrograms r1 r2 = RawProgram
  { rawprgNewTypes = rawprgNewTypes r1 ++ rawprgNewTypes r2
  , rawprgTypeDecls = rawprgTypeDecls r1 ++ rawprgTypeDecls r2
  , rawprgDataDefs = rawprgDataDefs r1 ++ rawprgDataDefs r2
  , rawprgInterfaceDefs = rawprgInterfaceDefs r1 ++ rawprgInterfaceDefs r2
  , rawprgImplDefs = rawprgImplDefs r1 ++ rawprgImplDefs r2
  }


-- |Extend program with Intro
withIntro :: RawProgram -> RawProgram
withIntro = flip mergePrograms intro
-- withIntro = id
