{-# LANGUAGE QuasiQuotes #-}

module TT where

import Radlang.Typechecker
import Radlang.Parser
import Radlang.Helpers
import Radlang.Desugar
import Radlang.Types
import Radlang.Error

import Text.RawString.QQ
import Control.Monad.Except
import Data.Bifunctor


runString :: String -> IO (Either ErrMsg TypeEnv)
runString s = let res = do
                    parsed <- parseProgram "test" s
                    buildProgram parsed
  in join <$> traverse (typecheck (TypecheckerConfig True)) res


fails :: (String, String) -> IO ()
fails (n, s) = runString s >>= \case
  Left e -> putStrLn $ n <> "\tFailed as expected with " <> showErrorType e
  Right te -> putStrLn $ n <> "\tWtf, should fail got: \n" <> show te <> "\n"


pass :: (String, String) -> IO ()
pass (n, s) = runString s >>= \case
  Right _ -> putStrLn $ n <> "\tPassed as expected."
  Left e -> putStrLn $ n <> "\tWtf, should pass got: \n" <> showError e <> "\n"

pref :: [Char]
pref = [r|

newtype Bool := True | False;;
newtype Option (~A : Type) := Some ~A | None;;
newtype Pair (~A : Type) (~B : Type) := Pair ~A ~B;;
newtype Wrap (~W : Type -> Type) (~A : Type) := Wrap (~W ~A);;

interface Id (~A : Type) {
  id : ~A -> ~A;;
};;


impl Int for Id {
 id x := x;;
};;

impl Bool for Id {
 id True := False;;
 id False := True;;
};;

impl ~A is Id, ~B is Id :- Pair ~A ~B for Id {
  id (Pair a b) := Pair (id a) (id b);;
};;

t := True;;

f : ~A is Id :- ~A -> Pair Int ~A;;
f a := id (Pair (id 3) (id a));;

g a := id (Pair (id 3) (id a));;

h : Option (Pair Int (Pair Int Bool));;
h := Some (f (g True));;

i := Some (f (g True));;

rec1 := rec2;;
rec2 := rec1;;

comp f g x := f (g x);;

interface Good (~A : Type) {
  good : ~A -> Bool;;
};;

interface GoodId (~A : Type) implies Id, Good {
  goodId : ~A -> Bool;;
};;

impl ~A is Good, ~A is Id :- ~A for GoodId {
  goodId := comp good id;;
};;

impl Bool for Good {
  good := id;;
};;

impl ~A is Good :- Pair ~A ~B for Good {
  good (Pair a b) := good a;;
};;

aaa : ~A is GoodId :- ~A -> ~A -> Bool;;
aaa f g := id (good (id (Pair (id f) (id g))));;

cas x := match x with
  | None -> 0
  | Some 2 -> 1
  | _ -> 3
  ;;

takiesame := if (eq 3 3) then 1 else 2;;

lt :=
  let x :=
    let x := 3
      | x : Int
    in True
  in let x := Some False in x;;


interface Monad (~M : Type -> Type) {
  bind : ~M ~A -> (~A -> ~M ~B) -> ~M ~B;;
};;

impl Option for Monad {
  bind (Some x) f := f x;;
  bind None _ := None;;
};;

ffrr := for
{ s <- Some 3
| if eq s 3 then None else Some 1
} None;;


|]


testGood :: IO ()
testGood = void $ pass ("Prefix", pref)

testBad :: IO ()
testBad = void $ traverse fails bad

bad :: [([Char], [Char])]
bad = fmap (second (pref <>))
  [ "notInst" <~ "t : Option Int;; t := id None;;"
  , "notInstGen1" <~ "t : ~A -> Option ~A;; t := comp id Some;;"
  , "notInstGen2" <~ "t : ~A -> Option ~A;; t := comp Some id;;"
  , "noSuchClass" <~ "t : ~A is Dupalala :- ~A;;"
  , "noSuchClassInst" <~ "impl ~A for Dupalala {};;"
  , "implNonexistentMethod" <~ "impl Int for Good { dupalala := 3;; };;"
  , "implBadTypeMethod1" <~ "impl Int for Good { good a b c := True;; };;"
  , "implBadTypeMethod2" <~ "impl Int for Good { good x := x;; };;"
  , "implBadTypeMethod3" <~ "impl Int for Good { good True := True;; };;"
  , "implBadTypeMethod4" <~ "impl Int for Good { good := True;; };;"
  , "occurCheck" <~ "o := o o;;"
  , "tooManyArgs" <~ "o : Int -> Int;; o 1 2 3 := 3;;"
  , "badPatternType" <~ "o : Int -> Int;; o (Some 3) := 3;;"
  , "badForYield" <~ "o := for {} x <- None;;"
  , "nonMonadFor" <~ "o := for {x <- 4} 3;;"
  , "mixedContextFor" <~ [r|newtype Option2 (~A : Type) := Some2 ~A | None2;;
                           impl Option2 for Monad {};;
                           o := for {x <- Some 1 | y <- Some2 2} None;;
                           |]
  , "shadowLet" <~ "o : Int;; o := let x := 3 in let x := True in x;;"
  , "shadowLet2" <~ "o : Bool;; o := let x := let x := True in 2 in x;;"
  , "overlappingPatterns" <~ "o a a := a;;"
  , "overlappingPatterns2" <~ "o (Some a) (Some a) := a;;"
  ]


