{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE QuasiQuotes #-}

module Radlang.Test where

import Radlang.Typechecker
import Radlang.Types
import Radlang.QQ

-- tt :: IO ()
-- tt = runTypecheckerT $ void . inferTypeExpr $
--   Application (Application (Val "eq") (Lit $ LitString "")) (Lit $ LitInt 3)

-- test :: IO ()
-- test = do
--   f <- readFile "examples/toplevel.rdl"
--   testt f


-- printTypeEnv :: TypeEnv -> String
-- printTypeEnv (TypeEnv te) =
--   let l :: [(String, TypePoly)]
--       l = M.toList te
--   in
--   unlines $ fmap (\(v, t) -> v <> " : " <> show t) l


classProgram :: RawProgram
classProgram = [rawrdl|interface Semigroup (~A : Type) {
  plus : ~A -> ~A -> ~A;;
}
;;

interface Monoid (~A : Type) implies Semigroup { -- implication separated by comma
  zero : ~A;;
}
;;

impl Int for Semigroup {
  plus := plusInt;;
};;

impl Int for Monoid {
  zero := 0;;
};;

impl (~A is Semigroup :- Some ~A) for Semigroup {
  plus (Some a) (Some b) := Some (op a b);;
  plus _ _ := None;;
};;

impl (~A is Monoid :- Some ~A) for Monoid {
  zero := Some zero;;
};;
|]

sample :: Program
sample = [rdl|newtype Option (~A : Type) := None | Some ~A;;

newtype Bool := True | False;;
newtype Pair (~A : Type) (~B : Type) := Pair ~A ~B;;
newtype List (~A : Type) := Nil | Cons ~A (List ~A);;

newtype Void := Void;;

newtype StateT (~S : Type) (~M : Type -> Type) (~A : Type) :=
   State (~S -> ~M (Pair ~S ~A))
;;

interface Monad (~A : Type -> Type) {};;

-- a : Option Int;;
a := Some (plusInt 3 2);;

l := Cons 2 (Cons 4 Nil);;

|]

tt :: IO (Either ErrMsg TypeEnv)
tt = typecheck (TypecheckerConfig True) sample
