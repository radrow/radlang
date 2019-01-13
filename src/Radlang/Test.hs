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



sample :: Program
sample = [rdl|

newtype Option (~A : Type) := None | Some ~A;;

newtype Bool := True | False;;
newtype Pair (~A : Type) (~B : Type) := Pair ~A ~B;;
newtype List (~A : Type) := Nil | Cons ~A (List ~A);;

newtype Void := Void;;

newtype StateT (~S : Type) (~M : Type -> Type) (~A : Type) :=
   State (~S -> ~M (Pair ~S ~A))
;;

interface Semigroup (~A : Type) {
  plus : ~A -> ~A -> ~A;;
};;

impl Int for Semigroup {
  plus := plusInt;;
};;


impl ~A is Semigroup :- Option ~A for Semigroup {
  plus (Some a) (Some b) := Some (plus a b);;
  plus _ _ := None;;
};;

interface Monad (~M : Type -> Type) {
  pure : ~A -> ~M ~A;;
  bind : ~M ~A -> (~A -> ~M ~B) -> ~M ~B;;
};;

-- a : Option Int;;
a := Some (plusInt 3 2);;

l := Cons 2 (Cons 4 Nil);;

m : ~M is Monad :- Int -> ~M Int;;
m x := bind (m x) pure;;

|]

tt :: IO (Either ErrMsg TypeEnv)
tt = typecheck (TypecheckerConfig True) sample
