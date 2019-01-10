{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE QuasiQuotes #-}

module Radlang.Test where

-- import Radlang.Typechecker
import Radlang.Types


-- import Radlang.ClassEnvBuild
import Radlang.QQ
import Radlang.Kindchecker

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

newtypeProgram :: RawProgram
newtypeProgram = [rawrdl|newtype Option (~A : Type) := None | Some ~A;;

newtype Pair (~A : Type) (~B : Type) := Pair ~A ~B;;
newtype Func (~A : Type) (~B : Type) := Func ~A ~B;;

newtype Void := Void;;

newtype StateT (~S : Type) (~M : Type -> Type) (~A : Type) :=
  State (~S -> ~M (Pair ~S ~A))
;;

interface Monad (~A : Type -> Type) {};;

x : ~M is Monad :- ~M Void;;
x := x;;
|]

ntt :: RawProgram
ntt = [rawrdl|newtype Dup (~A : Type) (~B : Type -> Type) := A (~B ~A);;
|]

dec :: RawProgram
dec = [rawrdl|x : ~A ~A;;|]


-- rawclasses :: [ClassDef]
-- rawclasses = rawprgClassDefs classProgram
rawimpls :: [ImplDef]
rawimpls = rawprgImplDefs classProgram

-- classenv :: Either ErrMsg ClassEnv
-- classenv = buildClassEnv rawclasses rawimpls
