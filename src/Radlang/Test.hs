{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE QuasiQuotes #-}


module Radlang.Test where

import qualified Data.Map as M

import System.IO.Unsafe
import Radlang.Types
import Radlang.Parser
import Radlang.Desugar
import Radlang.Typechecker
import Radlang.Pretty
import Radlang.InterfaceResolve

-- tt :: IO ()
-- tt = runTypecheckerT $ void . inferTypeExpr $
--   Application (Application (Val "eq") (Lit $ LitString "")) (Lit $ LitInt 3)

-- test :: IO ()
-- test = do
--   f <- readFile "examples/toplevel.rdl"
--   testt f


printTypeEnv :: TypeEnv -> String
printTypeEnv (TypeEnv te) =
  let l :: [(String, TypePoly)]
      l = M.toList te
  in
  unlines $ fmap (\(v, t) -> v <> " : " <> show t) l




-- sample :: Program
-- sample = [rdl|

-- newtype Option (~A : Type) := None | Some ~A;;

-- newtype Bool := True | False;;
-- newtype Pair (~A : Type) (~B : Type) := Pair ~A ~B;;
-- newtype List (~A : Type) := Nil | Cons ~A (List ~A);;

-- newtype Void := Void;;

-- newtype StateT (~S : Type) (~M : Type -> Type) (~A : Type) :=
--    State (~S -> ~M (Pair ~S ~A))
-- ;;

-- interface Semigroup (~A : Type) {
--   plus : ~A -> ~A -> ~A;;
-- };;

-- impl Int for Semigroup {
--   plus := plusInt;;
-- };;


-- impl ~A is Semigroup :- Option ~A for Semigroup {
--   plus (Some a) (Some b) := Some (plus a b);;
--   plus _ _ := None;;
-- };;

-- interface Monad (~M : Type -> Type) {
--   pure : ~A -> ~M ~A;;
--   bind : ~M ~A -> (~A -> ~M ~B) -> ~M ~B;;
-- };;

-- a : Option Int;;
-- a := Some (plusInt 3 2);;

-- l := Cons 2 (Cons 4 Nil);;

-- m : ~M is Monad :- Int -> ~M Int;;
-- m x := bind (m x) pure;;

-- |]

-- mini :: TypedProgram
-- mini = [trdl|
-- newtype Bool := True | False;;
-- iff True a _ := a;;
-- iff False _ b := b;;

-- const a _ := a;;
-- main := plusInt 1 2;;

-- |]

-- runPrg tp = let (res, ds) = run (TypedLet (tprgBindings tp) (TypedVal "main"))
--   in putStrLn (either showError show res) >> (putStrLn $ "\n" ++ show ds)
-- runPrg tp =
--   let mock = TypedLet (tprgBindings tp) (TypedVal "main")
--       (ns, ds, _) = primitiveSpace
--       res = runEvaluator ns ds (TypeEnv M.empty) $ eval mock >>= force
--    in putStrLn (either showError show res) >> (putStrLn $ "\n" ++ show ds)

-- tt :: IO (Either ErrMsg TypeEnv)
-- tt = typecheck (TypecheckerConfig True) sample
printEither :: Show a => Either a TypedProgram -> String
printEither (Left e) = show e
printEither (Right r) = prettyBnds 0 $ tprgBindings r


ttest = readFile "examples/dup.rdl" >>= \f -> either (putStrLn . Prelude.show) (putStrLn . prettyBnds 0 . tprgBindings) $ parseRDL "XD" f >>= buildProgram >>= typecheck (TypecheckerConfig True)
ptest = readFile "examples/dup.rdl" >>= \f -> either (putStrLn . Prelude.show) (putStrLn . prettyPBnds . tprgPolyBindings) $ parseRDL "XD" f >>= buildProgram >>= typecheck (TypecheckerConfig True)
etest = readFile "examples/dup.rdl" >>= \f -> either (putStrLn . Prelude.show) (putStrLn . prettyBndsE 0 . \(_, _, [a]) -> a) $ parseRDL "XD" f >>= buildProgram >>= typecheck (TypecheckerConfig True) >>= \tp -> runResolver (fmap fst (tprgBindings tp) `M.union` fmap fst (tprgPolyBindings tp)) (fmap fst $ resolveAssgs $ tprgBindings tp)
