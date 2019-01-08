{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE QuasiQuotes #-}

module Radlang.Test where

import Data.Either
-- import Radlang.Typechecker
import Radlang.Types
import Data.Map.Strict as M
import Text.Megaparsec
import Control.Monad
import Text.RawString.QQ
import Language.Haskell.TH.Quote

import qualified Language.Haskell.TH as TH

import Radlang.Parser
import Radlang.Parser.General
import Radlang.ClassEnvBuild
import Radlang.DependencyAnalysis

-- tt :: IO ()
-- tt = runTypecheckerT $ void . inferTypeExpr $
--   Application (Application (Val "eq") (Lit $ LitString "")) (Lit $ LitInt 3)

-- test :: IO ()
-- test = do
--   f <- readFile "examples/toplevel.rdl"
--   testt f

testpars :: Show a => Parser a -> String -> IO ()
testpars p f = case parse (p <* eof) "XD" f of
  Left a -> putStrLn $ parseErrorPretty a
  Right x -> print x


-- printTypeEnv :: TypeEnv -> String
-- printTypeEnv (TypeEnv te) =
--   let l :: [(String, TypePoly)]
--       l = M.toList te
--   in
--   unlines $ fmap (\(v, t) -> v <> " : " <> show t) l

ast :: QuasiQuoter
ast = QuasiQuoter
  { quoteExp = \str ->  do
      loc <- TH.location
      let pos =  (TH.loc_filename loc,
                   fst (TH.loc_start loc),
                   snd (TH.loc_start loc))
          prs :: Monad m => String -> m RawProgram
          prs = either (fail . parseErrorPretty) pure . parse rawProgram ""
      expr <- prs str
      dataToExpQ (const Nothing) expr
  }

classProgram :: [Char]
classProgram = [r|interface Semigroup ~A {
  plus : ~A -> ~A -> ~A;;
}
;;

interface Monoid ~A implies Semigroup { -- implication separated by comma
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


rawclasses :: [ClassDef]
rawclasses = rawprgClassDefs . either (error . parseErrorPretty) id $ parse rawProgram "" classProgram
rawimpls :: [ImplDef]
rawimpls = rawprgImplDefs . fromRight undefined $ parse rawProgram "" classProgram

classenv :: Either ErrMsg ClassEnv
classenv = buildClassEnv rawclasses rawimpls
