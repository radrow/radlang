-- |Debug only
{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE QuasiQuotes #-}


module Radlang.Test where

import qualified Data.Map as M

import qualified Data.Text as T
import Radlang.Types
import Radlang.Parser
import Radlang.Desugar
import Radlang.Typechecker
import Radlang.Pretty
import Radlang.InterfaceResolve
import Radlang.Intro


printTypeEnv :: TypeEnv -> String
printTypeEnv (TypeEnv te) =
  let l :: [(T.Text, TypePoly)]
      l = M.toList te
  in
  unlines $ fmap (\(v, t) -> T.unpack v <> " : " <> show t) l

ttest :: FilePath -> IO ()
ttest fl = readFile ("examples/" <> fl <> ".rdl") >>= \f -> either (putStrLn . Prelude.show) (putStrLn . prettyBnds 0 . tprgBindings) $ parseRDL "XD" f >>= buildProgram . withIntro >>= typecheck (TypecheckerConfig True)
ptest :: FilePath -> IO ()
ptest fl = readFile ("examples/" <> fl <> ".rdl") >>= \f -> either (putStrLn . Prelude.show) (putStrLn . prettyPBnds . tprgPolyBindings) $ parseRDL "XD" f >>= buildProgram . withIntro >>= typecheck (TypecheckerConfig True)
etest :: FilePath -> IO ()
etest fl = readFile ("examples/" <> fl <> ".rdl") >>= \f -> either (putStrLn . Prelude.show) (putStrLn . prettyBndsKok 0) $ do
  parsed <- parseRDL "XD" f
  built <- buildProgram . withIntro $ parsed
  tched <- typecheck (TypecheckerConfig True) $ built
  prgBindings <$> resolveProgram tched
rtest :: FilePath -> IO ()
rtest fl = readFile ("examples/" <> fl <> ".rdl") >>= \f -> either (putStrLn . Prelude.show) (putStrLn . prettyBndsE 0 . M.unions . (fmap $ \(_, _, is) -> M.unions is) . uprgBindings) $ parseRDL "XD" f >>= buildProgram . withIntro
