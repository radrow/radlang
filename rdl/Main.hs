module Main where

import System.Environment
import System.IO

import Radlang
import Radlang.Error
import Radlang.Types
import Radlang.Intro
import Radlang.InterfaceResolve

main :: IO ()
main = do
  args <- getArgs
  (fileName, sourceCode) <-
        if null args
        then (,) "<stdin>" <$> getContents
        else (,) (head args) <$> readFile (head args)
  let result = do
        rprg <- parseRDL fileName sourceCode
        uprg <- buildProgram $ withIntro rprg
        tprg <- typecheck (TypecheckerConfig True) uprg
        prg <- runResolver (resolveProgram tprg)
        runProgram prg
  case result of
    Left e -> hPutStrLn stderr $ showError e
    Right d -> print d
