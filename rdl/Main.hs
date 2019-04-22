module Main where

import System.Environment
import System.IO

import Radlang
import Radlang.Error
import Radlang.Types
import Radlang.Intro

main :: IO ()
main = do
  args <- getArgs
  (fileName, sourceCode) <-
        if null args
        then (,) "<stdin>" <$> getContents
        else (,) (head args) <$> readFile (head args)
  let result = do
        rprg <- parseRDL fileName sourceCode
        prg <- buildProgram $ withIntro rprg
        tprg <- typecheck (TypecheckerConfig True) prg
        runProgram tprg
  case result of
    Left e -> hPutStrLn stderr $ showError e
    Right d -> print d
