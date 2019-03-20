module Main where

import System.Environment
import System.IO
import System.IO.Unsafe

import Radlang
import Radlang.Error
import Radlang.Types

main :: IO ()
main = do
  args <- getArgs
  (fileName, sourceCode) <-
        if null args
        then (,) "<stdin>" <$> getContents
        else (,) (head args) <$> readFile (head args)
  let result = do
        rprg <- parseRDL fileName sourceCode
        prg <- buildProgram rprg
        tprg <- unsafePerformIO $ typecheck (TypecheckerConfig True) prg
        runProgram tprg
  case result of
    Left e -> hPutStrLn stderr $ showError e
    Right d -> print d
