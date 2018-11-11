module Main where

import System.Environment
import System.IO

import Radlang

main :: IO ()
main = do
  args <- getArgs
  (fileName, sourceCode) <-
        if null args
        then (,) "<stdin>" <$> getContents
        else (,) (head args) <$> readFile (head args)
  let result = do
        e <- parseProgram fileName sourceCode
        t <- typecheck e
        d <- evalProgram e
        pure (t, d)
  case result of
    Left e -> hPutStrLn stderr e
    Right (t, d) -> putStrLn $ show d <> " : " <> show t
