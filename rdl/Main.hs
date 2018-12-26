module Main where

import System.Environment
import System.IO

import Radlang

main :: IO ()
main = do pure ()
  -- args <- getArgs
  -- (fileName, sourceCode) <-
  --       if null args
  --       then (,) "<stdin>" <$> getContents
  --       else (,) (head args) <$> readFile (head args)
  -- let result = do
  --       e <- parseProgram fileName sourceCode
  --       t <- typecheck e
  --       d <- evalPrintProgram e
  --       pure (t, d)
  -- case result of
  --   Left e -> hPutStrLn stderr e
  --   Right (t, d) -> putStrLn $ d <> " : " <> show t
