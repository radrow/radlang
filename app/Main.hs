module Main where

import System.Environment
import System.IO

import Radlang(parseProgram)

f = parseProgram

main :: IO ()
main = putStrLn f
  -- args <- getArgs
  -- (fileName, sourceCode) <-
  --       if null args
  --       then (,) "<stdin>" <$> getContents
  --       else (,) (head args) <$> readFile (head args)
  -- let result = do
  --       (ProgramTree p) <- parse fileName sourceCode
  --       case typeErrors p of
  --         Nothing -> return ()
  --         Just e -> Left e
  --       evalProgram p
  -- case result of
  --   Left e -> hPutStrLn e
  --   Right r -> putStrLn r
