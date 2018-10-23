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
        -- case typeErrors p of
        --   Nothing -> return ()
        --   Just e -> Left e
        evalProgram e
  case result of
    Left e -> hPutStrLn stderr e
    Right r -> putStrLn $ show r
