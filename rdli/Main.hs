module Main where

import Control.Monad
import System.IO

import Radlang

main :: IO ()
main = forever $ do
  line <- getLine
  let result = do
        e <- parseProgram "interactive" line
        -- case typeErrors p of
        --   Nothing -> return ()
        --   Just e -> Left e
        evalProgram e
  case result of
    Left e -> hPutStrLn stderr e
    Right r -> putStrLn $ show r
