module Main where

import Control.Monad
import System.IO

import Radlang

main :: IO ()
main = forever $ do
  line <- getLine
  let result = do
        e <- parseProgram "interactive" line
        t <- typecheck e
        d <- evalProgram e
        pure (t, d)
  case result of
    Left e -> hPutStrLn stderr e
    Right (t, d) -> putStrLn $ show d <> " : " <> show t
