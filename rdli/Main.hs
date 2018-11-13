{-#LANGUAGE LambdaCase#-}
module Main where

import Data.Char
import Data.List(find, isPrefixOf)
import Control.Monad
import System.Exit
import System.IO

import Radlang

data Action
  = Eval
  | Typecheck
  | Quit

commandMap :: [(String, Action)]
commandMap =
  [ (":t", Typecheck)
  , (":type", Typecheck )
  , (":q", Quit)
  , (":quit", Quit)
  ]

processLine :: String -> (Action, String)
processLine l = case find (\(s, _) -> isPrefixOf s l) commandMap of
  Just (s, a) -> (a, dropWhile (isSpace) $ drop (length s) l)
  Nothing -> (Eval, dropWhile (isSpace) l)

printResult :: Either ErrMsg String -> IO ()
printResult = \case
  Right r -> putStrLn r
  Left e -> hPutStrLn stderr e

main :: IO ()
main = forever $ do
  hPutStr stderr "RDL: "
  hFlush stderr
  lineRead <- getLine
  let (action, line) = processLine lineRead
  unless (all isSpace lineRead) $
    case action of
      Eval -> printResult $ do
        e <- parseProgram "interactive" line
        void $ typecheck e
        d <- evalProgram e
        pure $ show d
      Typecheck -> printResult $ do
        e <- parseProgram "interactive" line
        t <- typecheck e
        pure $ show t
      Quit -> hPutStrLn stderr "Bye!" >> exitSuccess
