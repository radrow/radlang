module Main where

import qualified Data.Text as T
import Control.Monad.Except
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
  result <- runExceptT $ do
        liftIO $ putStrLn "Parsing..."
        rprg <- liftEither $ parseRDL fileName sourceCode
        liftIO $ putStrLn "Desugaring..."
        uprg <- liftEither $ buildProgram $ withIntro rprg
        liftIO $ putStrLn "Typechecking..."
        tprg <- liftEither $ typecheck (TypecheckerConfig True) uprg
        liftIO $ putStrLn "Resolving..."
        prg <- liftEither $ resolveProgram tprg
        liftIO $ putStrLn "Running...\n"
        liftEither $ runProgram prg
  case result of
    Left e -> hPutStrLn stderr $ T.unpack $ showError e
    Right d -> print d
