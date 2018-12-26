module Radlang.Test where

import Radlang.TypecheckerDebug
import Radlang.Types
import Data.Map.Strict as M
import Text.Megaparsec
import Control.Monad
import Radlang.Parser

-- tt :: IO ()
tt = runTypecheckerT $ execTypeInfer $ void . inferTypeExpr $
  Application (Application (Val "eq") (Lit $ LitString "")) (Lit $ LitInt 3)

test :: IO ()
test = do
  f <- readFile "examples/toplevel.rdl"
  testt f

testt :: String -> IO ()
testt f = case parse (program <* eof) "XD" f of
  Left a -> putStrLn $ parseErrorPretty a
  Right p -> (either id printTypeEnv <$> typecheck (prgBindings p)) >>= putStrLn


printTypeEnv :: TypeEnv -> String
printTypeEnv (TypeEnv te) =
  let l :: [(String, TypePoly)]
      l = M.toList te
  in
  unlines $ fmap (\(v, t) -> v <> " : " <> show t) l
  
