{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeOperators             #-}

module Test where

import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State.Strict
import           Data.Bifunctor
import qualified Data.Map.Strict            as M
import           System.Console.ANSI
import qualified Text.Megaparsec            as MP

import           Radlang.Evaluator
import           Radlang.Parser
import           Radlang.Space
import           Radlang.Stdlib
import           Radlang.Types


evalProgramWithC :: Namespace -> Expr -> Either String Data
evalProgramWithC ns ex = evalState
  (runReaderT
    (runExceptT
      $ registerConstructor "D" 3 >>= \n -> withStdlib $ withNsExpr n ex
    ) ns
  ) (M.empty, 0)


parse :: String -> Either ErrMsg Expr
parse inp = first MP.parseErrorPretty $ MP.parse expr "test" inp

parsePrint :: String -> IO ()
parsePrint inp = case parse inp of
  Right d -> setSGR [SetColor Foreground Vivid Green] >> print d >> setSGR [SetColor Foreground Vivid White]
  Left d -> setSGR [SetColor Foreground Vivid Red] >> putStrLn d >> setSGR [SetColor Foreground Vivid White]



evalE :: String -> Either ErrMsg Data
evalE inp = parse inp >>= evalProgramWithC M.empty

class Testable t where
  test :: t -> Either ErrMsg ()

data Test a b where
  (:==) :: a -> b -> Test a b
  (:/=) :: a -> b -> Test a b
  Failing :: Expr -> Test () Expr

instance Testable (Test Data Expr) where
  test (t :== x) = do
    (d :: Data) <- evalProgram M.empty x
    if t == d
      then return ()
      else throwError (show t <> ":/=" <> show d)
  test (t :/= x) = do
    (d :: Data) <- evalProgram M.empty x
    if t /= d
      then return ()
      else throwError (show t <> ":==" <> show d)
instance Eq a => Testable (Test a a) where
  test (a :== b) = if a == b then Right () else Left "Not equal"
  test (a :/= b) = if a /= b then Right () else Left "Equal"
instance Testable (Test () Expr) where
  test (Failing e) = case evalProgram M.empty e of
    Right _ -> Left "Succeeded"
    Left _  -> Right ()
  test (() :== e) = void $ evalProgram M.empty e
  test (() :/= e) = void $ evalProgram M.empty e
instance Testable (Test Data String) where
  test (d :== s) = case evalE s of
    Left e  -> Left e
    Right r -> if r == d then Right () else Left "Results mismatch"
  test (d :/= s) = case evalE s of
    Left e  -> Left e
    Right r -> if r /= d then Right () else Left "Results match"

data AnyTest = forall a b. Testable (Test a b) => AnyTest (Test a b)

(<==>) :: Testable (Test a b) => a -> b -> AnyTest
a <==> b = AnyTest (a :== b)
(</=>) :: Testable (Test a b) => a -> b -> AnyTest
a </=> b = AnyTest (a :/= b)
failing :: Expr -> AnyTest
failing a = AnyTest (Failing a)

printTest :: String -> AnyTest -> IO ()
printTest name (AnyTest t) = case test t of
  Right _ -> do putStr name
                setSGR [SetColor Foreground Vivid Green]
                putStrLn " passed."
                setSGR [SetColor Foreground Vivid White]

  Left e -> do  putStr name
                setSGR [SetColor Foreground Vivid Red]
                putStrLn " FAILED:"
                setSGR [SetColor Foreground Vivid White]
                putStrLn $ "\t" <> e <> "\n"

testAll :: IO ()
testAll = go testCases where -- `traverse` crashed GHC lol
  go []    = return ()
  go (h:t) = uncurry printTest h >> go t

testCases :: [(Name, AnyTest)]
testCases =
  [ ("trivialTest", DataInt 3 <==> Data (DataInt 3))

  , ("letTest", DataInt 3 <==> Let [("XD", Nothing, Data $ DataInt 3)] (Val "XD"))

  , ("caseTest1", DataInt 42 <==> Case (Data $ DataInt 3) [ (Data $ DataInt 2, Val ":C")
                                                   , (Data $ DataInt 3, Data $ DataInt 42)
                                                   ])
  , ("caseTest2", DataInt 42 <==> Case (Data $ DataInt 42) [ (Data $ DataInt 9, Val ":C")
                                                   , (Val "kek", Val "kek")
                                                   ])

  , ("caseTest3", DataInt 42 <==> Case (Data $ DataADT "D" [DataInt 42])
            [(Application (Val "D") (Data $ DataInt 42), Data $ DataInt 42)])


  , ("caseTest4", DataInt 42 <==> Case (Data $ DataADT "D" [DataInt 42])
            [ (Application (Val "A") (Data $ DataInt 42), Data $ DataInt 0)
            , (Application (Application (Val "D") (Data $ DataInt 0)) (Data $ DataInt 42), Data $ DataInt 42)
            , (Application (Val "D") (Data $ DataInt 42), Data $ DataInt 42)
            ])

  , ("trivialParse", DataInt 42 <==> "42")

  , ("letParse1", DataInt 42 <==> "let x := 42 in x")
  , ("letParse2", DataInt 42 <==> "let x := 0; y := 42 in y")
  , ("letParse3", DataInt 42 <==> "let x := 42; y := 0 in x")
  , ("letParse4", DataInt 42 <==> "let x := 42; y := x in y")
  , ("shadowParse1", DataInt 42 <==> "let x := 0 in let x := 42 in x")
  , ("shadowParse2", DataInt 42 <==> "let x := 2; y := x in let x := 40 in plus x y")

  , ("caseParse1", DataInt 42 <==> "case 5 of 5 -> 42")
  , ("caseParse2", DataInt 42 <==> "case 5 of 3 -> 0 | 5 -> 42")
  , ("caseParse3", DataInt 42 <==> "case 5 of 5 -> 42 | 3 -> 0")
  , ("caseParse4", DataInt 42 <==> "case 42 of 1 -> 0 | n -> n")

  , ("ADTParse", DataADT "D" [DataInt 1, DataInt 2, DataInt 3]
                 <==> "D 1 2 3"
    )

  , ("ADTCaseParse1", DataInt 42
                     <==> "case D 1 2 3 of D 1 1 1 -> 0 | D 1 2 3 -> 42 | D 1 1 1 -> 1")
  , ("ADTCaseParse2", DataInt 42
                     <==> "case D 1 42 3 of D 1 1 1 -> 0 | D 1 n 3 -> n | D 1 1 1 -> 1")

  , ("primitiveParse", DataInt 42 <==> "plus 40 2")

  , ("lambdaParse", DataInt 42 <==> "(\\x -> x) 42")
  , ("lambdaLetParse", DataInt 42 <==> "let f := \\x -> plus x 2 in f 40")
  , ("primitiveAssignParse", DataInt 42 <==> "let f := plus in f 40 2")
  ]

