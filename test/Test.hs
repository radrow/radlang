{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-#LANGUAGE TypeOperators#-}
{-#LANGUAGE GADTs#-}
{-#LANGUAGE FlexibleInstances#-}

module Test where

import Control.Monad.Except
import qualified Data.Map.Strict as M
import Radlang.Types
import Radlang.Evaluator

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
    Left _ -> Right ()
  test (() :== e) = void $ evalProgram M.empty e
  test (() :/= e) = void $ evalProgram M.empty e
instance Testable (Test Data String) where
  

trivialTest :: Test Data Expr
trivialTest = DataInt 3 :== Data (DataInt 3)

letTest :: Test Data Expr
letTest = DataInt 3 :== Let [("XD", Nothing, Data $ DataInt 3)] (Val "XD")

caseTest1 :: Test Data Expr
caseTest1 = DataInt 42 :== Case (Data $ DataInt 3) [ (Data $ DataInt 2, Val ":C")
                                                   , (Data $ DataInt 3, Data $ DataInt 42)
                                                   ]
caseTest2 :: Test Data Expr
caseTest2 = DataInt 42 :== Case (Data $ DataInt 42) [ (Data $ DataInt 9, Val ":C")
                                                   , (Val "kek", Val "kek")
                                                   ]

caseTest3 :: Test Data Expr
caseTest3 = DataInt 42 :== Case (Data $ DataADT "D" [Strict $ DataInt 42])
            [(Application (Val "D") (Data $ DataInt 42), Data $ DataInt 42)]


caseTest4 :: Test Data Expr
caseTest4 = DataInt 42 :== Case (Data $ DataADT "D" [Strict $ DataInt 42])
            [ (Application (Val "A") (Data $ DataInt 42), Data $ DataInt 0)
            , (Application (Application (Val "D") (Data $ DataInt 0)) (Data $ DataInt 42), Data $ DataInt 42)
            , (Application (Val "D") (Data $ DataInt 42), Data $ DataInt 42)
            ]
