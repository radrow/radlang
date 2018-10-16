{-# LANGUAGE ScopedTypeVariables #-}
{-#LANGUAGE TypeOperators#-}
{-#LANGUAGE GADTs#-}

module Test where

import Control.Monad.Except
import qualified Data.Map.Strict as M
import Radlang.Types
import Radlang.Evaluator

data Test a b where
  (:==) :: a -> b -> Test a b
  deriving (Eq, Show)

test :: Test Data Expr -> Either ErrMsg ()
test (t :== x) = do
  (d :: Data) <- evalProgram M.empty x
  if t == d
    then return ()
    else throwError (show $ t :== d)

-- p1 = evalProgram M.empty $ (Case (Data (DataADT "XD" [DataInt 3])) [(Application (Val "XD") (Data $ DataInt 7), Val "Bad"), (Application (Val "XD") (Val "Good"), Val "Good")])

trivialTest :: Test Data Expr
trivialTest = DataInt 3 :== Data (DataInt 3)

letTest :: Test Data Expr
letTest = DataInt 3 :== Let [("XD", Nothing, Data $ DataInt 3)] (Val "XD")

caseTest1 :: Test Data Expr
caseTest1 = DataInt 42 :== Case (Data $`` DataInt 3) [ (Data $ DataInt 2, Val ":C")
                                                   , (Data $ DataInt 3, Data $ DataInt 42)
                                                   ]
caseTest2 :: Test Data Expr
caseTest2 = DataInt 42 :== Case (Data $ DataInt 3) [ (Data $ DataInt 9, Val ":C")
                                                   , (Data $ DataInt 3, Data $ DataInt 42)
                                                   ]


