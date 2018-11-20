{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeOperators             #-}

module Test where

import           Control.Monad.Except
import           Data.Bifunctor(bimap)
import           System.Console.ANSI
import qualified Text.Megaparsec            as MP

import           Radlang.Evaluator
import           Radlang.Typechecker
import           Radlang.Parser
import           Radlang.Types


parse :: String -> Either ErrMsg Expr
parse inp = bimap MP.parseErrorPretty processAST $ MP.parse (ast <* MP.eof) "test" inp

parsePrint :: String -> IO ()
parsePrint inp = case parse inp of
  Right d -> setSGR [SetColor Foreground Vivid Green] >> print d >> setSGR [SetColor Foreground Vivid White]
  Left d -> setSGR [SetColor Foreground Vivid Red] >> putStrLn d >> setSGR [SetColor Foreground Vivid White]

class Testable t where
  test :: t -> Either ErrMsg ()

data Test a b where
  (:==) :: a -> b -> Test a b
  (:/=) :: a -> b -> Test a b
  Failing :: Expr -> Test () Expr

instance Testable (Test StrictData Expr) where
  test (t :== x) = do
    (d :: StrictData) <- evalProgram x
    if t == d
      then return ()
      else throwError (show t <> ":/=" <> show d)
  test (t :/= x) = do
    (d :: StrictData) <- evalProgram x
    if t /= d
      then return ()
      else throwError (show t <> ":==" <> show d)
instance Eq a => Testable (Test a a) where
  test (a :== b) = if a == b then Right () else Left "Not equal"
  test (a :/= b) = if a /= b then Right () else Left "Equal"
instance Testable (Test () Expr) where
  test (Failing e) = case evalProgram e of
    Right _ -> Left "Succeeded"
    Left _  -> Right ()
  test (() :== e) = void $ evalProgram e
  test (() :/= e) = void $ evalProgram e
instance Testable (Test StrictData String) where
  test (d :== s) = case parse s >>= evalProgram of
    Left e  -> Left e
    Right r -> if r == d then Right () else Left "Results mismatch"
  test (d :/= s) = case parse s >>= evalProgram of
    Left e  -> Left e
    Right r -> if r /= d then Right () else Left "Results match"
instance Testable (Test Type String) where
  test (t :== s) = void $ flip fmap (parse s) (\e -> Let [("TEST", Just t, e)] (Val "TEST")) >>= typecheck
  test (t :/= s) = case flip fmap (parse s) (\e -> Let [("TEST", Just t, e)] (Val "TEST")) of
    Left e  -> Left e
    Right r -> case typecheck r of
      Left _ -> Right ()
      Right rr -> Left $ "Shouldn't typecheck, but got "<> show rr
instance Testable (Test Type Expr) where
  test (t :== e) = void $ typecheck (Let [("TEST", Just t, e)] (Val "TEST"))
  test (t :/= e) = case typecheck (Let [("TEST", Just t, e)] (Val "TEST")) of
      Left _ -> Right ()
      Right rr -> Left $ "Shouldn't typecheck, but got "<> show rr


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
  [ ("trivialTest", DataInt 3 <==> ConstInt 3)

  , ("letTest", DataInt 3 <==> Let [("XD", Nothing, ConstInt 3)] (Val "XD"))

  -- , ("caseTest1", DataInt 42 <==> Case (Data $ DataInt 3) [ (Data $ DataInt 2, Val ":C")
  --                                                  , (Data $ DataInt 3, Data $ DataInt 42)
  --                                                  ])
  -- , ("caseTest2", DataInt 42 <==> Case (Data $ DataInt 42) [ (Data $ DataInt 9, Val ":C")
  --                                                  , (Val "kek", Val "kek")
  --                                                  ])

  -- , ("caseTest3", DataInt 42 <==> Case (Data $ DataADT "D" [DataInt 42])
  --           [(Application (Val "D") (Data $ DataInt 42), Data $ DataInt 42)])


  -- , ("caseTest4", DataInt 42 <==> Case (Data $ DataADT "D" [DataInt 42])
  --           [ (Application (Val "A") (Data $ DataInt 42), Data $ DataInt 0)
  --           , (Application (Application (Val "D") (Data $ DataInt 0)) (Data $ DataInt 42), Data $ DataInt 42)
  --           , (Application (Val "D") (Data $ DataInt 42), Data $ DataInt 42)
  --           ])

  , ("trivialParse", DataInt 42 <==> "42")

  , ("letParse1", DataInt 42 <==> "let x := 42 in x")
  , ("letParse2", DataInt 42 <==> "let x := 0; y := 42 in y")
  , ("letParse3", DataInt 42 <==> "let x := 42; y := 0 in x")
  , ("letParse4", DataInt 42 <==> "let x := 42; y := x in y")
  , ("shadowParse1", DataInt 42 <==> "let x := 0 in let x := 42 in x")
  , ("shadowParse2", DataInt 42 <==> "let x := 2; y := x in let x := 40 in plus x y")

  -- , ("caseParse1", DataInt 42 <==> "case 5 of 5 -> 42")
  -- , ("caseParse2", DataInt 42 <==> "case 5 of 3 -> 0 | 5 -> 42")
  -- , ("caseParse3", DataInt 42 <==> "case 5 of 5 -> 42 | 3 -> 0")
  -- , ("caseParse4", DataInt 42 <==> "case 42 of 1 -> 0 | n -> n")

  -- , ("ADTParse", DataADT "D" [DataInt 1, DataInt 2, DataInt 3]
  --                <==> "D 1 2 3"
  --   )

  -- , ("ADTCaseParse1", DataInt 42
  --                    <==> "case D 1 2 3 of D 1 1 1 -> 0 | D 1 2 3 -> 42 | D 1 1 1 -> 1")
  -- , ("ADTCaseParse2", DataInt 42
  --                    <==> "case D 1 42 3 of D 1 1 1 -> 0 | D 1 n 3 -> n | D 1 1 1 -> 1")

  , ("primitiveParse", DataInt 42 <==> "plus 40 2")

  , ("lambdaParse", DataInt 42 <==> "(\\x -> x) 42")
  , ("lambdaLetParse", DataInt 42 <==> "let f := \\x -> plus x 2 in f 40")

  , ("primitiveAssignParse", DataInt 42 <==> "let f := plus in f 40 2")

  , ("ifParse1", DataInt 42 <==> "if True then 42 else 0")
  , ("ifParse2", DataInt 42 <==> "if False then 0 else 42")
  , ("ifMulti", DataInt 42 <==> "if False then 0 if False then 0 else 42")

  , ("eq1", DataBool True <==> "eq 2 2")
  , ("eq2", DataBool False <==> "eq 2 3")

  , ("ifLambda", DataInt 42 <==> "let f := \\a -> if eq a 0 then 42 else 0 in f 0")
  , ("ifLambdaCompl", DataInt 42 <==> "let f := \\a b -> if eq a 0 then b else 0 in f 0 42")

  , ("rec1", DataInt 42 <==> "let f := \\a -> if eq a 0 then 42 else f 0 in f 42")
  , ("factorial", DataInt 24 <==> "let fac := \\n -> if eq n 0 then 1 else mult n (fac (minus n 1)) in fac 4")

  , ("lazyIf", DataInt 42 <==> "let x := x; iff c t e := if c then t else e in if True then 42 else x")
  , ("lazyFixConst", DataInt 42 <==> "let fix f := let x := f x in x; const a b := a in fix (const 42)")
  , ("lazyFixFactorial", DataInt 24 <==> "let fix f := let x := f x in x in fix (\\rec n -> if eq n 0 then 1 else mult n (rec (minus n 1))) 4")

  , ("typeInt", TypeInt <==> "3")
  , ("typeBool", TypeBool <==> "True")

  , ("typeLet", TypeInt <==> "let x := 3 in x")
  , ("typeLetFunc", TypeFunc (TypeVal "A") (TypeVal "A") <==> "let f x := x in f")
  , ("typeLetFunc2", TypeInt <==> "let f x y := plus y x in f 1 2")
  , ("typeLetFunc3", TypeInt <==> "let f : Int -> Int := plus 3 in f 3")
  , ("typeLetFunc4", TypeFunc TypeInt TypeInt <==> "let f x : Int -> Int := plus x x in f")
  , ("typeLetAnn", TypeInt <==> "let x : Int := 3 in x")
  , ("typeLetAnnBad", TypeBool </=> "let x : Int := True in x")
  , ("typeLetAnnBad2", TypeBool </=> "let x : Bool := 3 in x")

  , ("typeFunc", (TypeFunc (TypeVal "A") (TypeVal "A")) <==> "\\x -> x")
  , ("typeFuncRigid", (TypeFunc (TypeValRigid "A") (TypeValRigid "A")) <==> "\\x -> x")
  , ("typeFuncRigidBad", (TypeFunc (TypeValRigid "A") (TypeValRigid "B")) </=> "\\x -> x")
  , ("typeFuncRigidBad2", TypeValRigid "A" </=> "3")
  , ("typeFuncAnn", (TypeFunc (TypeValRigid "A") (TypeValRigid "A")) <==> "let f : ~A -> ~A := \\x -> x in f")
  , ("typeFuncRec", TypeInt <==> "let f : Int -> Int := \\x -> f x in f 3")

  , ("typeGeneralization", TypeFunc TypeInt TypeInt <==> "let f : Int -> Int := \\x -> x in f")
  , ("typeIf", TypeInt <==> "if True then 1 else 2")
  , ("typeIfBad1", TypeInt </=> "if 1 then 1 else 2")
  , ("typeIfBad2", TypeInt </=> "if True then True else 2")

  ]
