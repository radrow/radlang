-- |Standard library that contains hard-coded functions

{-# LANGUAGE ScopedTypeVariables #-}
{-#LANGUAGE GADTs #-}
module Radlang.Stdlib(stdlib, Prim(..), runtimeShow) where

import Control.Monad.Except

import Radlang.Types
import Radlang.Helpers
import {-# SOURCE #-} Radlang.Evaluator

import Prelude hiding (or, and, not)
import qualified Prelude

data Prim where
  (:::) :: StrictData -> TypePoly -> Prim
infixr 9 :::

fun :: (Data -> Evaluator Data) -> StrictData
fun = DataInternalFunc
fun2 :: (Data -> Data -> Evaluator Data) -> StrictData
fun2 f = fun $ \a ->
  pure . Strict . fun $ \b -> f a b

plus :: StrictData
plus = fun2 $ \i j -> do
  (DataInt ii) <- force i
  (DataInt jj) <- force j
  pure $ Strict (DataInt $ ii + jj)
minus :: StrictData
minus = fun2 $ \i j -> do
  (DataInt ii) <- force i
  (DataInt jj) <- force j
  pure $ Strict (DataInt $ ii - jj)
mult :: StrictData
mult = fun2 $ \i j -> do
  (DataInt ii) <- force i
  (DataInt jj) <- force j
  pure $ Strict (DataInt $ ii * jj)
divide :: StrictData
divide = fun2 $ \i j -> do
  (DataInt ii) <- force i
  (DataInt jj) <- force j
  if jj /= 0
    then pure $ Strict (DataInt $ ii `div` jj)
    else throwError "Division by zero"

runtimeEq :: StrictData -> StrictData -> Evaluator Bool
runtimeEq a b = case (a, b) of
  (DataInt i, DataInt j) -> pure $ i == j
  (DataBool i, DataBool j) -> pure $ i == j
  _ -> throwError "Objects not comparable"

runtimeShow :: Data -> Evaluator String
runtimeShow (Strict d) = pure $ show d
runtimeShow l = force l >>= pure . show

eq :: StrictData
eq = fun2 $ \i j -> do
  ii <- force i
  jj <- force j
  b <- runtimeEq ii jj
  pure $ Strict (DataBool $ b)
neq :: StrictData
neq = fun2 $ \i j -> do
  ii <- force i
  jj <- force j
  b <- runtimeEq ii jj
  pure $ Strict (DataBool $ Prelude.not b)

geq :: StrictData
geq = fun2 $ \i j -> do
  (DataInt ii) <- force i
  (DataInt jj) <- force j
  pure $ Strict (DataBool $ ii >= jj)
gt :: StrictData
gt = fun2 $ \i j -> do
  (DataInt ii) <- force i
  (DataInt jj) <- force j
  pure $ Strict (DataBool $ ii > jj)
leq :: StrictData
leq = fun2 $ \i j -> do
  (DataInt ii) <- force i
  (DataInt jj) <- force j
  pure $ Strict (DataBool $ ii <= jj)
lt :: StrictData
lt = fun2 $ \i j -> do
  (DataInt ii) <- force i
  (DataInt jj) <- force j
  pure $ Strict (DataBool $ ii < jj)

or :: StrictData
or = fun2 $ \i j -> do
  (DataBool ii) <- force i
  (DataBool jj) <- force j
  pure $ Strict (DataBool $ ii || jj)
and :: StrictData
and = fun2 $ \i j -> do
  (DataBool ii) <- force i
  (DataBool jj) <- force j
  pure $ Strict (DataBool $ ii && jj)
not :: StrictData
not = fun $ \i -> do
  (DataBool ii) <- force i
  pure $ Strict $ DataBool (Prelude.not ii)


stdlib :: [(Name, Prim)]
stdlib =
  [ "plus" <~ plus ::: makePoly (TypeFunc TypeInt (TypeFunc TypeInt TypeInt))
  , "minus" <~ minus ::: makePoly (TypeFunc TypeInt (TypeFunc TypeInt TypeInt))
  , "mult" <~ mult ::: makePoly (TypeFunc TypeInt (TypeFunc TypeInt TypeInt))
  , "div" <~ divide ::: makePoly (TypeFunc TypeInt (TypeFunc TypeInt TypeInt))
  , "eq" <~ eq ::: Poly (pure "A") (TypeFunc (TypeVal "A") (TypeFunc (TypeVal "A") TypeBool))
  , "neq" <~ neq ::: Poly (pure "A") (TypeFunc (TypeVal "A") (TypeFunc (TypeVal "A") TypeBool))
  , "geq" <~ geq ::: makePoly (TypeFunc TypeInt (TypeFunc TypeInt TypeBool))
  , "gt" <~ gt ::: makePoly (TypeFunc TypeInt (TypeFunc TypeInt TypeBool))
  , "leq" <~ leq ::: makePoly (TypeFunc TypeInt (TypeFunc TypeInt TypeBool))
  , "lt" <~ lt ::: makePoly (TypeFunc TypeInt (TypeFunc TypeInt TypeBool))
  , "or" <~ or ::: makePoly (TypeFunc TypeBool (TypeFunc TypeBool TypeBool))
  , "and" <~ and ::: makePoly (TypeFunc TypeBool (TypeFunc TypeBool TypeBool))
  , "not" <~ not ::: makePoly (TypeFunc TypeBool TypeBool)
  ]
