-- |Standard library that contains hard-coded functions

{-#LANGUAGE GADTs #-}
module Radlang.Stdlib(stdlib, Prim(..)) where

import Radlang.Types
import Radlang.Helpers

import Prelude hiding (or, and, not)
import qualified Prelude

data Prim where
  (:::) :: Data -> TypePoly -> Prim
infixr 9 :::

fun :: (Data -> Data) -> Data
fun = DataInternalFunc

plus :: Data
plus = fun (\(DataInt i) -> fun (\(DataInt j) -> DataInt (i + j)))
minus :: Data
minus = fun (\(DataInt i) -> fun (\(DataInt j) -> DataInt (i - j)))
mult :: Data
mult = fun (\(DataInt i) -> fun (\(DataInt j) -> DataInt (i * j)))
divide :: Data
divide = fun (\(DataInt i) -> fun (\(DataInt j) -> DataInt (i `div` j)))

eq :: Data
eq = fun (\a -> fun (\b -> DataBool $ a == b))
neq :: Data
neq = fun (\a -> fun (\b -> DataBool $ a /= b))

geq :: Data
geq = fun (\(DataInt i) -> fun (\(DataInt j) -> DataBool (i >= j)))
gt :: Data
gt = fun (\(DataInt i) -> fun (\(DataInt j) -> DataBool (i > j)))
leq :: Data
leq = fun (\(DataInt i) -> fun (\(DataInt j) -> DataBool (i <= j)))
lt :: Data
lt = fun (\(DataInt i) -> fun (\(DataInt j) -> DataBool (i < j)))

or :: Data
or = fun (\(DataBool i) -> fun (\(DataBool j) -> DataBool (i || j)))
and :: Data
and = fun (\(DataBool i) -> fun (\(DataBool j) -> DataBool (i && j)))
not :: Data
not = fun (\(DataBool i) -> DataBool (Prelude.not i))


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
