module Radlang.Stdlib where

import Radlang.Types
import Radlang.EvaluationEnv
import Radlang.Helpers

import qualified  Data.Map.Strict as M
import Control.Monad.Writer.Strict

import Prelude hiding (or, and)

fun :: (Data -> Data) -> Data
fun = DataInternalFunc

plus = fun (\(DataInt i) -> fun (\(DataInt j) -> DataInt (i + j)))
minus = fun (\(DataInt i) -> fun (\(DataInt j) -> DataInt (i - j)))
mult = fun (\(DataInt i) -> fun (\(DataInt j) -> DataInt (i * j)))
divide = fun (\(DataInt i) -> fun (\(DataInt j) -> DataInt (i `div` j)))

eq = fun (\a -> fun (\b -> DataBool $ a == b))

geq = fun (\(DataInt i) -> fun (\(DataInt j) -> DataBool (i >= j)))
gt = fun (\(DataInt i) -> fun (\(DataInt j) -> DataBool (i > j)))
leq = fun (\(DataInt i) -> fun (\(DataInt j) -> DataBool (i <= j)))
lt = fun (\(DataInt i) -> fun (\(DataInt j) -> DataBool (i < j)))

or = fun (\(DataBool i) -> fun (\(DataBool j) -> DataBool (i || j)))
and = fun (\(DataBool i) -> fun (\(DataBool j) -> DataBool (i && j)))


registerPrimitive :: Name -> Data -> WriterT [(Name, DataId)] Evaluator ()
registerPrimitive name dat = lift (registerData dat) >>= \i -> tell [(name, i)]

importStdlib :: Evaluator Namespace
importStdlib = fmap M.fromList $ execWriterT $
  traverse (uncurry registerPrimitive)
  [ "plus" <~ plus
  , "minus" <~ minus
  , "mult" <~ mult
  , "div" <~ divide
  , "eq" <~ eq
  , "geq" <~ geq
  , "gt" <~ gt
  , "leq" <~ leq
  , "lt" <~ lt
  , "or" <~ or
  , "and" <~ and
  ]

withStdlib :: Evaluator a -> Evaluator a
withStdlib e = importStdlib >>= \ns -> withNs ns e
