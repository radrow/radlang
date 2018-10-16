module Radlang.Stdlib where

import Radlang.Types
import Radlang.Space

import qualified  Data.Map.Strict as M
import Control.Monad.Writer.Strict

fun :: (Data -> Data) -> Data
fun = DataInternalFunc

plus = fun (\(DataInt i) -> fun (\(DataInt j) -> DataInt (i + j)))
minus = fun (\(DataInt i) -> fun (\(DataInt j) -> DataInt (i - j)))
mult = fun (\(DataInt i) -> fun (\(DataInt j) -> DataInt (i * j)))
divide = fun (\(DataInt i) -> fun (\(DataInt j) -> DataInt (i `div` j)))

registerPrimitive :: Name -> Data -> WriterT [(Name, DataId)] Evaluator ()
registerPrimitive name dat = lift (registerData (Strict dat)) >>= \i -> tell [(name, i)]

importStdlib :: Evaluator Namespace
importStdlib = fmap M.fromList $ execWriterT $
  traverse (uncurry registerPrimitive)
  [ "plus" <~ plus
  , "minus" <~ minus
  , "mult" <~ mult
  , "div" <~ divide
  ]

withStdlib :: Evaluator a -> Evaluator a
withStdlib e = importStdlib >>= \ns -> withNs ns e
