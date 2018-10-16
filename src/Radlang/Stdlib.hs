module Radlang.Stdlib where

import Radlang.Types

fun :: (Data -> Data) -> Data
fun = DataInternalFunc

plus = fun (\(DataInt i) -> fun (\(DataInt j) -> DataInt (i + j)))
minus = fun (\(DataInt i) -> fun (\(DataInt j) -> DataInt (i - j)))
mult = fun (\(DataInt i) -> fun (\(DataInt j) -> DataInt (i * j)))
divide = fun (\(DataInt i) -> fun (\(DataInt j) -> DataInt (i `div` j)))

