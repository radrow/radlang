module Radlang.Helpers where

import Radlang.Types


(<~) :: a -> b -> (a, b)
(<~) = (,)

rollApplication :: Expr -> [Expr]
rollApplication = reverse . go where
  go (Application f x) = x : go f
  go els = [els]

