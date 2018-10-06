module Radlang.Helpers where

import Radlang.Types

rollApplication :: Expr -> [Expr]
rollApplication = reverse . go where
  go (Application f x) = x : go f
  go els = [els]

uniqueName :: Name -> Name
uniqueName n = "__" <> n <> "__"
