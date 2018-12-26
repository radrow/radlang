module Radlang.Types.Toplevel where

import Data.Set.Monad
import Data.Map.Strict

import Radlang.Types.General
import Radlang.Types.Runtime
import Radlang.Types.Typesystem

-- |Left and right side of function definition
type Alt = ([Pattern], Expr)

-- |Typeclass ambiguity
type Ambiguity = (TypeVar, [Pred])

type ExplBinding = (Name, (TypePoly, [Alt]))
type ImplBinding = (Name, [Alt])

type ExplBindings = Map Name (TypePoly, [Alt])
type ImplBindings = Map Name [Alt]

type BindingGroup = (ExplBindings, [ImplBindings])
