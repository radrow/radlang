module Radlang.Typechecker where

import Data.Map.Strict as M

import Radlang.Types

type TypeScheme = M.Map Name Type


