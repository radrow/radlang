module Radlang.Namespace where

import qualified Data.Map.Strict as M

import Radlang.Types

empty :: Namespace
empty = M.empty

insert :: String -> Data -> Namespace -> Namespace
insert = M.insert

single :: String -> Data -> Namespace
single n d = insert n d empty
