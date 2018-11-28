-- |Basic universal types

{-# LANGUAGE TypeFamilies #-}

module Radlang.Types.General where

import GHC.Exts
import Data.Set.Monad as S

-- |Type aliasses to clarify purpose and ease refactor
type ErrMsg = String
type Name = String

-- |Key in Dataspace map
type DataId = Int
