-- |Basic universal types

module Radlang.Types.General where

import Data.List.NonEmpty

-- |Type aliasses to clarify purpose and ease refactor
data ErrMsg
  = ParseError String
  | KindcheckError String
  | ClassEnvError String
  | TypecheckError String
  | RuntimeError String
  | MultipleErrors (NonEmpty ErrMsg)
  deriving (Eq)

-- instance Semigroup ErrMsg where
--   e1 <> e2 = case (e1, e2) of
--     (MultipleErrors es1, MultipleErrors es2) -> MultipleErrors (es1 <> es2)
--     (_, MultipleErrors es2) -> MultipleErrors (cons e1 es2)
--     (MultipleErrors (e:|es), _) -> MultipleErrors (e:|(es ++ [e2]))
--     _ -> MultipleErrors (fromList [e1, e2])
-- instance Monoid ErrMgs where


type Name = String

-- |Key in Dataspace map
type DataId = Int
