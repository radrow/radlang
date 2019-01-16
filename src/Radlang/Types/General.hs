-- |Basic universal types

module Radlang.Types.General where


-- |Type aliasses to clarify purpose and ease refactor
data ErrMsg
  = ParseError String
  | KindcheckError String
  | ClassEnvError String
  | TypecheckError String
  | RuntimeError String

type Name = String

-- |Key in Dataspace map
type DataId = Int
