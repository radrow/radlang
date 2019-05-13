-- |Basic universal types
module Radlang.Types.General where

import Data.Text


-- |User errors that may appear whole interpretation process
data ErrMsg
  = ParseError Text
  | KindcheckError Text
  | InterfaceEnvError Text
  | TypecheckError Text
  | LanguageError Text
  | RuntimeError [Text] [Text] Text
  deriving (Eq, Show)


-- |Universal name type. Future releases may use 'Text' here
type Name = Text


-- |Key in Dataspace map
type DataId = Int
