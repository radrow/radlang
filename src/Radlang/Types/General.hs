-- |Basic universal types
module Radlang.Types.General where


-- |User errors that may appear whole interpretation process
data ErrMsg
  = ParseError String
  | KindcheckError String
  | InterfaceEnvError String
  | TypecheckError String
  | LanguageError String
  | RuntimeError [String] [String] String
  deriving (Eq, Show)


-- |Universal name type. Future releases may use 'Text' here
type Name = String


-- |Key in Dataspace map
type DataId = Int
