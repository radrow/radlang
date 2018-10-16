module Radlang.Types where

import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State.Strict
import           Data.Map.Strict            as M

type ErrMsg = String
type Name = String

type DataId = Int

type Namespace = M.Map Name DataId
type Dataspace = (M.Map DataId DataEntry, Int)
data DataEntry = Strict Data | Lazy Namespace Expr
  deriving (Eq, Show, Ord)

type Evaluator = ExceptT String (ReaderT Namespace (State Dataspace))

data Expr
  = Val Name
  | Data Data
  | Application Expr Expr
  | Let [(Name, Maybe Type, Expr)] Expr
  | Lambda Name Expr
  | Case Expr [(Expr, Expr)]
  deriving (Eq, Show, Ord)

data Type
  = TypeInt
  | TypeBool
  | TypeString
  | TypeFunc Type Type
  | TypeADT Name [Type]
  deriving (Eq, Show, Ord)

data Data
  = DataInt Int
  | DataBool Bool
  | DataLambda Namespace Name Expr
  | DataADT Name [DataEntry]
  deriving (Eq, Show, Ord)
