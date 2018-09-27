module Radlang.Types where

import Data.Map.Strict as M
import Control.Monad.State.Strict
import Control.Monad.Except

data Program

type ErrMsg = String
type Name = String
type Namespace = M.Map Name Data

data Expr
  = Val Name
  | Data Data
  | Application Expr Expr
  | Let [(Name, Maybe Type, Expr)] Expr
  | Lambda Name Expr
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
  deriving (Eq, Show, Ord)

type Interpreter = ExceptT ErrMsg (State Namespace)
