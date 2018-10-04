module Radlang.Types where

import           Data.Map.Strict as M

type ErrMsg = String
type Name = String
type Namespace = M.Map Name Data

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
  | DataADT Name [Data]
  deriving (Eq, Show, Ord)
