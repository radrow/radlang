-- |Types related to program evaluation

module Radlang.Types.Runtime where

import Data.List.NonEmpty
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State.Strict
import  Data.Map.Strict(Map)

import Radlang.Types.Typesystem
import Radlang.Types.General

-- |Map of value names into ids
type Namespace = Map Name DataId

-- |Map of ids into real data
type Dataspace = (Map DataId Data, Int)

-- |Transformer responsible for expression evaluation and error handling
type Evaluator = ExceptT String (ReaderT Namespace (State Dataspace))

-- |Desugared expression tree designed for evaluation
data Expr
  = Val Name
  | ConstInt Integer
  | ConstBool Bool
  | Application Expr Expr
  | Let [(Name, Maybe Type, Expr)] Expr
  | Lambda Name Expr
  | If Expr Expr Expr
  deriving (Eq, Show)

-- |Abstract syntax tree that faithfully represents code. Layer between text and Expr
data AST
  = ASTVal Name
  | ASTInt Integer
  | ASTBool Bool
  | ASTApplication AST (NonEmpty AST)
  | ASTLet (NonEmpty (Name, [Name], Maybe Type, AST)) AST
  | ASTLambda (NonEmpty Name) AST
  | ASTIf (NonEmpty (AST, AST)) AST
  deriving(Eq, Show)

data Data = Lazy Namespace DataId Expr | Strict StrictData

data StrictData
  = DataInt Integer
  | DataBool Bool
  | DataLambda Namespace Name Expr
  | DataInternalFunc (Data -> Evaluator Data)

instance Show StrictData where
  show = \case
    DataInt i -> show i
    DataBool b -> show b
    DataLambda _ n e -> "\\" <> n <> " -> " <> show e
    DataInternalFunc _ -> "internal func"

instance Eq StrictData where
  (DataInt a) == (DataInt b) = a == b
  (DataBool a) == (DataBool b) = a == b
  _ == _ = False -- we don't compare functions.


