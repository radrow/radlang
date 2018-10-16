module Radlang.Types where

import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State.Strict
import qualified Data.Map.Strict            as M

type ErrMsg = String
type Name = String

type DataId = Int

type Namespace = M.Map Name DataId
type Dataspace = (M.Map DataId DataEntry, Int)
data DataEntry = Strict Data | Lazy Namespace Expr
  deriving (Show, Eq)

type Evaluator = ExceptT String (ReaderT Namespace (State Dataspace))

data Expr
  = Val Name
  | Data Data
  | Application Expr Expr
  | Let [(Name, Maybe Type, Expr)] Expr
  | Lambda Name Expr
  | Case Expr [(Expr, Expr)]
  deriving (Eq, Show)

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
  | DataInternalFunc (Data -> Data)
  | DataADT Name [DataEntry]

instance Show Data where
  show = \case
    DataInt i -> show i
    DataBool b -> show b
    DataLambda n nn e -> "lambda in (" <> show n <> ") \\" <> nn <> " -> " <> show e
    DataInternalFunc _ -> "internal func"
    DataADT n e -> n <> foldr (<>) "" (map show e)

instance Eq Data where
  (DataInt a) == (DataInt b) = a == b
  (DataBool a) == (DataBool b) = a == b
  (DataADT n e) == (DataADT n2 e2) = n == n2 && all id (zipWith (==) e e2)
  _ == _ = False -- we don't compare functions.
