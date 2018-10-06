module Radlang.Space where

import Control.Monad.State.Strict
import qualified Data.Map.Strict as M

import Radlang.Types

empty :: Namespace
empty = M.empty

insert :: Name -> Data -> Evaluator ()
insert = M.insert

inserts :: [(Name, Data)] -> Namespace -> Namespace
inserts as ns = foldl (flip $ uncurry insert) ns as

single :: String -> Data -> Namespace
single n d = insert n d empty

update :: Namespace -> Namespace -> Namespace
update = M.union

registerConstructor :: String -> Int -> Namespace -> Namespace
registerConstructor name arity ns =
  M.insert name (cons arity) ns where
  cons 0 = DataADT name []
  cons n = let (DataADT _ l) = cons (n-1)
               argname = uniqueName $ name <> show n
           in DataLambda ns argname (Data $ DataADT name (Val argname : l))


lookup :: Name -> Namespace -> Maybe Data
lookup = M.lookup
