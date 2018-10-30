module Radlang.EvaluationEnv where

import qualified Data.Map.Strict as M
import Control.Monad.State.Strict
import Control.Monad.Except
import Control.Monad.Reader

import Radlang.Helpers
import Radlang.Types

getNamespace :: Evaluator Namespace
getNamespace = lift ask

getDataspace :: Evaluator Dataspace
getDataspace = lift $ lift get

setDataspace :: Dataspace -> Evaluator ()
setDataspace d = lift $ lift $ put d

inserts :: [(Name, Int)] -> Namespace -> Namespace
inserts as ns = foldl (flip $ uncurry M.insert) ns as

update :: Namespace -> Namespace -> Namespace
update = M.union

-- |Try to get data by name
lookupName :: Name -> Evaluator (Maybe Data)
lookupName n = do
  ns <- getNamespace
  ds <- fst <$> getDataspace
  case M.lookup n ns of
    Just i -> case M.lookup i ds of
      Just d -> pure $ Just d
      Nothing -> throwError $ "Unbound id: " <> show i
    Nothing -> pure Nothing


-- |Allocates new data and returns id
registerData :: Data -> Evaluator DataId
registerData d = do
  (ds, count) <- getDataspace
  put $ (M.insert (count + 1) d ds, count + 1)
  pure $ count + 1

-- |Evals with overbound variable id
withAssg :: (Name, Int) -> Evaluator a -> Evaluator a
withAssg (n, d) = local (M.insert n d)

-- |Evals with data bound to name
withData :: (Name, Data) -> Evaluator a -> Evaluator a
withData (n, d) e = registerData d >>= \i -> withAssg (n <~ i) e

-- |Evals with updated namespace
withNs :: Namespace -> Evaluator a -> Evaluator a
withNs n = local (update n)
