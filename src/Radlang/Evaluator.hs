-- |This module is responsible for evaluation of Expr tree into Data

module Radlang.Evaluator(evalProgram) where

import Data.Bifunctor(first)
import Control.Applicative
import Control.Monad.State.Strict
import Control.Monad.Reader
import Control.Monad.Except
import Prelude hiding (lookup)
import qualified Data.Map.Strict as M

import Radlang.Helpers
import Radlang.Types
import Radlang.Stdlib


getNamespace :: Evaluator Namespace
getNamespace = lift ask

getDataspace :: Evaluator Dataspace
getDataspace = lift $ lift get

setDataspace :: Dataspace -> Evaluator ()
setDataspace d = lift $ lift $ put d

-- |Insert multiple assignments to namespace
inserts :: [(Name, Int)] -> Namespace -> Namespace
inserts as ns = foldl (flip $ uncurry M.insert) ns as

-- |Update namespace with new set of names replacing previous bindings
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

-- |Evals with stdlib included
withStdlib :: Evaluator a -> Evaluator a
withStdlib ev = do
  ns <- fmap M.fromList $ forM stdlib $ \(name, val ::: _) -> do
    i <- registerData val
    pure (name <~ i)
  withNs ns ev

-- |Same as `withAssg`, but evaluation performed
withAssgExpr :: (Name, Int) -> Expr -> Evaluator Data
withAssgExpr a e = withAssg a (eval e)

-- |Same as `withData`, but evaluation performed
withDataExpr :: (Name, Data) -> Expr -> Evaluator Data
withDataExpr a e = withData a (eval e)

-- |Same as `withNs`, but evaluation performed
withNsExpr :: Namespace -> Expr -> Evaluator Data
withNsExpr n e = local (update n) (eval e)

-- |Evaluator that returns computed result
eval :: Expr -> Evaluator Data
eval expr =
  case expr of
    Val a -> lookupName a >>= \case
      Just x -> pure x
      Nothing -> throwError $ "Unbound value: " <> a
    ConstInt d -> pure $ DataInt d
    ConstBool d -> pure $ DataBool d
    Application f arg ->
      eval f >>= \case
        DataLambda ns argname e -> do
          d <- withNsExpr ns arg
          withData (argname <~ d) $ withNsExpr ns e
        DataInternalFunc func -> func <$> eval arg
        d -> do
          ds <- getDataspace
          ns <- getNamespace
          throwError $ "Function application not into lambda: " <> show d <> "\n\n ds: " <> show ds <> "\n\n ns: " <> show ns
    Let [] eIn -> eval eIn
    Let ((name, _, e):rest) eIn -> do
      d <- eval e
      withDataExpr (name <~ d) (Let rest eIn)
    Lambda name e -> (\ns -> DataLambda ns name e) <$> ask

    If cond then_ else_ -> do
      c <- eval cond
      case c of
        DataBool b ->
          if b then eval then_ else eval else_
        _ -> throwError $ "Not a valid condition: " <> show c

-- |Executes Evaluator on given Expr
evalProgram :: Expr -> Either String Data
evalProgram ex = first ("Runtime Error: "<>) $ evalState (runReaderT (runExceptT $ withStdlib (withStdlib $ eval ex)) M.empty) (M.empty, 0)
