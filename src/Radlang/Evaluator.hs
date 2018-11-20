-- |This module is responsible for evaluation of Expr tree into Data

module Radlang.Evaluator(evalProgram, evalPrintProgram, force) where

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
  put (M.insert (count + 1) d ds, count + 1)
  pure $ count + 1


-- |Allocates new data on given id
updateDataAt :: Data -> DataId -> Evaluator ()
updateDataAt d i = do
  (ds, count) <- getDataspace
  put (M.insert i d ds, count)
  pure ()

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
    i <- registerData $ Strict val
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

-- |Forces evaluation of lazy data
force :: Data -> Evaluator StrictData
force (Strict d) = pure d
force (Lazy ns i expr) = do
  forced <- withNsExpr ns expr >>= force
  updateDataAt (Strict forced) i
  pure forced

-- |Forces deeply data
deepForce :: Data -> Evaluator StrictData
deepForce = force

-- |Evaluator that returns computed result
eval :: Expr -> Evaluator Data
eval expr =
  case expr of
    Val a -> lookupName a >>= \case
      Just x -> pure x
      Nothing -> throwError $ "Unbound value: " <> a
    ConstInt d -> pure $ Strict $ DataInt d
    ConstBool d -> pure $ Strict $ DataBool d
    Application f arg ->
      eval f >>= force >>= \case
        DataLambda ns argname e -> do
          d <- eval arg
          withNs ns $ withDataExpr (argname <~ d) e
        DataInternalFunc func -> eval arg >>= func
        d -> do
          throwError $ "Function application not into lambda: " <> show d
    Let defs eIn -> do
      (_, dcount) <- getDataspace
      ns <- getNamespace
      let n = length defs
          ids = take n [dcount + 1..]
          idDefs = map (\((a,b,c), i) -> (a,b,c,i)) (zip defs ids)
          newNs = foldl
                  (\prevNs (name, _, _, i) -> M.insert name i prevNs)
                  ns
                  idDefs
      forM_ idDefs $ \(_, _, e, i) -> registerData (Lazy newNs i e)
      withNsExpr newNs eIn

    Lambda name e -> Strict . (\ns -> DataLambda ns name e) <$> ask

    If cond then_ else_ -> do
      c <- force =<< eval cond
      case c of
        DataBool b ->
          if b then eval then_ else eval else_
        _ -> throwError $ "Not a valid condition: " <> show c

-- |Executes Evaluator on given Expr
evalProgram :: Expr -> Either ErrMsg StrictData
evalProgram ex = first ("Runtime Error: "<>) $ evalState (runReaderT (runExceptT $ withStdlib (withStdlib $ eval ex >>= deepForce)) M.empty) (M.empty, 0)

-- |Executes Evaluator and prints result
evalPrintProgram :: Expr -> Either ErrMsg String
evalPrintProgram ex = first ("Runtime Error: "<>) $ evalState (runReaderT (runExceptT $ withStdlib (withStdlib $ eval ex >>= runtimeShow )) M.empty) (M.empty, 0)
