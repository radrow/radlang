module Radlang.Evaluator where

import Control.Applicative
import Control.Monad.State.Strict
import Control.Monad.Reader
import Control.Monad.Except
import Prelude hiding (lookup)
import qualified Data.Map.Strict as M

import Radlang.Helpers
import Radlang.Types
import Radlang.EvaluationEnv

-- |Same as `withAssg`, but evaluation performed
withAssgExpr :: (Name, Int) -> Expr -> Evaluator Data
withAssgExpr a e = withAssg a (eval e)

-- |Same as `withData`, but evaluation performed
withDataExpr :: (Name, Data) -> Expr -> Evaluator Data
withDataExpr a e = withData a (eval e)

-- |Same as `withNs`, but evaluation performed
withNsExpr :: Namespace -> Expr -> Evaluator Data
withNsExpr n e = local (update n) (eval e)

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

evalProgram :: Expr -> Either String Data
evalProgram ex = evalState (runReaderT (runExceptT $ withStdlib (withStdlib $ eval ex)) M.empty) (M.empty, 0)
