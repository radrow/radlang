module Radlang.Evaluator where

import Data.Maybe (catMaybes)
import Data.Traversable (for)
import Control.Applicative
import Control.Monad.State.Strict
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.Trans.Maybe
import Prelude hiding (lookup)
import qualified Data.Map.Strict as M

import Radlang.Helpers
import Radlang.Types
import Radlang.EvaluationEnv
import Radlang.Stdlib

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

    Case ecased cases -> do
      let caseWith :: ((Expr, Expr) -> Evaluator (Maybe Data)) -> Evaluator (Maybe Data)
          caseWith f = msum <$> traverse f cases
      cased <- eval ecased
      newe <- case cased of
        DataInt i -> caseWith (\(c, e) -> case c of
                                  Val v -> Just <$> withDataExpr (v <~ DataInt i) e
                                  ConstInt d ->
                                    if d == i
                                    then Just <$> eval e
                                    else pure Nothing
                                  _ -> pure Nothing
                              )
        _ -> pure Nothing
      case newe of
        Nothing -> throwError "Case match exhaustion"
        Just dd -> pure dd
    If cond then_ else_ -> do
      c <- eval cond
      case c of
        DataBool b ->
          if b then eval then_ else eval else_
        _ -> throwError $ "Not a valid condition: " <> show c

evalProgram :: Expr -> Either String Data
evalProgram ex = evalState (runReaderT (runExceptT $ withStdlib (eval ex)) M.empty) (M.empty, 0)
