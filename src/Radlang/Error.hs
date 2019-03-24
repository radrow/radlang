{-# LANGUAGE FlexibleContexts #-}
module Radlang.Error where

import Control.Monad.Except
import Control.Monad.Reader

import Radlang.Types


typecheckError :: MonadError ErrMsg m => String -> m a
typecheckError = throwError . TypecheckError


languageError :: MonadError ErrMsg m => String -> m a
languageError = throwError . LanguageError


kindcheckError :: MonadError ErrMsg m => String -> m a
kindcheckError = throwError . KindcheckError


parseError :: MonadError ErrMsg m => String -> m a
parseError = throwError . ParseError


classEnvError :: MonadError ErrMsg m => String -> m a
classEnvError = throwError . ClassEnvError


runtimeError :: String -> Evaluator a
runtimeError s = do
  st <- asks _envDefStacktrace
  est <- asks _envEvalStacktrace
  throwError $ RuntimeError st est s


showErrorType :: ErrMsg -> String
showErrorType = \case
  TypecheckError _ -> "Typecheck error"
  LanguageError _ -> "Language error"
  KindcheckError _ -> "Kindcheck error"
  ParseError _ -> "Parse error"
  ClassEnvError _ -> "While building class environment"
  RuntimeError _ _ _ -> "Runtime error"


showErrorMessage :: ErrMsg -> String
showErrorMessage = \case
  TypecheckError e -> e
  LanguageError e -> e
  KindcheckError e -> e
  ParseError e -> e
  ClassEnvError e -> e
  RuntimeError dst est e ->
    let enum = fmap (uncurry $ (<>) . (<>". ") . show) . zip [(1::Int)..]
    in e <> "\nDefinition Stacktrace:\n" <> unlines (enum dst)
    <> "\nEvaluation stacktrace:\n" <> unlines (enum est)


showError :: ErrMsg -> String
showError em = showErrorType em <> ": " <> showErrorMessage em


wtf :: String -> a
wtf = error . ("WTF: "<>)
