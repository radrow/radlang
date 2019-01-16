{-# LANGUAGE FlexibleContexts #-}
module Radlang.Error where

import Control.Monad.Except

import Radlang.Types


typecheckError :: MonadError ErrMsg m => String -> m a
typecheckError = throwError . TypecheckError


kindcheckError :: MonadError ErrMsg m => String -> m a
kindcheckError = throwError . KindcheckError


parseError :: MonadError ErrMsg m => String -> m a
parseError = throwError . ParseError


classEnvError :: MonadError ErrMsg m => String -> m a
classEnvError = throwError . ClassEnvError


runtimeError :: MonadError ErrMsg m => String -> m a
runtimeError = throwError . RuntimeError


showErrorType :: ErrMsg -> String
showErrorType = \case
  TypecheckError _ -> "Typecheck error"
  KindcheckError _ -> "Kindcheck error"
  ParseError _ -> "Parse error"
  ClassEnvError _ -> "While building class environment"
  RuntimeError _ -> "Runtime error"


showErrorMessage :: ErrMsg -> String
showErrorMessage = \case
  TypecheckError e -> e
  KindcheckError e -> e
  ParseError e -> e
  ClassEnvError e -> e
  RuntimeError e -> e


showError :: ErrMsg -> String
showError em = showErrorType em <> ": " <> showErrorMessage em


