-- |Module that contains error handling related utils
{-# LANGUAGE FlexibleContexts #-}
module Radlang.Error where

import           Control.Monad.Except
import           Control.Monad.Reader

import           Radlang.Types


-- |Throw an error that indicates typing problems
typecheckError :: MonadError ErrMsg m => String -> m a
typecheckError = throwError . TypecheckError


-- |Throw an error that is caused by illegal use of the language, however it
--is correct in terms of parsing
languageError :: MonadError ErrMsg m => String -> m a
languageError = throwError . LanguageError


-- |Throw an error that indicates kindchecking problem
kindcheckError :: MonadError ErrMsg m => String -> m a
kindcheckError = throwError . KindcheckError


-- |Throw an error that is related to parsing
parseError :: MonadError ErrMsg m => String -> m a
parseError = throwError . ParseError


-- |Throw an error that indicates incorrect use of a interface
interfaceEnvError :: MonadError ErrMsg m => String -> m a
interfaceEnvError = throwError . InterfaceEnvError


-- |Throw an error that occured during runtime from users fault (eg. division by zero)
runtimeError :: String -> Evaluator a
runtimeError s = do
  st <- asks _envDefStacktrace
  est <- asks _envEvalStacktrace
  throwError $ RuntimeError st est s


-- |Get the information of the type of an error
showErrorType :: ErrMsg -> String
showErrorType = \case
  TypecheckError _ -> "Typecheck error"
  LanguageError _ -> "Language error"
  KindcheckError _ -> "Kindcheck error"
  ParseError _ -> "Parse error"
  InterfaceEnvError _ -> "While building interface environment"
  RuntimeError _ _ _ -> "Runtime error"


-- |Get the message of an error
showErrorMessage :: ErrMsg -> String
showErrorMessage = \case
  TypecheckError e -> e
  LanguageError e -> e
  KindcheckError e -> e
  ParseError e -> e
  InterfaceEnvError e -> e
  RuntimeError dst est e ->
    let enum = fmap (uncurry $ (<>) . (<>". ") . show) . zip [(1::Int)..]
    in e <> "\nDefinition Stacktrace:\n" <> unlines (enum dst)
    <> "\nEvaluation stacktrace:\n" <> unlines (enum est)


-- |Print all error information
showError :: ErrMsg -> String
showError em = showErrorType em <> ": " <> showErrorMessage em


-- |"What a Terrible Failure" – internall error that should never happen. It may be thrown only
-- as a result of a bug.
wtf :: String -> a
wtf = error . ("WTF: "<>)
