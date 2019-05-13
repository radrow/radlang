-- |Module that contains error handling related utils
{-# LANGUAGE FlexibleContexts #-}
module Radlang.Error where

import           Control.Monad.Except
import           Control.Monad.Reader
import           Data.Text as T
import           Data.List as DL

import           Radlang.Types


-- |Throw an error that indicates typing problems
typecheckError :: MonadError ErrMsg m => Text -> m a
typecheckError = throwError . TypecheckError


-- |Throw an error that is caused by illegal use of the language, however it
--is correct in terms of parsing
languageError :: MonadError ErrMsg m => Text -> m a
languageError = throwError . LanguageError


-- |Throw an error that indicates kindchecking problem
kindcheckError :: MonadError ErrMsg m => Text -> m a
kindcheckError = throwError . KindcheckError


-- |Throw an error that is related to parsing
parseError :: MonadError ErrMsg m => Text -> m a
parseError = throwError . ParseError


-- |Throw an error that indicates incorrect use of a interface
interfaceEnvError :: MonadError ErrMsg m => Text -> m a
interfaceEnvError = throwError . InterfaceEnvError


-- |Throw an error that occured during runtime from users fault (eg. division by zero)
runtimeError :: Text -> Evaluator a
runtimeError s = do
  st <- asks _evenvDefStacktrace
  est <- asks _evenvEvalStacktrace
  throwError $ RuntimeError st est s


-- |Get the information of the type of an error
showErrorType :: ErrMsg -> Text
showErrorType = \case
  TypecheckError _ -> "Typecheck error"
  LanguageError _ -> "Language error"
  KindcheckError _ -> "Kindcheck error"
  ParseError _ -> "Parse error"
  InterfaceEnvError _ -> "While building interface environment"
  RuntimeError _ _ _ -> "Runtime error"


-- |Get the message of an error
showErrorMessage :: ErrMsg -> Text
showErrorMessage = \case
  TypecheckError e -> e
  LanguageError e -> e
  KindcheckError e -> e
  ParseError e -> e
  InterfaceEnvError e -> e
  RuntimeError dst est e ->
    let enum = fmap (uncurry $ (<>) . (<>". ") . T.pack . show) . DL.zip [(1::Int)..]
    in e <> "\nDefinition Stacktrace:\n" <> T.unlines (enum dst)
    <> "\nEvaluation stacktrace:\n" <> T.unlines (enum est)


-- |Print all error information
showError :: ErrMsg -> Text
showError em = showErrorType em <> ": " <> showErrorMessage em


-- |"What a Terrible Failure" – internall error that should never happen. It may be thrown only
-- as a result of a bug.
wtf :: Text -> a
wtf = error . ("WTF: "<>) . T.unpack
