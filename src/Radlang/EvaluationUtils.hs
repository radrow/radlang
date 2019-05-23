module Radlang.EvaluationUtils where

import Control.Monad.State
import Control.Monad.Reader
import Control.Applicative
import Control.Lens hiding (Strict, Lazy)
import qualified Data.Map.Strict as M
import Data.Maybe
import Data.Text as T

import Radlang.Types
import Radlang.Error

import Debug.Trace


-- |Evaluate thunk into weak-head normal form
force :: Data -> Evaluator StrictData
force (Strict d) = pure d
force (Lazy ns st i e) = do
  forced <- force =<< withDefStacktrace st
    (withEvalStackElem ("forcing " <> T.pack (show i)) $ withNamespace ns e)
  putData i (Strict forced)
  pure forced
force (PolyDict acc sup p) = pure $ DataPolyDict acc sup p

-- |Get value by name and desired type
dataByName :: Name -> Evaluator Data
dataByName = idByName >=> dataById


-- |Get value by store id
dataById :: DataId -> Evaluator Data
dataById i = do
  m <- gets _evstDataspace
  case M.lookup i m of
    Nothing -> wtf $ "dataById: no such id " <> T.pack (show i) <>
      "\nKnown ids are: " <> T.pack (show (M.keys m))
    Just x -> pure x


-- |Get store id of a variable by name and desired type
idByName :: Name -> Evaluator DataId
idByName n = asks (M.lookup n . _evenvNamespace) >>= \case
  Nothing -> wtf $ "idByName: no such name " <> n
  Just i -> pure i


-- |Finds the most matching data id by type. "Most matching" is determined by the number of matched rigid variables
idByType :: Type -> [(Type, DataId)] -> Maybe DataId
idByType t propos =
  let matches = mapMaybe (\(tp, i) -> typesMatch t tp <&> flip (,) i) propos
      best = Prelude.maximum matches
  in trace ("MATCHES FOR " <> show t <> " IN\n" <> show (propos) <> " ARE\n" <> show matches <> "\nTOOK " <> show (fst best)) $ if Prelude.null matches then Nothing
     else Just (snd best)


-- |Calculate score of match of two types, or return `Nothing` if types don't match
typesMatch :: Type -> Type -> Maybe Int
typesMatch t1 t2 = case (t1, t2) of
  (TypeVarWobbly _, TypeVarWobbly _) -> Just 1
  (TypeVarWobbly _, _) -> Just 0
  (_, TypeVarWobbly _) -> Just 0
  (TypeVarRigid tv1, TypeVarRigid tv2) -> if tv1 == tv2 then Just 1 else Nothing
  (TypeApp tf1 ta1, TypeApp tf2 ta2) ->
    (+) <$> typesMatch tf1 tf2 <*> typesMatch ta1 ta2
  _ -> Nothing


-- |Update namespace by a single namespace entry
withAssign :: (Name, DataId) -> Evaluator a -> Evaluator a
withAssign (n, d) = local $ over evenvNamespace (M.insert n d)


-- |Modify action to be ran in different namespace
withNamespace :: Namespace -> Evaluator a -> Evaluator a
withNamespace = local . set evenvNamespace


-- |Modify action to be ran with updated definition stacktrace
withStackElem :: Text -> Evaluator a -> Evaluator a
withStackElem s = local $ over evenvDefStacktrace (s:)


-- |Modify action to be ran with updated evaluation stacktrace
withEvalStackElem :: Text -> Evaluator a -> Evaluator a
withEvalStackElem s = local $ over evenvEvalStacktrace (s:)


-- |Modify action to be ran with updated stacktrace
withStackElems :: Text -> Evaluator a -> Evaluator a
withStackElems s = local $ over evenvDefStacktrace (s:) . over evenvEvalStacktrace (s:)


-- |Modify action to be ran with different stacktrace
withDefStacktrace :: DefStacktrace -> Evaluator a -> Evaluator a
withDefStacktrace st = local $ set evenvDefStacktrace st


-- |Get stacktraces from current evenvironment
getStacktraces :: Evaluator (DefStacktrace, EvalStacktrace)
getStacktraces = liftA2 (,) (asks _evenvDefStacktrace) (asks _evenvEvalStacktrace)


-- |Insert data over certain id
putData :: DataId -> Data -> Evaluator ()
putData i d = modify $ over evstDataspace (M.insert i d)


-- |Get current namespace
getNamespace :: Evaluator Namespace
getNamespace = asks _evenvNamespace
