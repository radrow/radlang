module Radlang.EvaluationUtils where

import Control.Monad.State
import Control.Monad.Reader
import Control.Applicative
import Control.Lens hiding (Strict, Lazy)
import qualified Data.Map.Strict as M
import Data.Maybe

import Radlang.Types
import Radlang.Error

import Debug.Trace

typeByName :: Name -> Evaluator Type
typeByName n = asks (M.lookup n . _evenvTypespace) >>= \case
  Just t -> pure t
  Nothing -> do
    i <- newId
    pure (TypeVarWobbly (TypeVar ("_RTIME_" <> show i) KType))

-- |Evaluate thunk into weak-head normal form
force :: Data -> Evaluator StrictData
force (Strict d) = pure d
force (Lazy ns ts sub st i e) = do
  traceM $ "FORCING LAZY IN SUBST " <> show sub
  s <- asks _evenvSubst
  traceM $ "FORCING SUBST " <> show s
  forced <- force =<< withDefStacktrace st
    (withEvalStackElem ("forcing " <> show i) $ (withSubst sub $ withTypespace ts $ withNamespace ns e))
  putData i (Strict forced)
  pure forced

-- |Get value by name and desired type
dataByName :: Type -> Name -> Evaluator Data
dataByName t n = do
  s <- asks _evenvSubst
  traceM $ "GETTING " <> n <> " : " <> show t <> " WITH SUBST " <> show s
  idByName (substitute s t) n >>= dataById >>= \case
    Strict (DataFunc fname f) -> pure $ Strict $ DataFunc fname (\arg -> withSubst s $ f arg)
    d -> pure d


-- |Get value by store id
dataById :: DataId -> Evaluator Data
dataById i = do
  m <- gets _evstDataspace
  case M.lookup i m of
    Nothing -> wtf $ "dataById: no such id " <> show i <>
      "\nKnown ids are: " <> show (M.keys m)
    Just x -> pure x


-- |Get store id of a variable by name and desired type
idByName :: Type -> Name -> Evaluator DataId
idByName t n = do
  ns <- asks _evenvNamespace
  ps <- asks _evenvPolyspace
  case mplus (M.lookup n ns) (M.lookup n ps >>= idByType t) of
    Just i -> pure i
    Nothing -> wtf $ "idByName: no such name " <> n <> " of type " <> show t <> ". Got " <> show ns


-- |Finds the most matching data id by type. "Most matching" is determined by the number of matched rigid variables
idByType :: Type -> [(Type, DataId)] -> Maybe DataId
idByType t propos =
  let matches = mapMaybe (\(tp, i) -> typesMatch t tp <&> flip (,) i) propos
      best = maximum matches
  in trace ("MATCHES FOR " <> show t <> " IN\n" <> show (propos) <> " ARE\n" <> show matches <> "\nTOOK " <> show (fst best)) $ if null matches then Nothing
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


-- |Modify action to be ran in different type substitution
withSubst :: Substitution -> Evaluator a -> Evaluator a
withSubst = local . set evenvSubst


-- |Modify action to be ran in different typespace
withTypespace :: Typespace -> Evaluator a -> Evaluator a
withTypespace = local . set evenvTypespace


-- |Modify action to be ran in different polyspace. Should be used only during initialization
withPolyspace :: Polyspace -> Evaluator a -> Evaluator a
withPolyspace = local . set evenvPolyspace


-- |Modify action to be ran with updated definition stacktrace
withStackElem :: String -> Evaluator a -> Evaluator a
withStackElem s = local $ over evenvDefStacktrace (s:)


-- |Modify action to be ran with updated evaluation stacktrace
withEvalStackElem :: String -> Evaluator a -> Evaluator a
withEvalStackElem s = local $ over evenvEvalStacktrace (s:)


-- |Modify action to be ran with updated stacktrace
withStackElems :: String -> Evaluator a -> Evaluator a
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


-- |Get current typespace
getTypespace :: Evaluator Typespace
getTypespace = asks _evenvTypespace


-- |Get current polyspace
getPolyspace :: Evaluator Polyspace
getPolyspace = asks _evenvPolyspace
