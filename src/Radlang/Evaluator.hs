{-# LANGUAGE MultiWayIf          #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- |This module is responsible for evaluation of Expr tree into Data
module Radlang.Evaluator where

import           Control.Applicative
import           Control.Lens               hiding (Lazy, Strict, (<~))
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State.Strict
import           Data.List
import qualified Data.Map.Strict            as M
import           Data.Maybe
import           Prelude                    hiding (lookup)

import           Radlang.Error
import           Radlang.DependencyAnalysis
import           Radlang.Types
-- import Radlang.Test
import Debug.Trace

-- |Get value by name and desired type
dataByName :: Type -> Name -> Evaluator Data
dataByName t n = idByName t n >>= dataById


-- |Get value by store id
dataById :: DataId -> Evaluator Data
dataById i = do
  m <- gets _evstDataspace
  case M.lookup i m of
    Nothing -> wtf $ "dataById: no such id " <> show i <>
      "\nKnown ievst are: " <> show (M.keys m)
    Just x -> pure x


-- |Get store id of a variable by name and desired type
idByName :: Type -> Name -> Evaluator DataId
idByName t n = do
  ns <- asks _evenvNamespace
  ps <- asks _evenvPolyspace
  case mplus (M.lookup n ns) (M.lookup n ps >>= idByType t) of
    Just i -> pure i
    Nothing -> wtf $ "idByName: no such name " <> n <> " of type " <> show t


-- |Finds the most matching data id by type. "Most matching" is determined by the number of matched rigid variables
idByType :: Type -> [(Type, DataId)] -> Maybe DataId
idByType t propos =
  let matches = mapMaybe (\(tp, i) -> typesMatch t tp <&> flip (,) i) propos
  in trace ("MATCHES FOR " <> show t <> " IN\n" <> show (propos) <> " ARE\n" <> show matches) $ if null matches then Nothing
     else Just (snd $ maximum matches)


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


-- |Get current polyspace
getPolyspace :: Evaluator Polyspace
getPolyspace = asks _evenvPolyspace


-- |Create new lazy thunk from evaluator and return id assigned to it
newLazy :: Evaluator Data -> Evaluator DataId
newLazy e = do
  i <- newId
  ns <- getNamespace
  (st, _) <- getStacktraces
  putData i $ Lazy ns st i e
  pure i


-- |Create new lazy thunk from expression and return id assigned to it
lazyExpr :: TypedExpr -> Evaluator DataId
lazyExpr e =newLazy (eval e)


-- |Insert strict data into dataspace and return its id
newStrict :: StrictData -> Evaluator DataId
newStrict d = do
  i <- newId
  putData i $ Strict $ d
  pure i


-- |Insert data into fresh place and return its id
newData :: Data -> Evaluator DataId
newData d = do
  i <- newId
  putData i d
  pure i


-- |Evaluate thunk into weak-head normal form
force :: Data -> Evaluator StrictData
force (Strict d) = pure d
force (Ref i) = force =<< dataById i
force (Lazy ns st i e) = do
  forced <- force =<< withDefStacktrace st
    (withEvalStackElem ("forcing " <> show i) $ (withNamespace ns e))
  putData i (Strict forced)
  pure forced


-- |Perform deep evaluation and remove all thunks from the data
deepForce :: Data -> Evaluator StrictData
deepForce (Strict d) = case d of
  DataADT n args -> DataADT n . fmap Strict <$> mapM deepForce args
  _              -> pure d
deepForce (Ref i) = deepForce =<< dataById i
deepForce (Lazy ns st i e) = do
  forced <- deepForce =<< withDefStacktrace st (withNamespace ns e)
  putData i (Strict forced)
  pure forced


-- |Data substitution used to resolve pattern matching
newtype DataSubst = DataSubst {evstubMap :: M.Map Name Data} deriving Show


-- |Union two data substitutions
unionSubst :: DataSubst -> DataSubst -> DataSubst
unionSubst (DataSubst s1) (DataSubst s2) = DataSubst $ M.union s1 s2


-- |Build data definition from bindings
processSingleBindings :: Name -> [([Pattern], TypedExpr, DataSubst)] -> Evaluator Data
processSingleBindings =
  let domainGuard :: Evaluator a
      domainGuard = runtimeError "Out of domain"

      bindings :: Evaluator Data -> Int -> Name -> [([Pattern], TypedExpr, DataSubst)]
               -> Evaluator Data
      bindings prevGuard level name alts = --trace ("FOR " <> name <> " ALTS " <> show alts) $
        let (finalized, functions) = partition (\(ps, _, _) -> null ps) alts
            newGuard = if null finalized then prevGuard else do
              -- traceM $ name <> " ::: " <> show finalized
              let ([], te, evst) = head finalized
              newns <- applyDataSubst evst
              ii <- withNamespace newns (lazyExpr te)
              pure $ Ref ii
        in if | null functions && null finalized -> prevGuard
              | not (null functions) && not (null finalized) -> wtf "pattern number exploited"
              | null functions -> newGuard
              | otherwise -> getNamespace >>= \myNs ->
                  let asFunction :: Data -> Evaluator Data
                      asFunction d = do
                        (conts :: [([Pattern], TypedExpr, DataSubst)]) <-
                          let extractor ((p:ps), te, s) = do
                                msub <- matchDataToPattern p d
                                pure $ fmap (\sub -> (ps, te, unionSubst sub s)) msub
                              extractor _ = wtf "extractor match fail"
                          in mapMaybe id <$> mapM extractor functions
                        bindings newGuard (level + 1) name conts
                  in pure $ Strict $ DataFunc
                     (name <> "#" <> show level) $ withNamespace myNs . asFunction
  in bindings domainGuard 0


-- |Build dataspace and namespace from set of bindings
processBindings :: TypedBindings -> Evaluator Namespace
processBindings tbnevst = do
  ns <- getNamespace

  let aslist = M.toList tbnevst
      names = fmap fst aslist

  ievst <- traverse (const newId) names

  let recNs = foldr (uncurry M.insert) ns (zip names ievst)

  withNamespace recNs $ do
    dats <- flip mapM aslist $
            (\(n, (_, a)) -> fmap Ref . newLazy $
              processSingleBindings n (fmap (\(ps, te) -> (ps, te, DataSubst M.empty)) a)
            )

    forM_ (zip ievst dats) $ uncurry putData
  pure recNs


-- |Build dataspace and namespace from set of polymorphic bindings
processPolyBindings :: PolyBindings -> Evaluator Polyspace
processPolyBindings pb = fmap M.fromList $ forM (M.toList pb) $ \(n, tdl) -> do
  let processSinglePoly t dd = do
        d <- processSingleBindings ("impl " <> n <> " for " <> show t)
          $ fmap (\(ps, te) -> (ps, te, DataSubst M.empty)) dd
        -- traceM $ "DUPA " <> show dd <> "\n\n"
        i <- newData d
        pure (t, i)
  is <- mapM (uncurry processSinglePoly) tdl
  pure $ (n, is)


-- |Try to match data to pattern and return unifying substitution if possible
matchDataToPattern :: Pattern -> Data -> Evaluator (Maybe DataSubst)
matchDataToPattern pat dat = case pat of
  PVar n -> pure $ Just $ DataSubst $ M.singleton n dat
  PWildcard -> pure $ Just $ DataSubst M.empty
  PAs n p -> do
    pp <- matchDataToPattern p dat
    pure $ DataSubst . M.insert n dat . evstubMap <$> pp
  PLit l -> do
    sdat <- force dat
    case (l, sdat) of
      (LitInt li, DataInt di) ->
        if li == di
        then pure $ Just $ DataSubst M.empty
        else pure Nothing
      (LitChar lc, DataChar dc) ->
        if lc == dc
        then pure $ Just $ DataSubst M.empty
        else pure Nothing
      (LitString [], DataADT "Nil" []) -> pure $ Just $ DataSubst M.empty
      (LitString (c:rests), DataADT "Cons" [d, rest]) -> do
        mc <- matchDataToPattern (PLit $ LitChar c) d
        rc <- matchDataToPattern (PLit $ LitString rests) rest
        pure $ mplus mc rc
      _ -> pure Nothing
  PConstructor n pts -> do
    sdat <- force dat
    case sdat of
      DataADT nadt args ->
        if n == nadt && length args == length pts
        then do
          msubs <- sequence <$> mapM (uncurry matchDataToPattern) (zip pts args)
          pure $ fmap (foldl (\s s1 -> DataSubst $ M.union (evstubMap s) (evstubMap s1)) (DataSubst M.empty)) msubs
        else pure Nothing
      _ -> wtf $ "Illegal ADT match:\ndata=" <> show sdat <>
                             ",\nname=" <> n <> ", args=" <> show pts


-- |Apply data substitution to current namespace
applyDataSubst :: DataSubst -> Evaluator Namespace
applyDataSubst (DataSubst sub) = do
  let assgs = M.toList sub
  ns <- getNamespace
  ievst <- traverse (\(_, d) -> newData d) assgs
  pure $ M.union (M.fromList $ zip (fmap fst assgs) ievst) ns


-- |Evaluate typed expression
eval :: TypedExpr -> Evaluator Data
eval = \case
  TypedVal t n -> trace ("EVALUATING " <> n <> " OF TYPE " <> show t) $ dataByName t n
  TypedLit _ l -> case l of
    LitInt i -> pure $ Strict $ DataInt i
    LitString s ->
      let folder el li = Strict $ DataADT "Cons" [Strict $ DataChar el, li]
      in pure $ foldr folder (Strict $ DataADT "Nil" []) s
    LitChar c -> pure $ Strict $ DataChar c
  TypedApplication _ f a -> do
    fd <- force =<< eval f
    aId <- lazyExpr a
    case fd of
      DataFunc name func -> withStackElems name $ dataById aId >>= func
      _                  -> wtf $ "Call not a function! " <> show fd
  TypedLet _ assgs e -> withStackElems "let expression" $ do
    assgsNs <- processBindings assgs
    withNamespace assgsNs $ withStackElems "let evaluation" $ eval e


evalProgram :: TypedProgram -> Evaluator StrictData
evalProgram tp = do
  ns <- processBindings $ tprgBindings tp
  ps <- processPolyBindings $ tprgPolyBindings tp
  case M.lookup "main" (tprgBindings tp) of
    Nothing -> languageError "No `main` function defined!"
    Just (t, _) ->
      withNamespace ns $ withPolyspace ps $ withStackElems "main" $ eval (TypedVal t "main") >>= deepForce


-- |Perform evaluation of the main value from the program
runProgram :: TypedProgram -> Either ErrMsg StrictData
runProgram tp = --trace (prettyBnds 0 (tprgBindings tp)) $
  runEvaluator (tprgNamespace tp) (tprgDataspace tp) $ evalProgram tp


-- |Run evaluator and extract the result
runEvaluator :: Namespace
             -> Dataspace
             -> Evaluator a
             -> Either ErrMsg a
runEvaluator ns evst (Evaluator e)
  = flip evalState (EvaluationState evst (M.size evst))
  $ flip runReaderT (EvaluationEnv ns M.empty M.empty [] [])
  $ runExceptT e
