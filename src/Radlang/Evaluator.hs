{-# LANGUAGE MultiWayIf          #-}
{-# LANGUAGE RecursiveDo         #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- |This module is responsible for evaluation of EvalExpr tree into Data
module Radlang.Evaluator(runProgram, force, deepForce) where

import           Control.Applicative
import           Control.Lens               hiding (Lazy, Strict, (<~))
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State.Strict
import qualified Data.Text as T
import           Data.Text(Text)
import           Data.List
import qualified Data.Map.Strict            as M
import           Data.Maybe
import           Prelude                    hiding (lookup)

import           Radlang.Error
import           Radlang.Types


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


-- |Modify action to be ran in different namespace
withNamespace :: Namespace -> Evaluator a -> Evaluator a
withNamespace = local . set evenvNamespace


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


-- |Create new lazy thunk from evaluator and return id assigned to it
newLazy :: Evaluator Data -> Evaluator Data
newLazy e = do
  i <- newId
  ns <- getNamespace
  (st, _) <- getStacktraces
  let laz = Lazy ns st i e
  putData i laz
  pure laz


-- |Create new lazy thunk from expression and return id assigned to it
lazyExpr :: EvalExpr -> Evaluator Data
lazyExpr e = do
  newLazy (eval e)


-- |Insert data into fresh place and return its id
newData :: Data -> Evaluator DataId
newData d = do
  i <- newId
  putData i d
  pure i


-- |Evaluate thunk into weak-head normal form
force :: Data -> Evaluator StrictData
force (Strict d) = pure d
force (Lazy ns st i e) = do
  forced <- force =<< withDefStacktrace st
    (withEvalStackElem ("forcing " <> T.pack (show i)) $ withNamespace ns e)
  putData i (Strict forced)
  pure forced
force (PolyDict acc sup p) = pure $ DataPolyDict acc sup p


-- |Perform deep evaluation and remove all thunks from the data
deepForce :: Data -> Evaluator StrictData
deepForce (Strict d) = case d of
  DataADT n args -> DataADT n . fmap Strict <$> mapM deepForce args
  _              -> pure d
deepForce (Lazy ns st i e) = do
  forced <- deepForce =<< (withDefStacktrace st $ withNamespace ns e)
  putData i (Strict forced)
  pure forced
deepForce (PolyDict load sup ns) = pure $ DataPolyDict load sup ns


-- |Data substitution used to resolve pattern matching
newtype DataSubst = DataSubst {evstubMap :: M.Map Name Data}


-- |Union two data substitutions
unionSubst :: DataSubst -> DataSubst -> DataSubst
unionSubst (DataSubst s1) (DataSubst s2) = DataSubst $ M.union s1 s2


-- |Build data definition from bindings
processSingleBindings :: DataId -> Name -> [([Pattern], EvalExpr, DataSubst)] -> Evaluator Data
processSingleBindings =
  let domainGuard :: Evaluator a
      domainGuard = runtimeError "Out of domain"

      bindings :: Evaluator Data -> Int -> DataId -> Name -> [([Pattern], EvalExpr, DataSubst)]
               -> Evaluator Data
      bindings prevGuard level dataid name alts =
        let (finalized, functions) = partition (\(ps, _, _) -> null ps) alts
            newGuard = if null finalized then prevGuard else do
              let ([], e, dsub) = head finalized
              newns <- applyDataSubst dsub
              withNamespace newns $ eval e
        in if | null functions && null finalized -> prevGuard
              | not (null functions) && not (null finalized) -> wtf "pattern number exploited"
              | null functions -> newGuard
              | otherwise -> getNamespace >>= \myNs ->
                  let asFunction :: Data -> Evaluator Data
                      asFunction d = do
                        (conts :: [([Pattern], EvalExpr, DataSubst)]) <-
                          let extractor ((p:ps), te, s) = do
                                mdsub <- matchDataToPattern p d
                                pure $ fmap (\dsub -> (ps, te, unionSubst dsub s)) mdsub
                              extractor _ = wtf "extractor match fail"
                          in mapMaybe id <$> mapM extractor functions
                        bindings newGuard (level + 1) dataid name conts
                  in pure $ Strict $ DataFunc (name <> "#" <> T.pack (show level)) $ \argd ->
                      withNamespace myNs $ asFunction argd
  in bindings domainGuard 0


-- |Build dataspace and namespace from set of bindings
processBindings :: Bindings -> Evaluator Namespace
processBindings bnevst = do
  ns <- getNamespace
  (st, _) <- getStacktraces

  let aslist = M.toList bnevst
      names = fmap fst aslist

  ievst <- traverse (const newId) names

  let recNs = foldr (uncurry M.insert) ns (zip names ievst)

  withNamespace recNs $ do
    let dats = flip fmap (zip ievst aslist) $
            (\(i, (n, a)) -> Lazy recNs st i $
              processSingleBindings i n (fmap (\(ps, te) -> (ps, te, DataSubst M.empty)) a)
            )

    forM_ (zip ievst dats) $ uncurry putData
  pure recNs


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
      _ -> wtf $ "Illegal ADT match:\ndata=" <> T.pack (show sdat) <> ",\nname=" <> n <> ", args=" <> T.pack (show pts)


-- |Apply data substitution to current namespace
applyDataSubst :: DataSubst -> Evaluator Namespace
applyDataSubst (DataSubst sub) = do
  let assgs = M.toList sub
  ns <- getNamespace
  ievst <- traverse (\(_, d) -> newData d) assgs
  pure $ M.union (M.fromList $ zip (fmap fst assgs) ievst) ns


-- |Evaluate typed expression
eval :: EvalExpr -> Evaluator Data
eval = \case
  Val n -> dataByName n
  Dict n -> dataByName n
  Lit l -> case l of
    LitInt i -> pure $ Strict $ DataInt i
    LitString s ->
      let folder el li = Strict $ DataADT "Cons" [Strict $ DataChar el, li]
      in pure $ foldr folder (Strict $ DataADT "Nil" []) s
    LitChar c -> pure $ Strict $ DataChar c
  Application f a -> do
    fd <- force =<< eval f
    alazy <- lazyExpr a
    case fd of
      DataFunc name func ->
        withStackElems name $ func alazy
      DataPolyDict load sups p -> case a of
        Val v ->
          let searchMethod load' sups' p' =
                case M.lookup v p' of
                  Just nv -> fmap Just $ do
                    ns <- getNamespace
                    withNamespace (M.fromList load' <> ns) $ eval $ foldl Application (Val nv) (fmap Val $ reverse (map fst load'))
                  Nothing -> fmap msum $ flip mapM sups' $ \s ->
                    dataByName s >>= \case
                    PolyDict _ sups'' p'' -> searchMethod load' sups'' p''
                    bad -> wtf $ "Not poly dict: " <> T.pack (show bad)
          in fromMaybe (wtf $ "Method not found: \"" <> v <> "\" in " <> T.pack (show fd) <> " known as " <> T.pack (show f))
             <$> searchMethod load sups p
        Dict d -> do
          i <- idByName d
          pure $ PolyDict ((d, i):load) sups p
        Application d1 d2 -> case alazy of
          Lazy _ _ i _ -> do
            let newname = T.pack (show d1 <> show d2)
            pure $ PolyDict ((newname, i):load) sups p
          _ -> wtf "Totally impossible lazy exploit"
        b -> wtf $ "This is not method name nor a dict: " <> T.pack (show b)
      _                  -> wtf $ "Call not a function! " <> T.pack (show fd)
  Let assgs e -> withStackElems "let expression" $ do
    assgsNs <- processBindings assgs
    withNamespace assgsNs $ withStackElems "let evaluation" $ eval e


evalProgram :: Program -> Evaluator StrictData
evalProgram tp = do
  ns <- processBindings $ prgBindings tp
  case M.lookup "main" (prgBindings tp) of
    Nothing -> languageError "No `main` function defined!"
    Just (_) ->
      withNamespace ns $ withStackElems "main" $ eval (Val "main") >>= deepForce

buildSpace :: DataMap -> Evaluator Namespace
buildSpace = mapM newData


-- |Run evaluator and extract the result
runEvaluator :: Namespace
             -> Dataspace
             -> Evaluator a
             -> Either ErrMsg a
runEvaluator ns ds (Evaluator e)
  = flip evalState (EvaluationState ds (if M.null ds then 0 else fst (M.findMax ds) + 1))
  $ flip runReaderT (EvaluationEnv ns [] [])
  $ runExceptT e


-- |Perform evaluation of the main value from the program
runProgram :: Program -> Either ErrMsg StrictData
runProgram p =
  runEvaluator M.empty M.empty $ buildSpace (prgDataMap p) >>= \ns -> withNamespace ns (evalProgram p)
