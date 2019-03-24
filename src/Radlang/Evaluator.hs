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
import           Radlang.Types


-- |Get value by name
dataByName :: Name -> Evaluator Data
dataByName n = idByName n >>= dataById


-- |Get value by store id
dataById :: DataId -> Evaluator Data
dataById i = do
  m <- gets _dsMap
  case M.lookup i m of
    Nothing -> runtimeError $ "dataById: no such id " <> show i <>
      "\nKnown ids are: " <> show (M.keys m)
    Just x -> pure x


-- |Get store id of a variable by name
idByName :: Name -> Evaluator DataId
idByName n = do
  m <- asks _envNamespace
  case M.lookup n m of
    Nothing -> runtimeError $ "idByName: no such name " <> show n <>
      "\nKnown ids are: " <> show (M.keys m)
    Just x -> pure x


-- |Update namespace by a single namespace entry
withAssign :: (Name, DataId) -> Evaluator a -> Evaluator a
withAssign (n, d) = local $ over envNamespace (M.insert n d)


-- |Modify action to be ran in different namespace
withNamespace :: Namespace -> Evaluator a -> Evaluator a
withNamespace = local . set envNamespace


-- |Modify action to be ran with updated definition stacktrace
withStackElem :: String -> Evaluator a -> Evaluator a
withStackElem s = local $ over envDefStacktrace (s:)


-- |Modify action to be ran with updated evaluation stacktrace
withEvalStackElem :: String -> Evaluator a -> Evaluator a
withEvalStackElem s = local $ over envEvalStacktrace (s:)


-- |Modify action to be ran with updated stacktrace
withStackElems :: String -> Evaluator a -> Evaluator a
withStackElems s = local $ over envDefStacktrace (s:) . over envEvalStacktrace (s:)


-- |Modify action to be ran with different stacktrace
withDefStacktrace :: Stacktrace -> Evaluator a -> Evaluator a
withDefStacktrace st = local $ set envDefStacktrace st


-- |Get stacktraces from current environment
getStacktraces :: Evaluator (Stacktrace, EvalStacktrace)
getStacktraces = liftA2 (,) (asks _envDefStacktrace) (asks _envEvalStacktrace)


-- |Insert data over certain id
putData :: DataId -> Data -> Evaluator ()
putData i d = modify $ over dsMap (M.insert i d)


-- |Get current namespace
getNamespace :: Evaluator Namespace
getNamespace = asks _envNamespace


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
newtype DataSubst = DataSubst {dsubMap :: M.Map Name Data}


-- |Union two data substitutions
unionSubst :: DataSubst -> DataSubst -> DataSubst
unionSubst (DataSubst s1) (DataSubst s2) = DataSubst $ M.union s1 s2


-- |Try to match data to pattern and return unifying substitution if possible
matchDataToPattern :: Pattern -> Data -> Evaluator (Maybe DataSubst)
matchDataToPattern pat dat = case pat of
  PVar n -> pure $ Just $ DataSubst $ M.singleton n dat
  PWildcard -> pure $ Just $ DataSubst M.empty
  PAs n p -> do
    pp <- matchDataToPattern p dat
    pure $ DataSubst . M.insert n dat . dsubMap <$> pp
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
          pure $ fmap (foldl (\s s1 -> DataSubst $ M.union (dsubMap s) (dsubMap s1)) (DataSubst M.empty)) msubs
        else pure Nothing
      _ -> wtf $ "Illegal ADT match:\ndata=" <> show sdat <>
                             ",\nname=" <> n <> ", args=" <> show pts


-- |Apply data substitution to current namespace
applyDataSubst :: DataSubst -> Evaluator Namespace
applyDataSubst (DataSubst sub) = do
  let assgs = M.toList sub
  ns <- getNamespace
  ids <- traverse (\(_, d) -> newData d) assgs
  pure $ M.union (M.fromList $ zip (fmap fst assgs) ids) ns


-- |Evaluate typed expression
eval :: TypedExpr -> Evaluator Data
eval = \case
  TypedVal n -> withStackElems ("reading var " <> n) $ dataByName n
  TypedLit l -> case l of
    LitInt i -> pure $ Strict $ DataInt i
    LitString s ->
      let folder el li = Strict $ DataADT "Cons" [ Strict $ DataChar el, li]
      in pure $ foldr folder (Strict $ DataADT "Nil" []) s
    LitChar c -> pure $ Strict $ DataChar c
  TypedApplication f a -> do
    fd <- force =<< eval f
    aId <- lazyExpr a
    case fd of
      DataFunc name func -> withStackElems name $ dataById aId >>= func
      _                  -> wtf $ "Call not a function! " <> show fd
  TypedLet assgs e -> withStackElems "let expression" $ do
    ns <- getNamespace

    let aslist = M.toList assgs
        names = fmap fst aslist

    ids <- traverse (const newId) names

    let recNs = foldr (uncurry M.insert)
          ns (zip names ids)

        domainGuard :: Evaluator a
        domainGuard = runtimeError "Out of domain"

        bindings :: Evaluator Data -> Int -> Name -> [([Pattern], TypedExpr, DataSubst)]
                 -> Evaluator Data
        bindings prevGuard level name alts =
          let (finalized, functions) = partition (\(ps, _, _) -> null ps) alts
              newGuard = if null finalized then prevGuard else do
                let ([], te, ds) = head finalized
                newns <- applyDataSubst ds
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

    withNamespace recNs $ do
      dats <- flip mapM aslist $
              (\(n, (_, a)) -> do
                  let binding = bindings domainGuard 0 n (fmap (\(ps, te) -> (ps, te, DataSubst M.empty)) a)
                  Ref <$> newLazy binding
              )

      forM_ (zip ids dats) $ uncurry putData

      withStackElems "let evaluation" $ eval e


-- |Run evaluator and extract the result
runEvaluator :: Namespace
             -> (M.Map DataId Data)
             -> TypeEnv
             -> Evaluator a
             -> Either ErrMsg a
runEvaluator ns ds ts (Evaluator e)
  = flip evalState (Dataspace ds (M.size ds))
  $ flip runReaderT (Env ns ts [] [])
  $ runExceptT e


-- |Run evaluator, but keep the dataspace
runEvaluatorWithState :: Evaluator a -> (Either ErrMsg a, Dataspace)
runEvaluatorWithState (Evaluator e)
  = flip runState (Dataspace M.empty 0)
  $ flip runReaderT (Env M.empty (TypeEnv M.empty) [] [])
  $ runExceptT e
