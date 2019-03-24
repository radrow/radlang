{-# LANGUAGE StrictData #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
-- |This module is responsible for evaluation of Expr tree into Data

module Radlang.Evaluator where

import Control.Applicative
import Control.Monad.State.Strict
import Control.Monad.Reader
import Control.Monad.Except
import Control.Lens hiding (Lazy, Strict, (<~))
import Data.Maybe
import Data.List
import Prelude hiding (lookup)
import qualified Data.Map.Strict as M

import Debug.Trace

import Radlang.Types
import Radlang.Error


dataByName :: Name -> Evaluator Data
dataByName n = idByName n >>= dataById


dataById :: DataId -> Evaluator Data
dataById i = do
  m <- gets _dsMap
  case M.lookup i m of
    Nothing -> runtimeError $ "dataById: no such id " <> show i <>
      "\nKnown ids are: " <> show (M.keys m)
    Just x -> pure x


idByName :: Name -> Evaluator DataId
idByName n = do
  m <- asks _envNamespace
  case M.lookup n m of
    Nothing -> runtimeError $ "idByName: no such name " <> show n <>
      "\nKnown ids are: " <> show (M.keys m)
    Just x -> pure x


withAssign :: (Name, DataId) -> Evaluator a -> Evaluator a
withAssign (n, d) = local $ over envNamespace (M.insert n d)


withNamespace :: Namespace -> Evaluator a -> Evaluator a
withNamespace = local . set envNamespace


withStackElem :: String -> Evaluator a -> Evaluator a
withStackElem s = local $ over envDefStacktrace (s:)


withEvalStackElem :: String -> Evaluator a -> Evaluator a
withEvalStackElem s = local $ over envEvalStacktrace (s:)


withStackElems :: String -> Evaluator a -> Evaluator a
withStackElems s = local $ over envDefStacktrace (s:) . over envEvalStacktrace (s:)


withDefStacktrace :: Stacktrace -> Evaluator a -> Evaluator a
withDefStacktrace st = local $ set envDefStacktrace st


getStacktraces :: Evaluator (Stacktrace, EvalStacktrace)
getStacktraces = liftA2 (,) (asks _envDefStacktrace) (asks _envEvalStacktrace)


putData :: DataId -> Data -> Evaluator ()
putData i d = modify $ over dsMap (M.insert i d)


getNamespace :: Evaluator Namespace
getNamespace = asks _envNamespace


newLazy :: Evaluator Data -> Evaluator DataId
newLazy e = do
  i <- newId
  ns <- getNamespace
  (st, _) <- getStacktraces
  putData i $ Lazy ns st i e
  pure i


lazyExpr :: TypedExpr -> Evaluator DataId
lazyExpr e =newLazy (eval e)


newStrict :: StrictData -> Evaluator DataId
newStrict d = do
  i <- newId
  putData i $ Strict $ d
  pure i


newData :: Data -> Evaluator DataId
newData d = do
  i <- newId
  putData i d
  pure i


force :: Data -> Evaluator StrictData
force (Strict d) = pure d
force (Ref i) = force =<< dataById i
force (Lazy ns st i e) = do
  forced <- force =<< withDefStacktrace st
    (withEvalStackElem ("forcing " <> show i) $ (withNamespace ns e))
  putData i (Strict forced)
  pure forced

deepForce :: Data -> Evaluator StrictData
deepForce (Strict d) = case d of
  DataADT n args -> DataADT n . fmap Strict <$> mapM deepForce args
  _ -> pure d
deepForce (Ref i) = deepForce =<< dataById i
deepForce (Lazy ns st i e) = do
  forced <- deepForce =<< withDefStacktrace st (withNamespace ns e)
  putData i (Strict forced)
  pure forced


newtype DataSubst = DataSubst {dsubMap :: M.Map Name Data}
unionSubst :: DataSubst -> DataSubst -> DataSubst
unionSubst (DataSubst s1) (DataSubst s2) = DataSubst $ M.union s1 s2


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


applyDataSubst :: DataSubst -> Evaluator Namespace
applyDataSubst (DataSubst sub) = do
  let assgs = M.toList sub
  ns <- getNamespace
  ids <- traverse (\(_, d) -> newData d) assgs
  pure $ M.union (M.fromList $ zip (fmap fst assgs) ids) ns


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
      _ -> wtf $ "Call not a function! " <> show fd
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


runEvaluator :: Namespace
             -> (M.Map DataId Data)
             -> TypeEnv
             -> Evaluator a
             -> Either ErrMsg a
runEvaluator ns ds ts (Evaluator e)
  = flip evalState (Dataspace ds (M.size ds))
  $ flip runReaderT (Env ns ts [] [])
  $ runExceptT e

runEvaluatorWithState :: Evaluator a -> (Either ErrMsg a, Dataspace)
runEvaluatorWithState (Evaluator e)
  = flip runState (Dataspace M.empty 0)
  $ flip runReaderT (Env M.empty (TypeEnv M.empty) [] [])
  $ runExceptT e
