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
withStackElem s = local $ over envStacktrace (s:)


withEvalStackElem :: String -> Evaluator a -> Evaluator a
withEvalStackElem s = local $ over envEvalStacktrace (s:)


withStackElems :: String -> Evaluator a -> Evaluator a
withStackElems s = local $ over envStacktrace (s:) . over envEvalStacktrace (s:)


withStacktrace :: Stacktrace -> Evaluator a -> Evaluator a
withStacktrace st = local $ set envStacktrace st


getStacktraces :: Evaluator (Stacktrace, EvalStacktrace)
getStacktraces = liftA2 (,) (asks _envStacktrace) (asks _envEvalStacktrace)


putData :: DataId -> Data -> Evaluator ()
putData i d = modify $ over dsMap (M.insert i d)


getNamespace :: Evaluator Namespace
getNamespace = asks _envNamespace


newLazy :: (Evaluator Data) -> Evaluator DataId
newLazy e = do
  i <- newId
  ns <- getNamespace
  (st, _) <- getStacktraces
  putData i $ Lazy ns st i e
  pure i


lazyExpr :: TypedExpr -> Evaluator DataId
lazyExpr e = newLazy (eval e)


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
  forced <- force =<< withStacktrace st (withNamespace ns e)
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
      _ -> runtimeError "Illegal ADT match"


applyDataSubst :: DataSubst -> Evaluator Namespace
applyDataSubst (DataSubst sub) = do
  let assgs = M.toList sub
  ns <- getNamespace
  ids <- traverse (\(_, d) -> newData d) assgs
  pure $ M.union (M.fromList $ zip (fmap fst assgs) ids) ns


eval :: TypedExpr -> Evaluator Data
eval = \case
  TypedVal n -> dataByName n
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
      _ -> wtf "Call not a function!"
  TypedLet assgs e -> do
    ns <- getNamespace

    let aslist = M.toList assgs
        names = fmap fst aslist

    ids <- traverse (const newId) names

    let recNs = foldr (uncurry M.insert)
          ns (zip names ids)

    let domainGuard :: Evaluator a
        domainGuard = runtimeError "Out of domain"

        bindings :: [([Pattern], TypedExpr, DataSubst)] -> Evaluator Data
        bindings alts = do
          let (finalized, functions) = partition (\(ps, _, _) -> null ps) alts

              asFunction :: Data -> Evaluator Data
              asFunction d = do
                (conts :: [([Pattern], TypedExpr, DataSubst)]) <-
                  let extractor ((p:ps), te, s) = do
                        msub <- matchDataToPattern p d
                        pure $ fmap (\sub -> (ps, te, unionSubst sub s)) msub
                      extractor _ = wtf "extractor match fail"
                  in mapMaybe id <$> mapM extractor functions
                bindings conts

          if | null functions && null finalized -> domainGuard
             | null functions -> do
                 let ([], te, ds) = head finalized
                 newns <- applyDataSubst ds
                 Ref <$> withNamespace newns (lazyExpr te)
             | otherwise -> pure $ Strict $ DataFunc "patternMatch" asFunction

    dats <- flip mapM aslist $
            (\(_, (_, a)) ->
                (withNamespace recNs $
                  Ref <$> newLazy (bindings (fmap (\(ps, te) -> (ps, te, DataSubst M.empty)) a))
                ))

    forM_ (zip ids dats) $ uncurry putData

    withNamespace recNs $ eval e


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

run :: TypedExpr -> (Either ErrMsg StrictData, Dataspace)
run e = runEvaluatorWithState $ eval e >>= force
t :: Type
t = TypeVarRigid $ TypeVar "TYPE" KType
ex :: Integer -> TypedExpr
ex i = TypedApplication
     (TypedLet
       (M.singleton "f" (t, [ ([PLit $ LitInt 4], TypedLit (LitInt 222))
                            , ([PVar "x"], TypedVal "x")
                            ]))
       (TypedVal "f"))
     (TypedLit (LitInt i))

ex2 :: TypedExpr
ex2 = TypedLet (M.singleton "x" (t, [([], TypedLit (LitInt 3))])) (TypedVal "x")

ex3 :: Integer -> Integer -> TypedExpr
ex3 i j = TypedApplication (TypedApplication
     (TypedLet
       (M.singleton "f" (t, [ ([PLit $ LitInt 3, PLit $ LitInt 4], TypedLit (LitInt 222))
                            , ([PLit $ LitInt 3, PVar "x"], TypedVal "x")
                            ]))
       (TypedVal "f"))
     (TypedLit (LitInt i))) (TypedLit (LitInt j))

lazyjeb :: TypedExpr
lazyjeb =
  (TypedLet  -- let
    (M.fromList  -- const _ = 2137
      [ ("const", (t, [
                      ([PWildcard], TypedLit (LitInt 2137))
                      ]))
      -- , ("empty", (t, ([]))) -- empty = undefined
      ]) $ TypedApplication
    (TypedVal "const") -- in (const 1488)
    (TypedLit $ LitInt 1488)
    -- (TypedApplication (TypedVal "empty") (TypedLi(LitIn123)))
  )
