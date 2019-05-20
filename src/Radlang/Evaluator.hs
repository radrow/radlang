{-# LANGUAGE MultiWayIf          #-}
{-# LANGUAGE RecursiveDo         #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- |This module is responsible for evaluation of Expr tree into Data
module Radlang.Evaluator where

import           Control.Applicative
import           Control.Lens               hiding (Lazy, Strict, (<~))
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State.Strict
import qualified Data.Text as T
import           Data.List
import qualified Data.Map.Strict            as M
import           Data.Maybe
import           Prelude                    hiding (lookup)

import           Radlang.Error
import           Radlang.Types
import           Radlang.Pretty
import           Radlang.InterfaceResolve
import           Radlang.EvaluationUtils
import           Radlang.Typesystem.Typesystem (mgu)

import Debug.Trace


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
lazyExpr :: Expr -> Evaluator Data
lazyExpr e = do
  newLazy (eval e)


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


-- |Perform deep evaluation and remove all thunks from the data
deepForce :: Data -> Evaluator StrictData
deepForce (Strict d) = case d of
  DataADT n args -> DataADT n . fmap Strict <$> mapM deepForce args
  _              -> pure d
deepForce (Lazy ns st i e) = do
  forced <- deepForce =<< (withDefStacktrace st $ withNamespace ns e)
  putData i (Strict forced)
  pure forced


-- |Data substitution used to resolve pattern matching
newtype DataSubst = DataSubst {evstubMap :: M.Map Name Data} deriving Show


-- |Union two data substitutions
unionSubst :: DataSubst -> DataSubst -> DataSubst
unionSubst (DataSubst s1) (DataSubst s2) = DataSubst $ M.union s1 s2


-- |Build data definition from bindings
processSingleBindings :: DataId -> Name -> [([Pattern], Expr, DataSubst)] -> Evaluator Data
processSingleBindings =
  let domainGuard :: Evaluator a
      domainGuard = runtimeError "Out of domain"

      bindings :: Evaluator Data -> Int -> DataId -> Name -> [([Pattern], Expr, DataSubst)]
               -> Evaluator Data
      bindings prevGuard level dataid name alts =
        let (finalized, functions) = partition (\(ps, _, _) -> null ps) alts
            newGuard = if null finalized then prevGuard else do
              let ([], e, dsub) = head finalized
              newns <- applyDataSubst dsub
              (st, _) <- getStacktraces
              withNamespace newns $ eval e
              -- pure $ Lazy newns st dataid (eval e)
        in if | null functions && null finalized -> prevGuard
              | not (null functions) && not (null finalized) -> wtf "pattern number exploited"
              | null functions -> newGuard
              | otherwise -> getNamespace >>= \myNs ->
                  let asFunction :: Data -> Evaluator Data
                      asFunction d = do
                        (conts :: [([Pattern], Expr, DataSubst)]) <-
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


-- |Build dataspace and namespace from set of polymorphic bindings
-- processPolyBindings :: PolyBindings -> Evaluator Namespace
-- processPolyBindings pb = do
--   let polylist :: [(Name, (Qual Type, [(Qual Type, [TypedAlt])]))]
--       polylist = M.toList pb

--       -- Get single method definition and create dictionary reader for it
--       makeMethod :: (Name, Qual Type, [(Qual Type, [TypedAlt])]) -> Evaluator Namespace
--       makeMethod (n, t, defs) = do
--         -- For each method instance (its type, its alts)
--         prens <- forM defs $ \(qt, alts) -> do
--           let dict :: Name
--               dict = case getPreds t \\ getPreds qt of
--                 [cp] -> dictName cp
--                 x -> wtf $ "Class pred failure: " <> T.pack (show x)

--               impls :: Namespace
--               impls = undefined

--               method = DataFunc n $ \ldic -> do
--                 force ldic >>= \case
--                   DataPolyDict dic -> withNamespace dic $ eval (Val n)
--                   x -> wtf $ "This is not poly dict: " <> T.pack (show x)
--           i <- newData $ Strict method

--           pure $ M.insert n i impls
--         pure $ foldr M.union M.empty prens

--   methodNss <- traverse makeMethod $ fmap (\(a,(b,c)) -> (a,b,c)) polylist
--   pure $ foldr M.union M.empty methodNss



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
eval :: Expr -> Evaluator Data
eval = \case
  Val n -> dataByName n
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
      _                  -> wtf $ "Call not a function! " <> T.pack (show fd)
  Let assgs e -> withStackElems "let expression" $ do
    assgsNs <- processBindings assgs
    withNamespace assgsNs $ withStackElems "let evaluation" $ eval e


evalProgram :: Program -> Evaluator StrictData
evalProgram tp = do
  ns <- processBindings $ prgBindings tp
  -- ps <- withNamespace ns $ processPolyBindings $ prgPolyBindings tp
  case M.lookup "main" (prgBindings tp) of
    Nothing -> languageError "No `main` function defined!"
    Just (_) ->
      withNamespace ns $ withStackElems "main" $ eval (Val "main") >>= deepForce >>= \d->
      gets _evstDataspace >>= \ds -> traceM ("MEM USE: " <> show (M.size ds)) >> pure d

buildSpace :: DataMap -> Evaluator Namespace
buildSpace = mapM newData


-- |Perform evaluation of the main value from the program
runProgram :: Program -> Either ErrMsg StrictData
runProgram p =
  runEvaluator M.empty M.empty $ buildSpace (prgDataMap p) >>= \ns -> withNamespace ns (evalProgram p)


-- |Run evaluator and extract the result
runEvaluator :: Namespace
             -> Dataspace
             -> Evaluator a
             -> Either ErrMsg a
runEvaluator ns ds (Evaluator e)
  = flip evalState (EvaluationState ds (if M.null ds then 0 else fst (M.findMax ds) + 1))
  $ flip runReaderT (EvaluationEnv ns [] [])
  $ runExceptT e
