{-# LANGUAGE FlexibleContexts #-}
{-#LANGUAGE MultiWayIf #-}
{-#LANGUAGE ScopedTypeVariables #-}
{-#LANGUAGE OverloadedLists #-}

module Radlang.Typechecker where

import Data.List as DL
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Set(Set)
import Control.Monad.State.Strict
import Control.Monad.Reader
import Control.Monad.Except

import Radlang.Types
import Radlang.Typedefs
import Radlang.Typesystem.Typesystem
import Radlang.Helpers


dbg :: MonadIO m => String -> m ()
dbg = liftIO . putStrLn . ("DEBUG: " <>)


withTypeEnv :: Monad m => TypeEnv -> TypecheckerT m a -> TypecheckerT m a
withTypeEnv te = local $ \s -> s{typeEnv = te}


-- |Find typescheme in type env
lookupType :: HasTypeEnv m => Name -> m TypePoly
lookupType n = getTypeEnv >>= \(TypeEnv te) -> case M.lookup n te of
  Nothing -> throwError $ "Unbound id: " <> n
  Just tp -> pure tp


-- |Extend current substitution with new one
extendSubst :: Substitutor m => Substitution -> m ()
extendSubst s = getSubst >>= \ts -> setSubst $ s <> ts


-- |Unify types and update substitution
unify :: (Substitutor m, MonadIO m) => Type -> Type -> m ()
unify t1 t2 = do
  s <- getSubst
  u <- mgu (substitute s t1) (substitute s t2)
  extendSubst u


-- |Returns new type variable
newVar :: IdSupply m => String -> Kind -> m Type
newVar prefix k = do
  c <- newId
  pure $ TypeVarWobbly $ TypeVar (prefix <> show c) k


-- |Create new type varaibles for each parameter of scheme
freshInst :: IdSupply m => TypePoly -> m (Qual Type)
freshInst (Forall ks qt) = do
  ts <- mapM (newVar "_Inst") ks
  pure $ instantiate ts qt

type Infer e t = e -> TypecheckerT IO ([Pred], t)

inferTypeExpr :: Infer Expr Type
inferTypeExpr = \case
  Val v -> do
    sc <- lookupType v
    (ps :=> t) <- freshInst sc
    pure (ps, t)
  Lit l -> inferTypeLiteral l
  Let binds e -> do
    as <- getTypeEnv
    (ps, as') <- inferTypeBindingGroup binds
    (qs, t) <- withTypeEnv (as' <> as) (inferTypeExpr e)
    pure (ps ++ qs, t)
  Application f a -> do
    (ps, tf) <- inferTypeExpr f
    (qs, ta) <- inferTypeExpr a
    t <- newVar "_FunRes" KType
    unify (fun ta t) tf
    pure (ps ++ qs, t)
  _ -> error "infer expr case not implemented"

inferTypeLiteral :: Infer Literal Type
inferTypeLiteral = \case
  -- LitInt _ -> newVar "_LI" KType >>= \v -> pure ([IsIn "Num" v], v)
  LitInt _ -> pure ([], tInt)
  LitString _ -> pure ([], tString)

inferTypePattern :: Infer Pattern (TypeEnv, Type)
inferTypePattern = \case
  PVar i -> newVar "_PV" KType >>= \v ->
    pure ([], (TypeEnv $ M.singleton i (toTypePoly v), v))
  PWildcard -> newVar "_PW" KType >>= \v -> pure ([], (TypeEnv M.empty, v))
  PAs i patt -> do
    (ps, ((TypeEnv ts), t)) <- inferTypePattern patt
    pure (ps, (TypeEnv $ M.insert i (toTypePoly t) ts, t))
  PLit l -> inferTypeLiteral l >>= \(ps, t) -> pure (ps, (TypeEnv M.empty, t))
  PConstructor cname pats -> do
    sc <- lookupType cname
    (ps, (tspace, ts)) <- inferTypePatterns pats
    t' <- newVar "_PC" KType
    (qs :=> t) <- freshInst sc
    unify t (S.foldr fun t' ts)
    pure (ps ++ qs, (tspace, t'))

inferTypePatterns :: Infer [Pattern] (TypeEnv, Set Type)
inferTypePatterns pats = do
  psats <- mapM inferTypePattern pats
  let typeEnvJoin = foldr mappend (TypeEnv M.empty)
      ps = join $ fmap (\(x,(_,_)) -> x) psats
      as = typeEnvJoin $ fmap (\(_,(x,_)) -> x) psats
      ts = fmap (\(_,(_,x)) -> x) psats
  pure (ps, (as, S.fromList ts))


inferTypeAlt :: Infer Alt Type
inferTypeAlt (pats, e) = do
  as <- getTypeEnv
  (ps, (as', ts)) <- inferTypePatterns pats
  (qs, t) <- withTypeEnv (as' <> as) (inferTypeExpr e)
  pure (ps ++ qs, S.foldr fun t ts)


inferTypeAlts :: [Alt] -> Type -> TypecheckerT IO [Pred]
inferTypeAlts alts t = do
  psts <- mapM inferTypeAlt alts
  void $ mapM (unify t) (fmap snd psts)
  pure (join $ fmap fst psts)


-- |Split predicates on deferred and contraints. fs are fixed variables and gs are varaibles over which we want to quantify
split :: (HasClassEnv m, MonadIO m)
      => [TypeVar] -> [TypeVar] -> [Pred] -> m ([Pred], [Pred])
split fs gs ps = do
  ps' <- reduce ps
  let (ds, rs) = partition (all (`elem` fs) . free) ps'
  rs' <- defaultedPreds (fs ++ gs) rs
  pure (ds, rs \\ rs')


ambiguities :: [TypeVar] -> [Pred] -> [Ambiguity]
ambiguities vs ps = fmap (\v -> (v, filter (elem v . free) ps)) $ S.toList (free ps) \\ vs


candidates :: (HasClassEnv m, MonadIO m) => Ambiguity -> m [Type]
candidates (v, qs) = getClassEnv >>= \ce ->
  let is = fmap (\(IsIn i _) -> i) qs
      ts = fmap (\(IsIn _ t) -> t) qs
      -- filt :: [Type] -> m [Type]
      filt tts = flip filterM tts $ \t ->
        and <$> mapM (entail []) [IsIn i t | i <- is]
  in
    if all ((TypeVarWobbly v)==) ts
     && all (`M.member` stdClasses) is
     && any (`M.member` stdNumClasses) is
     -- then filt (S.toList $ defaults ce)
    then filt [def | ii <- is, def <- maybe [] id $ M.lookup ii (defaults ce)]
     -- && any (`S.member` numClasses) is
     -- then filt (S.toList $ defaults ce)
     else pure []



withDefaults :: (HasClassEnv m, MonadIO m)
             => ([Ambiguity] -> [Type] -> b) -> [TypeVar] -> [Pred] -> m b
withDefaults f vs ps = do
  let vps = ambiguities vs ps
  tss <- mapM candidates vps
  case find (null . fst) (zip tss vps) of
    Just (_, bad) -> throwError $ "Cannot resolve ambiguity: candidates for " <> show bad <> " are empty"
    Nothing -> pure $ f vps (fmap head tss)

defaultedPreds :: (HasClassEnv m,
                   MonadIO m)
               => [TypeVar] -> [Pred] -> m [Pred]
defaultedPreds = withDefaults (\vps _ -> join (fmap snd vps))


defaultSubst :: (HasClassEnv m, MonadIO m)
             => [TypeVar] -> [Pred] -> m Substitution
defaultSubst  = withDefaults (\vps ts -> Subst $ M.fromList $ zip (fmap (tName . fst) vps) ts)


inferTypeExpl :: ExplBinding -> TypecheckerT IO [Pred]
inferTypeExpl (_, (sc, alts)) = do
  (qs :=> t) <- freshInst sc
  ps <- inferTypeAlts alts t
  s <- getSubst
  as <- getTypeEnv
  let qs' = substitute s qs
      t'= substitute s t
      fs = S.toList $ free $ substitute s as
      gs = (S.toList $ free t') \\ fs
      sc' = quantify gs (qs' :=> t')
  ps' <- filterM (\x -> not <$> entail qs' x) (substitute s ps)
  (ds, rs) <- split fs gs ps'
  if | sc /= sc' -> throwError "Signature is too general"
     | not (null rs) -> throwError "Context is too weak"
     | otherwise -> pure ds


restricted :: Foldable t => t ImplBinding -> Bool
restricted bs = any simple bs where
  simple (_, alts) = any (null . fst) alts


inferTypeImpl :: Infer ImplBindings TypeEnv
inferTypeImpl bs = do
  ts <- mapM (const $ newVar "IMPL" KType) bs
  as <- getTypeEnv
  let is = M.keys bs
      scs = fmap toTypePoly ts
      altss = M.elems bs
      as' = (TypeEnv $ M.fromList $ zip is (M.elems scs)) <> as
  pss <- sequence (zipWith (\x y -> withTypeEnv as' $ inferTypeAlts x y) altss (M.elems ts))
  s <- getSubst
  let ps' = substitute s (join pss)
      ts' = substitute s ts
      fs = S.toList $ free (substitute s as)
      vss = fmap (S.toList . free) ts'
      gs = foldr1 union vss \\ fs
  (ds, rs) <- split fs (if null vss then [] else foldr1 intersect vss) ps'
  if restricted (M.toList bs)
    then let gs' = filter (`S.member` free rs) gs
             scs' = M.elems $ fmap (quantify gs' . ([] :=>)) ts'
    in pure (ds ++ rs, TypeEnv $ M.fromList $ zip is scs')
    else let scs' = M.elems $ fmap (quantify gs . (rs :=>)) ts'
    in pure (ds, TypeEnv $ M.fromList $ zip is scs')


inferTypeBindingGroup :: Infer BindingGroup TypeEnv
inferTypeBindingGroup (es, iss) = do
  as <- getTypeEnv
  let as' = -- assumptions made out of explicit bindings
        TypeEnv $ foldr (\(v, (sc, _)) m -> M.insert v sc m) M.empty (M.toList es)
  (ps, as'') <- inferTypeSeq (withTypeEnv (as' <> as) . inferTypeImpl) iss
  qss <- mapM (withTypeEnv (as'' <> as' <> as) . inferTypeExpl) (M.toList es)
  pure (ps ++ join qss, as'' <> as')


inferTypeSeq :: Infer bg TypeEnv -> Infer [bg] TypeEnv
inferTypeSeq ti = \case
  [] -> pure ([], mempty)
  (bs:bss) -> do
    as <- getTypeEnv
    (ps, as') <- ti bs
    (qs, as'') <- withTypeEnv (as' <> as) (inferTypeSeq ti bss)
    pure (ps ++ qs, as'' <> as')


inferTypeBindingGroups :: [BindingGroup] -> TypecheckerT IO TypeEnv
inferTypeBindingGroups bgs = do
  (ps, as') <- inferTypeSeq inferTypeBindingGroup bgs
  s <- getSubst
  rs <- reduce (substitute s ps)
  s' <- defaultSubst [] rs
  pure $ substitute (s' <> s) as'


-- |Evaluation of typechecker
runTypecheckerT :: ClassEnv
                -> TypeEnv
                -> TypecheckerConfig
                -> TypecheckerT IO TypeEnv
                -> IO (Either ErrMsg TypeEnv)
runTypecheckerT ce te tc
  = flip evalStateT (TypecheckerState 0 mempty)
  . flip runReaderT (TypecheckerEnv ce te tc)
  . runExceptT . (\(Typechecker t) -> t)

-- |Toplevel typechecking of program
typecheck :: TypecheckerConfig -> Program -> IO (Either ErrMsg TypeEnv)
typecheck tc p = runTypecheckerT
  (prgClassEnv p)
  (TypeEnv $ M.union (types stdTypeEnv) (types $ prgTypeEnv p)) -- (prgTypeEnv p)
  tc (inferTypeBindingGroups $ prgBindings p)
