{-# LANGUAGE MultiWayIf          #-}
{-# LANGUAGE OverloadedLists     #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Radlang.Typechecker where

import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State.Strict
import           Data.Functor
import           Data.List                     as DL
import qualified Data.Map.Strict               as M

import           Radlang.Error
import           Radlang.Intro
import           Radlang.Typedefs
import           Radlang.Types
import           Radlang.Typesystem.Typesystem


dbg :: MonadIO m => String -> m ()
dbg s = liftIO $ putStrLn ("DEBUG: " <> s)


-- |Run Typechecker in different type env
withTypeEnv :: Monad m => TypeEnv -> TypecheckerT m a -> TypecheckerT m a
withTypeEnv te = local $ \s -> s{typeEnv = te}


-- |Find typescheme in type env
lookupType :: HasTypeEnv m => Name -> m TypePoly
lookupType n = getTypeEnv >>= \(TypeEnv te) -> case M.lookup n te of
  Nothing -> languageError $ "Unbound id: " <> n <> "\nValid ids are: " <> show (M.keys te)
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


-- |Given `e` infer qualified `t`
type Infer e t = e -> TypecheckerT IO ([Pred], t)


-- |Get type of Expr
inferTypeExpr :: Infer Expr Type
inferTypeExpr = \case
  Val v -> do
    sc <- lookupType v
    (ps :=> t) <- freshInst sc
    pure (ps, t)
  Lit l -> inferTypeLiteral l <&> (\(p, t) -> (p, t))
  Let binds e -> do
    as <- getTypeEnv
    (ps, (as', _)) <- inferTypeBindingGroup binds
    (qs, t) <- withTypeEnv (as' <> as) $ inferTypeExpr e
    pure (ps ++ qs, t)
  Application f a -> do
    (ps, tf) <- inferTypeExpr f
    (qs, ta) <- inferTypeExpr a
    t <- newVar "_FunRes" KType
    unify (fun ta t) tf
    pure (ps ++ qs, t)


-- |Decorate 'Expr' tree with types to match given type
setExprType :: Type -> Expr -> TypecheckerT IO TypedExpr
setExprType t = \case
  Val v -> pure $ TypedVal v
  Lit l -> pure $ TypedLit l
  Let binds e -> do
    as <- getTypeEnv
    (_, (as', tb)) <- inferTypeBindingGroup binds
    typedE <- withTypeEnv (as' <> as) $ setExprType t e
    pure $ TypedLet tb typedE
  Application f a -> do
    (_, tf) <- inferTypeExpr f
    (_, ta) <- inferTypeExpr a
    s <- mgu (fun ta t) tf
    typedf <- setExprType (substitute s tf) f
    typeda <- setExprType (substitute s ta) a
    pure $ TypedApplication typedf typeda


-- |Infer type of literal value
inferTypeLiteral :: Infer Literal Type
inferTypeLiteral = \case
  -- LitInt _ -> newVar "_LI" KType >>= \v -> pure ([IsIn "Num" v], v)
  LitInt _ -> pure ([], tInt)
  LitString _ -> pure ([], tString)
  LitChar _ -> pure ([], tChar)


-- |Infer pattern and get it's type and updated type env
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
    unify t (foldr fun t' ts)
    pure (ps ++ qs, (tspace, t'))


-- |Infer types of multiple patterns
inferTypePatterns :: Infer [Pattern] (TypeEnv, [Type])
inferTypePatterns pats = do
  psats <- mapM inferTypePattern pats
  let typeEnvJoin = foldr mappend (TypeEnv M.empty)
      ps = join $ fmap (\(x,(_,_)) -> x) psats
      as = typeEnvJoin $ fmap (\(_,(x,_)) -> x) psats
      ts = fmap (\(_,(_,x)) -> x) psats
  pure (ps, (as, ts))


-- |Infer type of whole alt
inferTypeAlt :: Infer Alt Type
inferTypeAlt (pats, e) = do
  as <- getTypeEnv
  (ps, (as', ts)) <- inferTypePatterns pats
  (qs, t) <- withTypeEnv (as' <> as) (inferTypeExpr e)
  pure (ps ++ qs, foldr fun t ts)


-- |Decorate alt with type annotations
setAltType :: Type -> Alt -> TypecheckerT IO TypedAlt
setAltType t (pts, expr) = do
  as <- getTypeEnv
  (_, (as', _)) <- inferTypePatterns pts
  let dropFun (TypeApp _ resType) = resType
      dropFun _                   = wtf "Bad alt function type"
      dropFuns [] tp       = tp
      dropFuns (_:rest) tp = dropFuns rest (dropFun tp)
      typeForExpr = dropFuns pts t
  typed <- withTypeEnv (as' <> as) $ setExprType typeForExpr expr
  pure (pts, typed)


-- |Infer type of list of alts, unify them and decorate with type annotations
inferTypeAlts :: Type -> Infer [Alt] (Type, [TypedAlt])
inferTypeAlts t alts = do
  when (length (nub $ fmap (length . fst) alts) > 1) $
    languageError "Different number of patterns"
  psts <- mapM inferTypeAlt alts
  void $ mapM (unify t) (fmap snd psts)
  s <- getSubst
  talts <- forM (zip alts (fmap snd psts)) $ \(al, at) ->
    let sat = substitute s at in setAltType sat al
  pure (join $ fmap fst psts, (substitute s t, talts))


-- |Split predicates on deferred and contraints. fs are fixed variables and gs are varaibles over which we want to quantify
split :: (HasClassEnv m, MonadIO m)
      => [TypeVar] -> [TypeVar] -> [Pred] -> m ([Pred], [Pred])
split fs gs ps = do
  ps' <- reduce ps
  let (ds, rs) = partition (all (`elem` fs) . free) ps'
  rs' <- defaultedPreds (fs ++ gs) rs
  pure (ds, rs \\ rs')


-- |Get all possible ambiguities from type vars that arise from given set of predicates
ambiguities :: [TypeVar] -> [Pred] -> [Ambiguity]
ambiguities vs ps = fmap (\v -> (v, filter (elem v . free) ps)) $ free ps \\ vs


-- |Get all candidates that may resolve ambiguity
candidates :: (HasClassEnv m, MonadIO m) => Ambiguity -> m [Type]
candidates (v, qs) = getClassEnv >>= \ce ->
  let is = fmap (\(IsIn i _) -> i) qs
      ts = fmap (\(IsIn _ t) -> t) qs
      -- filt :: [Type] -> m [Type]
      filt tts = flip filterM tts $ \t ->
        and <$> mapM (entail []) [IsIn i t | i <- is]
  in if all ((TypeVarWobbly v)==) ts
        && all (`M.member` stdClasses) is
        && any (`M.member` stdNumClasses) is
     then filt [def | ii <- is, def <- maybe [] id $ M.lookup ii (defaults ce)]
     else pure []


-- |Check whether all ambiguities can be solved. If so, apply given function to ambiguities
--and first found candidates set
withDefaults :: (HasClassEnv m, MonadIO m)
             => ([Ambiguity] -> [Type] -> b) -> [TypeVar] -> [Pred] -> m b
withDefaults f vs ps = do
  let vps = ambiguities vs ps
  tss <- mapM candidates vps
  case find (null . fst) (zip tss vps) of
    Just (_, bad) -> typecheckError $ "Cannot resolve ambiguity: candidates for " <> show bad <> " are empty"
    Nothing -> pure $ f vps (fmap head tss)


-- |Predicates that can be removed after ambiguities are solved
defaultedPreds :: (HasClassEnv m,
                   MonadIO m)
               => [TypeVar] -> [Pred] -> m [Pred]
defaultedPreds = withDefaults (\vps _ -> join (fmap snd vps))


-- |Substitution to remove ambiguities used in toplevel inference
defaultSubst :: (HasClassEnv m, MonadIO m)
             => [TypeVar] -> [Pred] -> m Substitution
defaultSubst  = withDefaults (\vps ts -> Subst $ M.fromList $ zip (fmap (tName . fst) vps) ts)


-- |Typecheck explicitly typed binding
inferTypeExpl :: ExplBinding -> TypecheckerT IO ([Pred], (Type, [TypedAlt]))
inferTypeExpl (_, (sc, alts)) = do
  (qs :=> t) <- freshInst sc
  (ps, (_, talts)) <- inferTypeAlts t alts
  s <- getSubst
  as <- getTypeEnv
  let qs' = substitute s qs
      t'= substitute s t
      fs = free $ substitute s as
      gs = free t' \\ fs
      sc' = quantify gs (qs' :=> t')
  ps' <- filterM (\x -> not <$> entail qs' x) (substitute s ps)
  (ds, rs) <- split fs gs ps'
  if | sc /= sc' -> typecheckError "Signature is too general"
     | not (null rs) -> typecheckError "Context is too weak"
     | otherwise -> pure (ds, (t, talts))


-- |Implicit binding set is restricted when any of its members has alt with no explicit arguments
restricted :: Foldable t => t ImplBinding -> Bool
restricted bs = any simple bs where
  simple (_, alts) = any (null . fst) alts


-- |Infer type of binding without type declaration
inferTypeImpl :: Infer ImplBindings (TypeEnv, TypedBindings)
inferTypeImpl bs = do
  ts <- mapM (const $ newVar "IMPL" KType) bs
  as <- getTypeEnv
  let is = M.keys bs
      scs = fmap toTypePoly ts
      altss = M.elems bs
      as' = (TypeEnv $ M.fromList $ zip is (M.elems scs)) <> as
  inferred <-
    sequence (zipWith (\x y -> withTypeEnv as' $ inferTypeAlts y x) altss (M.elems ts))
  s <- getSubst
  let pss = fmap fst inferred
      taltss :: [(Type, [TypedAlt])]
      taltss = fmap snd inferred

      ps' = substitute s (join pss)
      ts' = substitute s ts
      fs = free (substitute s as)
      vss = fmap free ts'
      gs = foldr1 union vss \\ fs
  (ds, rs) <- split fs (if null vss then [] else foldr1 intersect vss) ps'
  if restricted (M.toList bs)
    then let gs' = filter (`elem` free rs) gs
             scs' = M.elems $ fmap (quantify gs' . ([] :=>)) ts'
    in pure (ds ++ rs, ( TypeEnv $ M.fromList $ zip is scs'
                       , M.fromList $ zip is taltss
                       ))
    else let scs' = M.elems $ fmap (quantify gs . (rs :=>)) ts'
    in pure (ds, ( TypeEnv $ M.fromList $ zip is scs'
                 , M.fromList $ zip is taltss
                 ))


-- |Infer types of all members in binding group
inferTypeBindingGroup :: Infer BindingGroup (TypeEnv, TypedBindings)
inferTypeBindingGroup (es, iss) = do
  as <- getTypeEnv
  let as' = -- assumptions made out of explicit bindings
        TypeEnv $ foldr (\(v, (sc, _)) m -> M.insert v sc m) M.empty (M.toList es)
  (ps, (as'', tbindsImp)) <- withTypeEnv (as' <> as) $ inferTypeSeq inferTypeImpl iss
  fromExpls <- mapM (withTypeEnv (as'' <> as' <> as) . inferTypeExpl) (M.toList es)
  let qss = fmap fst fromExpls
      exInfer = fmap snd fromExpls
      tbindsExp = M.fromList $ zipWith (\(n, _) (t, talt) -> (n, (t, talt))) (M.toList es) exInfer
  pure (ps ++ join qss, (as'' <> as', M.union tbindsExp tbindsImp))


-- |Sequence type inference of bindings
inferTypeSeq :: Infer bg (TypeEnv, TypedBindings) -> Infer [bg] (TypeEnv, TypedBindings)
inferTypeSeq ti = \case
  [] -> pure ([], mempty)
  (bs:bss) -> do
    as <- getTypeEnv
    (ps, (as', tb)) <- withTypeEnv as $ ti bs
    (qs, (as'', tbs)) <- withTypeEnv (as' <> as) (inferTypeSeq ti bss)
    pure (ps ++ qs, (as'' <> as', M.union tb tbs))


-- |Infer types of multiple independent binding groups
inferTypeBindingGroups :: [BindingGroup] -> TypecheckerT IO (TypeEnv, TypedBindings)
inferTypeBindingGroups bgs = do
  (ps, (as', tb)) <- inferTypeSeq inferTypeBindingGroup bgs
  s <- getSubst
  rs <- reduce (substitute s ps)
  s' <- defaultSubst [] rs
  pure (substitute (s' <> s) as', tb)


-- |Evaluation of typechecker
runTypecheckerT :: ClassEnv
                -> TypeEnv
                -> TypecheckerConfig
                -> TypecheckerT IO (TypeEnv, TypedBindings)
                -> IO (Either ErrMsg (TypeEnv, TypedBindings))
runTypecheckerT ce te tc
  = flip evalStateT (TypecheckerState 0 mempty)
  . flip runReaderT (TypecheckerEnv ce te tc)
  . runExceptT . (\(Typechecker t) -> t)


-- |Toplevel typechecking of a program without intro
typecheckEmpty :: TypecheckerConfig -> Program -> IO (Either ErrMsg TypedProgram)
typecheckEmpty tc p =
  let (_, _, ts) = primitiveSpace
  in fmap (fmap $ \(te, tb) -> TypedProgram tb te (prgDataspace p) (prgNamespace p)) $ runTypecheckerT
     (prgClassEnv p)
     (TypeEnv $ M.union (types ts) (types $ prgTypeEnv p))
     tc (inferTypeBindingGroups $ prgBindings p)


-- |Toplevel typechecking of a program
typecheck :: TypecheckerConfig -> Program -> IO (Either ErrMsg TypedProgram)
typecheck tc pp =
  let p = withIntro pp
      (_, _, ts) = primitiveSpace
  in fmap (fmap $ \(te, tb) -> TypedProgram tb te (prgDataspace p) (prgNamespace p)) $ runTypecheckerT
     (prgClassEnv p)
     (TypeEnv $ M.union (types ts) (types $ prgTypeEnv p))
     tc (inferTypeBindingGroups $ prgBindings p)
