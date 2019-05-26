-- |Type checker and type inferer. Decorates UntypedExpr with type annotations and resovles ambiguitites.
{-# LANGUAGE MultiWayIf          #-}
{-# LANGUAGE OverloadedLists     #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Radlang.Typechecker where

import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Applicative
import           Control.Monad.State.Strict
import           Data.Foldable
import           Data.Functor
import qualified Data.Text as T
import           Data.Bifunctor
import           Data.List                     as DL
import qualified Data.Map.Strict               as M

import           Radlang.Error
import           Radlang.Intro
import           Radlang.Typedefs
import           Radlang.Types
import           Radlang.Typesystem.Typesystem


-- |Run Typechecker in different type env
withTypeEnv :: Monad m => TypeEnv -> TypecheckerT m a -> TypecheckerT m a
withTypeEnv te = local $ \s -> s{typeEnv = te}


-- |Find typescheme in type env
lookupTypeSafe :: HasTypeEnv m => Name -> m (Maybe TypePoly)
lookupTypeSafe n = M.lookup n . types <$> getTypeEnv


-- |Find typescheme in type env and throw error if not present
lookupType :: HasTypeEnv m => Name -> m TypePoly
lookupType n = getTypeEnv >>= \(TypeEnv te) -> case M.lookup n te of
  Nothing -> languageError $ "Unbound id: " <> n <> "\nValid ids are: " <> T.pack (show (M.keys te))
  Just tp -> pure tp


-- |Extend current substitution with new one
extendSubst :: Substitutor m => Substitution -> m ()
extendSubst s = getSubst >>= \ts -> setSubst $ s <> ts


-- |Unify types and update substitution
unify :: Substitutor m => Type -> Type -> m ()
unify t1 t2 = do
  s <- getSubst
  u <- mgu (substitute s t1) (substitute s t2)
  extendSubst u


-- |Returns new type variable
newVar :: IdSupply m => Name -> Kind -> m Type
newVar prefix k = do
  c <- newId
  pure $ TypeVarWobbly $ TypeVar ("#" <> prefix <> "_" <> T.pack (show c)) k


-- |Create new type varaibles for each parameter of scheme
freshInst :: IdSupply m => TypePoly -> m (Qual Type)
freshInst (Forall ks qt) = do
  ts <- mapM (newVar "inst") ks
  pure $ instantiate ts qt


-- |Given argument infer qualified result
type Infer e t = e -> Typechecker (Qual t)


-- |Get type of UntypedExpr
inferTypeExpr :: Infer UntypedExpr Type
inferTypeExpr = \case
  UntypedVal v -> do
    sc <- lookupType v
    (ps :=> t) <- freshInst sc
    pure (ps :=> t)
  UntypedLit l -> inferTypeLiteral l <&> (\(p :=> t) -> (p :=> t))
  UntypedLet binds e -> do
    as <- getTypeEnv
    (ps :=> (as', _, _)) <- inferTypeBindingGroup binds
    (qs :=> t) <- withTypeEnv (as' <> as) $ inferTypeExpr e
    pure (ps ++ qs :=> t)
  UntypedApplication f a -> do
    (ps :=> tf) <- inferTypeExpr f
    (qs :=> ta) <- inferTypeExpr a
    t <- newVar "funres" KType
    unify (fun ta t) tf
    pure (ps ++ qs :=> t)


-- |Decorate 'UntypedExpr' tree with types to match given type
setExprType :: Qual Type -> UntypedExpr -> Typechecker TypedExpr
setExprType t@(pt :=> tt) = \case
  UntypedVal v -> do
    pure $ TypedVal t v
  UntypedLit l -> pure $ TypedLit t l
  UntypedLet binds e -> do
    as <- getTypeEnv
    (_ :=> (as', tb, _)) <- inferTypeBindingGroup binds
    typedE <- withTypeEnv (as' <> as) $ setExprType t e
    pure $ TypedLet t tb typedE
  UntypedApplication f a -> do
    (_ :=> tf) <- inferTypeExpr f
    (_ :=> ta) <- inferTypeExpr a
    s <- mgu (fun ta tt) tf
    unify (fun ta tt) tf
    typedf <- setExprType (pt :=> substitute s tf) f
    typeda <- setExprType (pt :=> substitute s ta) a
    pure $ TypedApplication (substitute s t) typedf typeda

reduceExprPreds :: TypedExpr -> Typechecker TypedExpr
reduceExprPreds = \case
  TypedVal (p :=> t) v -> reduce p >>= \rp -> pure $ TypedVal (rp :=> t) v
  TypedLit (p :=> t) v -> reduce p >>= \rp -> pure $ TypedLit (rp :=> t) v
  TypedApplication (p :=> t) f a ->
    reduce p >>= \rp -> liftA2 (TypedApplication (rp :=> t)) (reduceExprPreds f) (reduceExprPreds a)
  TypedLet (p :=> t) bnds e -> do
    rp <- reduce p
    re <- reduceExprPreds e
    rbnds <- flip mapM bnds $ \(bp :=> bt, balts) -> do
      rbp <- reduce bp
      rbalts <- reduceAltsPreds balts
      pure (rbp :=> bt, rbalts)
    pure $ TypedLet (rp :=> t) rbnds re

reduceAltsPreds :: [TypedAlt] -> Typechecker [TypedAlt]
reduceAltsPreds = mapM (\(pats, be) -> reduceExprPreds be >>= \rbe -> pure (pats, rbe))

-- |Infer type of literal value
inferTypeLiteral :: Infer Literal Type
inferTypeLiteral = \case
  -- UntypedLitInt _ -> newVar "_LI" KType >>= \v -> pure ([IsIn "Num" v], v)
  LitInt _ -> pure ([] :=> tInt)
  LitString _ -> pure ([] :=> tString)
  LitChar _ -> pure ([] :=> tChar)


-- |Infer pattern and get it's type and updated type env
inferTypePattern :: Infer Pattern (TypeEnv, Type)
inferTypePattern = \case
  PVar i -> newVar "var" KType >>= \v ->
    pure ([] :=> (TypeEnv $ M.singleton i (toTypePoly v), v))
  PWildcard -> newVar "w" KType >>= \v -> pure ([] :=> (TypeEnv M.empty, v))
  PAs i patt -> do
    (ps :=> ((TypeEnv ts), t)) <- inferTypePattern patt
    pure (ps :=> (TypeEnv $ M.insert i (toTypePoly t) ts, t))
  PLit l -> inferTypeLiteral l >>= \(ps :=> t) -> pure (ps :=> (TypeEnv M.empty, t))
  PConstructor cname pats -> do
    sc <- lookupType cname
    (ps :=> (tspace, ts)) <- inferTypePatterns pats
    t' <- newVar "constr" KType
    (qs :=> t) <- freshInst sc
    unify t (foldr fun t' ts)
    pure (ps ++ qs :=> (tspace, t'))


-- |Infer types of multiple patterns
inferTypePatterns :: Infer [Pattern] (TypeEnv, [Type])
inferTypePatterns pats = do
  psats <- mapM inferTypePattern pats
  let typeEnvJoin = foldr mappend (TypeEnv M.empty)
      ps = join $ fmap (\(x :=> (_,_)) -> x) psats
      as = typeEnvJoin $ fmap (\(_ :=> (x,_)) -> x) psats
      ts = fmap (\(_ :=> (_,x)) -> x) psats
  pure (ps :=> (as, ts))


-- |Infer type of whole alt
inferTypeAlt :: Infer Alt (TypeEnv, Type)
inferTypeAlt (pats, e) = do
  as <- getTypeEnv
  (ps :=> (as', ts)) <- inferTypePatterns pats
  (qs :=> t) <- withTypeEnv (as' <> as) (inferTypeExpr e)
  pure (ps ++ qs :=> (as', foldr fun t ts))


-- |Decorate alt with type annotations
setAltType :: Qual Type -> Alt -> Typechecker TypedAlt
setAltType t (pts, expr) = do
  as <- getTypeEnv
  let dropFun (TypeApp _ resType) = resType
      dropFun _                   = wtf "Bad alt function type"
      dropFuns [] tp       = tp
      dropFuns (_:rest) tp = dropFuns rest (dropFun tp)
      typeForExpr = getPreds t :=> dropFuns pts (getQualified t)
  s <- getSubst --fmap fold $ sequence $ zipWith mgu (argtypes t) tps
  let as'' = substitute s as -- as'
  typed <- withTypeEnv (as'' <> as) $ setExprType typeForExpr expr
  ss <- getSubst
  pure (pts, substitute ss typed)


-- |Infer type of list of alts, unify them and decorate with type annotations
inferTypeAlts :: Qual Type -> Infer [Alt] (Type, [TypedAlt])
inferTypeAlts t alts = do
  when (length (nub $ fmap (length . fst) alts) > 1) $
    languageError "Different number of patterns"
  psts <- mapM inferTypeAlt alts
  void $ mapM (unify (getQualified t)) (fmap (snd . getQualified) psts)
  as <- getTypeEnv
  let as' = foldr (\a b -> TypeEnv $ M.union (types a) (types b)) as (fmap (fst . getQualified) psts)
  talts <- forM (zip (fmap getPreds psts) alts) $ \(p, al) ->
    getSubst >>= \s -> withTypeEnv as' $ setAltType (substitute s (p :=> getQualified t)) al
  s <- getSubst
  let finalPreds = join (fmap (substitute s . getPreds) psts)
      finalType = getQualified $ substitute s t
  reduced <- reduce finalPreds
  reducedAlts <- reduceAltsPreds $ fmap (second $ substitute s) talts
  pure (reduced :=> (finalType, reducedAlts))


-- |Split predicates on deferred and contraints. fs are fixed variables and gs are varaibles over which we want to quantify
split :: HasInterfaceEnv m
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
candidates :: HasInterfaceEnv m => Ambiguity -> m [Type]
candidates (v, qs) = getInterfaceEnv >>= \ce ->
  let is = fmap (\(IsIn i _) -> i) qs
      ts = fmap (\(IsIn _ t) -> t) qs
      -- filt :: [Type] -> m [Type]
      filt tts = flip filterM tts $ \t ->
        and <$> mapM (entail []) [IsIn i t | i <- is]
  in if all ((TypeVarWobbly v)==) ts
        && all (`M.member` stdInterfaces) is
        && any (`M.member` stdNumInterfaces) is
     then filt [def | ii <- is, def <- maybe [] id $ M.lookup ii (defaults ce)]
     else pure []


-- |Predicates that can be removed after ambiguities are solved
defaultedPreds :: HasInterfaceEnv m
               => [TypeVar] -> [Pred] -> m [Pred]
defaultedPreds vs ps = do
  let vps = ambiguities vs ps
  tss <- mapM candidates vps
  case find (null . fst) (zip tss vps) of
    Just (_, bad) -> typecheckError $ "Cannot resolve ambiguity: candidates for " <> T.pack (show bad) <> " are empty"
    Nothing -> pure $ join (fmap snd vps)


-- |Substitution that solves ambiguities using defaults
defaultSubst :: HasInterfaceEnv m => [TypeVar] -> [Pred] -> m Substitution
defaultSubst vs ps = do
  let vps = ambiguities vs ps
  tss <- mapM candidates vps
  case find (null . fst) (zip tss vps) of
    Just (_, bad) -> typecheckError $ "Cannot resolve ambiguity: candidates for " <> T.pack (show bad) <> " are empty"
    Nothing -> pure $
      Subst $ M.fromList $ zip (map ((\(TypeVar n _) -> n) . fst) vps) (map head tss)


-- |Typecheck explicitly typed binding
inferTypeExpl :: Infer ExplBinding (Qual Type, [TypedAlt])
inferTypeExpl (name, (typeDeclared, alts)) = do
  qt@(tpreds :=> t) <- freshInst typeDeclared
  (inferredPreds :=> (_, talts)) <- inferTypeAlts qt alts
  s <- getSubst
  as <- getTypeEnv
  let predsUnified = substitute s tpreds
      typeUnified = substitute s t
      freeOutside = free $ substitute s as
      freeInside = free typeUnified \\ freeOutside
      typeQuantified = quantify freeInside (predsUnified :=> typeUnified)
  ps' <- filterM (\x -> not <$> entail predsUnified x) (substitute s inferredPreds)
  (ds, rs) <- split freeOutside freeInside ps'
  predsUnifiedReduced <- reduce predsUnified
  if | typeDeclared /= typeQuantified ->
         typecheckError $ "Signature is too general for " <> name
     | not (null rs) -> typecheckError $ "Context is too weak for " <> name
     | otherwise -> pure ( ds :=> (predsUnifiedReduced :=> typeUnified, talts))


-- |Implicit binding set is restricted when any of its members has alt with no explicit arguments
restricted :: Foldable t => t ImplBinding -> Bool
restricted bs = any simple bs where
  simple (_, alts) = any (null . fst) alts


-- |Infer type of binding without type declaration
inferTypeImpl :: Infer ImplBindings (TypeEnv, TypedBindings, PolyBindings)
inferTypeImpl bs = do
  ts <- mapM (\(n, _) -> newVar ("infer" <> n) KType) $ M.toList bs
  as <- getTypeEnv
  let is = M.keys bs
      scs = fmap toTypePoly ts
      altss = M.elems bs
      as' = (TypeEnv $ M.fromList $ zip is scs) <> as
  inferred <-
    sequence (zipWith (\x y -> withTypeEnv as' $ inferTypeAlts y x) altss (fmap ([] :=>) ts))
  s <- getSubst
  let pss = fmap getPreds inferred
      taltss :: [(Qual Type, [TypedAlt])]
      taltss = fmap (\(p :=> (t, a)) -> (p :=> t, a)) inferred

      ps' = substitute s (join pss)
      ts' = substitute s ts
      fs = free (substitute s as)
      vss = fmap free ts'
      gs = foldr1 union vss \\ fs
  (ds, rs) <- split fs (if null vss then [] else foldr1 intersect vss) ps'
  if restricted (M.toList bs)
    then let gs' = filter (`elem` free rs) gs
             scs' = fmap (quantify gs' . ([] :=>)) ts'
    in pure (ds ++ rs :=> ( TypeEnv $ M.fromList $ zip is scs'
                          , M.fromList $ zip is taltss
                          , M.empty
                          ))
    else let scs' = fmap (quantify gs . (rs :=>)) ts'
    in pure (ds :=> ( TypeEnv $ M.fromList $ zip is scs'
                    , M.fromList $ zip is taltss
                    , M.empty
                    ))


-- |Infer types of all members in binding group
inferTypeBindingGroup :: Infer BindingGroup (TypeEnv, TypedBindings, PolyBindings)
inferTypeBindingGroup (ints, es, iss) = do
  as <- getTypeEnv
  let as' = -- assumptions made out of explicit bindings and interface declarations
        TypeEnv $ foldr (\(v, sc) m -> M.insert v sc m)
        M.empty (fmap (\(n, (t, _)) -> (n, t)) (M.toList es) ++ fmap (\(n, (_, _, t, _)) -> (n, t)) (M.toList ints))
  (ps :=> (as'', tbindsImp, _)) <- withTypeEnv (as' <> as) $ inferTypeSeq inferTypeImpl iss
  let map4f f (a, b, c, d) = (a, b, c, f d)
  (fromExpls :: [Qual (Qual Type, [TypedAlt])]) <- mapM (withTypeEnv (as'' <> as' <> as) . inferTypeExpl) (M.toList es)
  (tbindsPoly :: PolyBindings) <- fmap (fmap (map4f (fmap getQualified)) . M.fromList) $ sequence
    $ M.toList ints <&> \(n, (cn, idata, tp, dds)) -> do
    tpinst <- freshInst tp
    implems <- forM dds $ \(t, alts) -> do
      (prds :=> res) <- (withTypeEnv (as'' <> as' <> as) . inferTypeExpl) (n, (t, alts))
      predsred <- reduce prds
      pure (predsred :=> res)
    pure (n, (cn, idata, tpinst, implems))

  let qss = fmap getPreds fromExpls
      tbindsExp :: TypedBindings
      tbindsExp = M.fromList $ zipWith (\(n, _) (_ :=> ttt) -> (n, ttt)) (M.toList es) fromExpls

  pure (ps ++ join qss
       :=> (as'' <> as'
           , M.union tbindsExp tbindsImp
           , tbindsPoly
           ))


-- |Sequence type inference of bindings
inferTypeSeq :: Infer bg (TypeEnv, TypedBindings, PolyBindings) -> Infer [bg] (TypeEnv, TypedBindings, PolyBindings)
inferTypeSeq ti = \case
  [] -> pure ([] :=> mempty)
  (bs:bss) -> do
    as <- getTypeEnv
    (ps :=> (as', tb, pb)) <- withTypeEnv as $ ti bs
    (qs :=> (as'', tbs, pbs)) <- withTypeEnv (as' <> as) (inferTypeSeq ti bss)
    pure (ps ++ qs :=> (as'' <> as', M.union tb tbs, M.union pb pbs))


-- |Infer types of multiple independent binding groups
inferTypeBindingGroups :: [BindingGroup] -> Typechecker (TypedBindings, PolyBindings)
inferTypeBindingGroups bgs = do
  (ps :=> (_, tb, pb)) <- inferTypeSeq inferTypeBindingGroup bgs
  s <- getSubst
  rs <- reduce (substitute s ps)
  s' <- defaultSubst [] rs
  let dsub :: IsType t => t -> t
      dsub = substitute (s' <> s)
      stb = fmap (\(a, b) -> (dsub a, fmap (fmap dsub) b)) tb
      spb = fmap (\(a, (b1, b2), c, d) ->
                     (a, (b1, b2), dsub c, fmap (\(qt, im) -> (dsub qt, fmap (fmap dsub) im)) d)) pb
  pure (stb, spb)


-- |Evaluation of typechecker
runTypechecker :: InterfaceEnv
               -> TypeEnv
               -> TypecheckerConfig
               -> Typechecker a
               -> Either ErrMsg a
runTypechecker ie te tc
  = flip evalState (TypecheckerState 0 mempty)
  . flip runReaderT (TypecheckerEnv ie te tc)
  . runExceptT
  . (\(Typechecker t) -> t)


-- |Toplevel typechecking of a program
typecheck :: TypecheckerConfig -> UntypedProgram -> Either ErrMsg TypedProgram
typecheck tc p =
  let (ps, ts) = primitiveSpace
  in do (tb, pb) <- runTypechecker
                    (uprgInterfaceEnv p)
                    (TypeEnv $ M.union (types ts) (types $ uprgTypeEnv p))
                    tc (inferTypeBindingGroups $ uprgBindings p)

        let psl = ps `M.union` (uprgDataMap p)
        pure $ TypedProgram
          { tprgDataMap = psl
          , tprgPolyBindings = pb
          , tprgBindings = tb
          , tprgInterfaceEnv = uprgInterfaceEnv p
          }
