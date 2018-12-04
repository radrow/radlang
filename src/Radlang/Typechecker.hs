{-# LANGUAGE FlexibleContexts #-}
{-#LANGUAGE MultiWayIf #-}
{-#LANGUAGE ScopedTypeVariables #-}
{-#LANGUAGE OverloadedLists #-}
-- |Implementation of the W Algorithm for typechecking

module Radlang.Typechecker where

import Data.Bifunctor
import Data.List as DL
import qualified Data.Map.Strict as M
import qualified Data.Set.Monad as S
import Data.Set.Monad(Set)
import Control.Applicative
import Control.Monad.State.Strict
import Control.Monad.Reader
import Control.Monad.Except

import Radlang.Types
import Radlang.Typedefs


typeEnvUnion :: TypeEnv -> TypeEnv -> TypeEnv
typeEnvUnion (TypeEnv t1) (TypeEnv t2) = TypeEnv (M.union t1 t2)

setTypeEnv :: MonadState TypecheckerState m => TypeEnv -> m ()
setTypeEnv te = modify $ \s -> s{tcTypeEnv = te}

-- |Gets superclasses of class by name
super :: HasClassEnv m => Name -> m (Set Name)
super n = getClassEnv >>= \ce -> case M.lookup n (classes ce) of
  Just (Class is _) -> pure is
  Nothing -> throwError $ "superclass lookup: " <> n <> " not defined"


-- |Gets instances of class by name
instances :: HasClassEnv m => Name -> m (Set Inst)
instances n = getClassEnv >>= \ce -> case M.lookup n (classes ce) of
  Just (Class _ its) -> pure its
  Nothing -> throwError $ "instances lookup: " <> n <> " not defined"


-- |Inserts new class to env
updateClassEnv :: Name -> Class -> ClassEnvBuilder ()
updateClassEnv n c = modify $ \ce -> ce {classes = M.insert n c (classes ce)}


-- |Empty class environment
emptyClassEnv :: ClassEnv
emptyClassEnv = ClassEnv
  { classes = []
  , defaults = S.fromList [] -- TODO: defaults!
  }

-- |Creates substitution with type assigned
bindVar :: MonadError ErrMsg m => TypeVar -> Type -> m Substitution
bindVar tv t = if
    | t == TypeVarWobbly tv -> pure mempty
    | S.member tv (free t) ->
      throwError $ "Occur check: cannot create infinite type: " <> tName tv <> " := " <> show t
    | kind tv /= kind t -> throwError $ "Kinds don't match"
    | otherwise -> pure $ Subst $ M.singleton (tName tv) t



-- |Merge substitutions ensuring that they agree
merge :: MonadError ErrMsg m => Substitution -> Substitution -> m Substitution
merge s1 s2 =
  let extract (n, t) = TypeVar n (kind t)
      agree = all (liftA2 (==) (substitute s1 . TypeVarWobbly) (substitute s2 .TypeVarWobbly))
        (fmap extract $ M.toList (getSubstMap s1) `intersect` M.toList (getSubstMap s2))
  in if agree then pure (s1 <> s2) else throwError "Cannot merge substitutions"



-- |Most general unifier
mgu :: MonadError ErrMsg m => Type -> Type -> m Substitution
mgu t1 t2 = case (t1, t2) of
  (TypeVarWobbly tv, _) -> bindVar tv t2
  (_, TypeVarWobbly tv) -> bindVar tv t1
  (TypeApp f1 a1, TypeApp f2 a2) -> do
    sf <- mgu f1 f2
    sa <- mgu a1 a2
    pure $ sa <> sf
  (TypeVarRigid a, TypeVarRigid b) ->
    if a == b
    then pure mempty
    else throwError $ "Cannot unify rigid different type variables: " <> tName a <> " vs " <> tName b
  (TypeVarRigid (TypeVar a _), b) ->
    throwError $ "Cannot unify rigid type variable with non-rigid type: " <> a <> " vs " <> show b
  (b, TypeVarRigid (TypeVar a _)) ->
    throwError $ "Cannot unify rigid type variable with non-rigid type: " <> show b <> " vs " <> a
  _ -> throwError $ "Cannot unify types: " <> show t1 <> " vs " <> show t2



-- |Unifier that uses `merge` instead of `<>`
match :: MonadError ErrMsg m => Type -> Type -> m Substitution
match t1 t2 = case (t1, t2) of
  (TypeApp f1 a1, TypeApp f2 a2) -> do
    sf <- match f1 f2
    sa <- match a1 a2
    merge sa sf
  (TypeVarWobbly tv, t) | kind tv == kind t -> bindVar tv t2
  (TypeVarRigid a, TypeVarRigid b) ->
    if a == b
    then pure mempty
    else throwError $ "Cannot merge rigid different type variables: " <> tName a <> " vs " <> tName b
  (TypeVarRigid (TypeVar a _), b) ->
    throwError $ "Cannot merge rigid type variable with non-rigid type: " <> a <> " vs " <> show b
  (b, TypeVarRigid (TypeVar a _)) ->
    throwError $ "Cannot merge rigid type variable with non-rigid type: " <> show b <> " vs " <> a
  _ -> throwError $ "Cannot merge types: " <> show t1 <> " vs " <> show t2


-- |mgu for predicates
mguPred :: MonadError ErrMsg m => Pred -> Pred -> m Substitution
mguPred (IsIn i1 t1) (IsIn i2 t2) =
  if i1 == i2 then mgu t1 t2
  else throwError $ "Classes don't unify: " <> i1 <> " vs " <> i2


-- |match for predicates
matchPred :: MonadError ErrMsg m => Pred -> Pred -> m Substitution
matchPred (IsIn i1 t1) (IsIn i2 t2) =
  if i1 == i2 then match t1 t2
  else throwError $ "Classes don't match: " <> i1 <> " vs " <> i2


-- |Check whether class is defined
classDefined :: HasClassEnv m => Name -> m Bool
classDefined n = M.member n . classes <$> getClassEnv


-- |Introduces new class extending given superclasses
addClass :: Name -> Set Name -> ClassEnvBuilder ()
addClass n sups = do
  nDefined <- classDefined n
  when nDefined (throwError $ "Class already defined: " <> n)
  notDefs <- mapM (\ss -> not <$> classDefined ss) (S.toList sups)
  when (not (null notDefs)) $
    throwError $ "Superclasses not defined: " <> show notDefs
  updateClassEnv n (Class sups S.empty)


-- |Declares new instance with qualification
addInst :: [Pred] -> Pred -> ClassEnvBuilder ()
addInst ps p@(IsIn i _) = do
  iDefined <- classDefined i
  when (not iDefined) (throwError $ "Class not defined: " <> i)
  its <- instances i
  c <- super i
  let overlaps prd q = catchError (mguPred prd q >> pure True) (const $ pure False)
      qs = fmap (\(_ :=> q) -> q) its
  filterM (overlaps p) (S.toList qs) >>= \case
    [] -> pure ()
    (IsIn h _):_ -> throwError $ "Instances overlap: " <> i <> " with " <> h
  updateClassEnv i (Class c $ S.insert (ps :=> p) its)


-- |Deep search for all superclasses' predicates
predsBySuper :: HasClassEnv m => Pred -> m [Pred]
predsBySuper p@(IsIn i t) = do
  i' <- S.toList <$> super i
  if Prelude.null i'
    then pure [p]
    else insert p <$> (join <$> (forM i' (\i'' -> predsBySuper (IsIn i'' t))))


-- |Deep search for all matching instances' predicates
predsByInstances :: HasClassEnv m => Pred -> m [Pred]
predsByInstances p@(IsIn i _) = do
  -- list of instances of i
  insts <- S.toList <$> instances i
  -- opertation that tries to strictly unify p with instance declaration
  let -- tryInst :: Qual Pred -> Typechecker [Pred]
      tryInst (ps :=> h) = do
        u <- matchPred h p
        pure $ fmap (substitute u) ps
  msum $ fmap tryInst insts


-- |Check if `p` will hold whenever all of `ps` are satisfied
entail :: HasClassEnv m => [Pred] -> Pred -> m Bool
entail ps p = do
  -- all sets of superclasses of `ps`
  sups <- mapM predsBySuper ps
  -- all matching instances have this property
  let instCheck = do
        qs <- predsByInstances p
        ents <- mapM (entail ps) qs
        pure $ all id ents
  instc <- catchError instCheck (const $ pure False) -- FIXME this `catch` may cause problems
  pure $ any (elem p) sups || instc


-- |Check if predicate is in head normal form. -- TODO: what does it mean?
inHNF :: Pred -> Bool
inHNF (IsIn _ t) = case t of
  (TypeVarWobbly _) -> True
  (TypeVarRigid _) -> False
  (TypeApp tt _) -> inHNF (IsIn undefined tt)
  _ -> error "unimplemented ihnf" -- FIXME


-- |Turn predicate into head normal form
toHNF :: HasClassEnv m => Pred -> m [Pred]
toHNF p =
  if inHNF p
    then pure [p]
    else predsByInstances p >>= toHNFs

-- |Turn a set of predicates into hnf
toHNFs :: HasClassEnv m => [Pred] -> m [Pred]
toHNFs ps = do
  pss <- mapM toHNF ps
  pure $ join pss


-- |Remove predicates that are entailed by others
simplify :: HasClassEnv m => [Pred] -> m [Pred]
simplify pps = loop [] pps where
  loop rs [] = pure rs
  loop rs (p:ps) = do
    e <- entail (rs ++ ps) p
    if e then loop rs ps else loop (p:rs) ps


-- |Turns predicates into head normal form and then simplifies
reduce :: HasClassEnv m => [Pred] -> m [Pred]
reduce ps = toHNFs ps >>= simplify


-- |Create scheme of generic type by its arguments
quantify :: [TypeVar] -> Qual Type -> TypePoly
quantify vs qt = Forall ks (substitute s qt) where
  vs' = [v | v <- S.toList $ free qt, v `elem` vs]
  ks = fmap kind vs'
  ns = fmap tName vs'
  s = Subst $ M.fromList $ zip ns (fmap TypeGeneric [0..])


-- |Turn plain type into scheme
toTypePoly :: Type -> TypePoly
toTypePoly t = Forall [] ([] :=> t)


-- |Find typescheme in type env
lookupType :: HasTypeEnv m => Name -> m TypePoly
lookupType n = getTypeEnv >>= \(TypeEnv te) -> case M.lookup n te of
  Nothing -> throwError $ "Unbound id: " <> n
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
newVar :: IdSupply m => String -> Kind -> m Type
newVar prefix k = do
  c <- newId
  pure $ TypeVarWobbly $ TypeVar (prefix <> show c) k


-- |Create new type varaibles for each parameter of scheme
freshInst :: IdSupply m => TypePoly -> m (Qual Type)
freshInst (Forall ks qt) = do
  ts <- mapM (newVar "_Inst") ks
  pure $ instantiate ts qt

type Infer e t = e -> TypeInfer ([Pred], t)

inferTypeExpr :: Infer Expr Type
inferTypeExpr = \case
  Val v -> do
    sc <- lookupType v
    (ps :=> t) <- freshInst sc
    pure (ps, t)
  ConstLit _ -> newVar "_Int" KType >>= \v -> pure ([IsIn "Num" v], v)
  Constructor (_, sc) -> do
    (ps :=> t) <- freshInst sc
    pure (ps, t)
  Application f a -> do
    (ps, tf) <- inferTypeExpr f
    (qs, ta) <- inferTypeExpr a
    t <- newVar "_Arg" KType
    unify (fun ta t) tf
    pure (ps ++ qs, t)

inferTypeLiteral :: Infer Literal Type
inferTypeLiteral = \case
  LitInt _ -> newVar "_LI" KType >>= \v -> pure ([IsIn "Num" v], v)

inferTypePattern :: Infer Pattern (TypeEnv, Type)
inferTypePattern = \case
  PVar i -> newVar "_PV" KType >>= \v ->
    pure ([], (TypeEnv $ M.singleton i (toTypePoly v), v))
  PWildcard -> newVar "_PW" KType >>= \v -> pure ([], (TypeEnv M.empty, v))
  PAs i pat -> do
    (ps, ((TypeEnv ts), t)) <- inferTypePattern pat
    pure (ps, (TypeEnv $ M.insert i (toTypePoly t) ts, t))
  PLit l -> inferTypeLiteral l >>= \(ps, t) -> pure (ps, (TypeEnv M.empty, t))
  PNPlusK n _ -> newVar "_PNPK" KType >>= \t ->
    pure ([IsIn "Integral" t], (TypeEnv $ M.singleton n (toTypePoly t), t))
  PConstructor (_, sc) pats -> do
    (ps, (tspace, ts)) <- inferTypePatterns pats
    t' <- newVar "_PC" KType
    (qs :=> t) <- freshInst sc
    unify t (S.foldr fun t' ts)
    pure (ps ++ qs, (tspace, t'))

inferTypePatterns :: Infer (Set Pattern) (TypeEnv, Set Type)
inferTypePatterns pats = do
  psats <- mapM inferTypePattern (S.toList pats)
  let typeEnvJoin = foldr typeEnvUnion (TypeEnv M.empty)
      ps = join $ fmap (\(x,(_,_)) -> x) psats
      as = typeEnvJoin $ fmap (\(_,(x,_)) -> x) psats
      ts = fmap (\(_,(_,x)) -> x) psats
  pure (ps, (as, S.fromList ts))


-- |Left and right side of function definition
type Alt = (Set Pattern, Expr)


inferTypeAlt :: Infer Alt Type
inferTypeAlt (pats, e) = do
  (ps, (as', ts)) <- inferTypePatterns pats
  (qs, t) <- local (first $ typeEnvUnion as') (inferTypeExpr e)
  pure (ps ++ qs, S.foldr fun t ts)


inferTypeAlts :: [Alt] -> Type -> TypeInfer [Pred]
inferTypeAlts alts t = do
  psts <- mapM inferTypeAlt alts
  void $ mapM (unify t) (fmap snd psts)
  pure (join $ fmap fst psts)


-- |Split predicates on deferred and contraints. fs are fixed variables and gs are varaibles over which we want to quantify
split :: HasClassEnv m => [TypeVar] -> [TypeVar] -> [Pred] -> m ([Pred], [Pred])
split fs gs ps = do
  ps' <- reduce ps
  let (ds, rs) = partition (all (`elem` fs) . free) ps'
  rs' <- defaultedPreds (fs ++ gs) rs
  pure (ds, rs \\ rs')


type Ambiguity = (TypeVar, [Pred])

ambiguities :: [TypeVar] -> [Pred] -> [Ambiguity]
ambiguities vs ps = fmap (\v -> (v, filter (elem v . free) ps)) $ S.toList (free ps) \\ vs


candidates :: HasClassEnv m => Ambiguity -> m [Type]
candidates (v, qs) = getClassEnv >>= \ce ->
  let is = fmap (\(IsIn i _) -> i) qs
      ts = fmap (\(IsIn _ t) -> t) qs
      -- filt :: [Type] -> m [Type]
      filt tts = flip filterM tts $ \t ->
        all id <$> mapM (entail []) [IsIn i t | i <- is]
  in if all ((TypeVarWobbly v)==) ts
     && any (`S.member` numClasses) is
     && all (`S.member` stdClasses) is
     then filt (S.toList $ defaults ce)
     else pure []


withDefaults :: HasClassEnv m
             => ([Ambiguity] -> [Type] -> a)
             -> [TypeVar] -> [Pred]
             -> m a
withDefaults f vs ps = do
  let vps = ambiguities vs ps
  tss <- mapM candidates vps
  if any null tss
    then throwError "Cannot resolve ambiguity"
    else pure $ f vps (fmap head tss)

defaultedPreds :: HasClassEnv m => [TypeVar] -> [Pred] -> m [Pred]
defaultedPreds = withDefaults (\vps _ -> join (fmap snd vps))


defaultSubst :: HasClassEnv m => [TypeVar] -> [Pred] -> m Substitution
defaultSubst  = withDefaults (\vps ts -> Subst $ M.fromList $ zip (fmap (tName . fst) vps) ts)

execTypeInfer :: TypeInfer a -> Typechecker a
execTypeInfer (TypeInfer ti) = do
  ce <- getClassEnv
  tstate <- get
  let istate = TypeInferState
        { tiSubst = tcSubst tstate
        , tiSupply = tcSupply tstate
        }
      iread = (tcTypeEnv tstate, ce)
      (x, newst) = runState (runReaderT (runExceptT ti) iread) istate
  case x of
    Left e -> throwError e
    Right res -> do
      put $ TypecheckerState
        { tcSupply = tiSupply newst
        , tcSubst = tiSubst newst
        , tcTypeEnv = tcTypeEnv tstate
        }
      pure res

type ExplBind = (Name, TypePoly, [Alt])

inferTypeExpl :: ExplBind -> Typechecker [Pred]
inferTypeExpl (_, sc, alts) = do
  (qs :=> t) <- freshInst sc
  ps <- execTypeInfer $ inferTypeAlts alts t
  s <- getSubst
  as <- getTypeEnv
  let qs' = substitute s qs
      t'= substitute s t
      fs = S.toList $ free $ substitute s as
      gs = (S.toList $ free t') \\ fs
      sc' = quantify gs (qs' :=> t')
  ps' <- filterM (\x -> not <$> entail qs' x) (substitute s ps)
  (ds, rs) <- execTypeInfer $ split fs gs ps'
  if | sc /= sc' -> throwError "Signature is too general"
     | not (null rs) -> throwError "Context is too weak"
     | otherwise -> pure ds


type ImplBind = (Name, [Alt])


restricted :: Foldable t => t ImplBind -> Bool
restricted bs = any simple bs where
  simple (_, alts) = any (null . fst) alts


inferTypeImpl :: [ImplBind] -> Typechecker [Pred]
inferTypeImpl bs = do
  ts <- mapM (const $ newVar "IMPL" KType) bs
  as <- getTypeEnv
  let is = fmap fst bs
      scs = fmap toTypePoly ts
      altss = fmap snd bs
  setTypeEnv $ typeEnvUnion (TypeEnv $ M.fromList $ zip is scs) as
  pss <- sequence (zipWith (\x y -> execTypeInfer $ inferTypeAlts x y) altss ts)
  s <- getSubst
  let ps' = substitute s (join pss)
      ts' = substitute s ts
      fs = S.toList $ free (substitute s as)
      vss = fmap (S.toList . free) ts'
      gs = foldr1 union vss \\ fs
  (ds, rs) <- split fs (foldr1 intersect vss) ps'
  if restricted bs
    then
    let gs' = filter (`S.member` free rs) gs
        scs' = fmap (quantify gs' . ([] :=>)) ts'
    in do
      setTypeEnv $ (TypeEnv $ M.fromList $ zip is scs')
      pure (ds ++ rs)
    else
    let scs' = fmap (quantify gs . (rs :=>)) ts'
    in setTypeEnv (TypeEnv $ M.fromList $ zip is scs') >> pure ds


type Bindings = ([ExplBind], [[ImplBind]])


inferTypeBindings :: Bindings -> Typechecker [Pred]
inferTypeBindings (es, iss) = do
  as <- getTypeEnv
  let as' = TypeEnv $ foldr (\(v, sc, _) m -> M.insert v sc m) M.empty es
  setTypeEnv $ typeEnvUnion as' as
  ps <- inferTypeSeq inferTypeImpl iss
  qss <- mapM inferTypeExpl es
  pure (ps ++ join qss) -- TODO originally I forgot here `as


inferTypeSeq :: (bg -> Typechecker [Pred]) -> [bg] -> Typechecker [Pred]
inferTypeSeq ti = \case
  [] -> pure []
  (bs:bss) -> do
    ps <- ti bs
    qs <- inferTypeSeq ti bss
    pure (ps ++ qs)

type Program = [Bindings]

inferTypeProgram :: Program -> Typechecker ()
inferTypeProgram bgs = do
  ps <- inferTypeSeq inferTypeBindings bgs
  s <- getSubst
  rs <- reduce (substitute s ps)
  s' <- defaultSubst [] rs
  modify $ \st -> st {tcTypeEnv = substitute (s' <> s) (tcTypeEnv st)}


-- |Evaluation of typechecker
runTypechecker :: Typechecker () -> Either ErrMsg TypeEnv
runTypechecker =
  fmap tcTypeEnv
  . flip evalState (TypecheckerState 0 mempty (TypeEnv M.empty))
  . flip runReaderT emptyClassEnv
  . runExceptT . (\(Typechecker t) -> t >> get)

-- |Toplevel typechecking of expression
typecheck :: Program -> Either ErrMsg TypeEnv
typecheck p = runTypechecker (inferTypeProgram p)

pat :: Pattern
pat = PVar "wisienka"
expr :: Expr
expr = ConstLit $ LitInt 3

impl :: ImplBind
impl = ("wisienka", [(S.singleton pat, expr)])

pr :: Program
pr = [([],[[impl]])]
