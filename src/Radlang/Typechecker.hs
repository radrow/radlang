{-#LANGUAGE MultiWayIf #-}
{-#LANGUAGE ScopedTypeVariables #-}
{-#LANGUAGE OverloadedLists #-}
-- |Implementation of the W Algorithm for typechecking

module Radlang.Typechecker where

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


getTypeEnv :: Typechecker TypeEnv
getTypeEnv = asks fst


getClassEnv :: Typechecker ClassEnv
getClassEnv = asks snd


-- |Gets superclasses of class by name
super :: HasClassEnv m => Name -> m (Set Name)
super n = case M.lookup n (classes ce) of
  Just (is, _) -> pure is
  Nothing -> throwError $ "superclass lookup: " <> n <> " not defined"


-- |Gets instances of class by name
instances :: HasClassEnv m => Name -> m (Set Inst)
instances ce n = case M.lookup n (classes ce) of
  Just (_, its) -> pure its
  Nothing -> throwError $ "instances lookup: " <> n <> " not defined"


-- |Inserts new class to env
updateClassEnv :: ClassEnv -> Name -> Class -> ClassEnvBuilder ()
updateClassEnv n c = modify $ \ce -> ce {classes = M.insert n c (classes ce)}


-- |Empty class environment
emptyClassEnv :: ClassEnv
emptyClassEnv = ClassEnv
  { classes = []
  , defaults = S.fromList [TypeInt]
  }


-- |Creates substitution with type assigned
bindVar :: TypeVar -> Type -> Typechecker Substitution
bindVar tv t = if
    | t == TypeVarWobbly tv -> pure mempty
    | S.member tv (free t) ->
      throwError $ "Occur check: cannot create infinite type: " <> tName tv <> " := " <> show t
    | kind tv /= kind t -> throwError $ "Kinds don't match"
    | otherwise -> pure $ Subst $ M.singleton (tName tv) t



-- |Merge substitutions ensuring that they agree
merge :: Substitution -> Substitution -> Typechecker Substitution
merge s1 s2 =
  let extract (n, t) = TypeVar n (kind t)
      agree = all (liftA2 (==) (substitute s1 . TypeVarWobbly) (substitute s2 .TypeVarWobbly))
        (fmap extract $ M.toList (getSubstMap s1) `intersect` M.toList (getSubstMap s2))
  in if agree then pure (s1 <> s2) else throwError "Cannot merge substitutions"



-- |Most general unifier
mgu :: Type -> Type -> Typechecker Substitution
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
match :: Type -> Type -> Typechecker Substitution
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
mguPred :: Pred -> Pred -> Typechecker Substitution
mguPred (IsIn i1 t1) (IsIn i2 t2) =
  if i1 == i2 then mgu t1 t2
  else throwError $ "Classes don't unify: " <> i1 <> " vs " <> i2


-- |match for predicates
matchPred :: Pred -> Pred -> Typechecker Substitution
matchPred (IsIn i1 t1) (IsIn i2 t2) =
  if i1 == i2 then match t1 t2
  else throwError $ "Classes don't match: " <> i1 <> " vs " <> i2


-- |Check whether class is defined
classDefined :: Name -> Bool
classDefined ce n = M.member n $ classes ce


-- |Introduces new class extending given superclasses
addClass :: Name -> Set Name -> ClassEnv -> Typechecker ClassEnv
addClass n sups ce = do
  when (classDefined ce n) (throwError $ "Class already defined: " <> n)
  case find (not . classDefined ce) (S.toList sups) of
    Nothing -> pure ()
    Just delikwent -> throwError $ "Superclass not defined: " <> delikwent
  pure $ updateClassEnv ce n (sups, S.empty)


-- |Declares new instance with qualification
addInst :: [Pred] -> Pred -> ClassEnv -> Typechecker ClassEnv
addInst ps p@(IsIn i _) ce = do
  when (not $ classDefined ce i) (throwError $ "Class not defined: " <> i)
  its <- instances ce i
  c <- super ce i
  let overlaps pr q = catchError (mguPred pr q >> pure True) (const $ pure False)
      qs = fmap (\(_ :=> q) -> q) its
  filterM (overlaps p) (S.toList qs) >>= \case
    [] -> pure ()
    (IsIn h _):_ -> throwError $ "Instances overlap: " <> i <> " with " <> h
  pure $ updateClassEnv ce i (c, S.insert (ps :=> p) its)


-- |Deep search for all superclasses' predicates
predsBySuper :: Pred -> Typechecker [Pred]
predsBySuper ce p@(IsIn i t) = do
  i' <- S.toList <$> super ce i
  if Prelude.null i'
    then pure [p]
    else insert p <$> (join <$> (forM i' (\i'' -> predsBySuper ce (IsIn i'' t))))


-- |Deep search for all matching instances' predicates
predsByInstances :: Pred -> Typechecker [Pred]
predsByInstances ce p@(IsIn i _) = do
  -- list of instances of i
  insts <- S.toList <$> instances ce i
  -- opertation that tries to strictly unify p with instance declaration
  let tryInst :: Qual Pred -> Typechecker [Pred]
      tryInst (ps :=> h) = do
        u <- matchPred h p
        pure $ fmap (substitute u) ps
  msum $ fmap tryInst insts


-- |Check if `p` will hold whenever all of `ps` are satisfied
entail :: [Pred] -> Pred -> Typechecker Bool
entail ce ps p = do
  -- all sets of superclasses of `ps`
  sups <- mapM (predsBySuper ce) ps
  -- all matching instances have this property
  let instCheck = do
        qs <- predsByInstances ce p
        ents <- mapM (entail ce ps) qs
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
toHNF :: Pred -> Typechecker [Pred]
toHNF ce p =
  if inHNF p
    then pure [p]
    else predsByInstances ce p >>= toHNFs ce

-- |Turn a set of predicates into hnf
toHNFs :: [Pred] -> Typechecker [Pred]
toHNFs ce ps = do
  pss <- mapM (toHNF ce) ps
  pure $ join pss


-- |Remove predicates that are entailed by others
simplify :: [Pred] -> Typechecker [Pred]
simplify ce pps = loop [] pps where
  loop rs [] = pure rs
  loop rs (p:ps) = do
    e <- entail ce (rs ++ ps) p
    if e then loop rs ps else loop (p:rs) ps


-- |Turns predicates into head normal form and then simplifies
reduce :: [Pred] -> Typechecker [Pred]
reduce ce ps = toHNFs ce ps >>= simplify ce


-- |Create scheme of generic type by itś arguments
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
lookupType :: Name -> Typechecker TypePoly -- TODO: to map
lookupType n = getTypeEnv >>= \te -> case M.lookup n te of
  Nothing -> throwError $ "Unbound id: " <> i
  Just tp -> pure tp


-- |Get access to currently carried substitution
getSubst :: Typechecker Substitution
getSubst = gets tsSubst


-- |Extend current substitution with new one
extendSubst :: Substitution -> Typechecker ()
extendSubst s = modify $ \ts -> ts{tsSubst = s <> tsSubst ts}


-- |Unify types and update substitution
unify :: Type -> Type -> Typechecker ()
unify t1 t2 = do
  s <- getSubst
  u <- mgu (substitute s t1) (substitute s t2)
  extendSubst u


-- |Returns new type variable
newVar :: String -> Kind -> Typechecker Type
newVar prefix k = do
  c <- gets tsSupply
  modify $ \s -> s{ tsSupply = c + 1 }
  pure $ TypeVarWobbly $ TypeVar (prefix <> show c) k


-- |Create new type varaibles for each parameter of scheme
freshInst :: TypePoly -> Typechecker (Qual Type)
freshInst (Forall ks qt) = do
  ts <- mapM (newVar "_Inst") ks
  pure $ instantiate ts qt

type Infer e t = TypeEnv -> e -> Typechecker ([Pred], t)


inferTypeExpr :: Infer Expr Type
inferTypeExpr ce as = \case
  Val v -> do
    sc <- lookupType v as
    (ps :=> t) <- freshInst sc
    pure (ps, t)
  ConstLit _ -> newVar "_Int" KType >>= \v -> pure ([IsIn "Num" v], v)
  Constructor (_, sc) -> do
    (ps :=> t) <- freshInst sc
    pure (ps, t)
  Application f a -> do
    (ps, tf) <- inferTypeExpr ce as f
    (qs, ta) <- inferTypeExpr ce as a
    t <- newVar "_Arg" KType
    unify (fun ta t) tf
    pure (ps ++ qs, t)

inferTypeLiteral :: Literal -> Typechecker ([Pred], Type)
inferTypeLiteral = \case
  LitInt _ -> newVar "_LI" KType >>= \v -> pure ([IsIn "Num" v], v)

inferTypePattern :: Pattern -> Typechecker ([Pred], TypeEnv, Type)
inferTypePattern = \case
  PVar i -> newVar "_PV" KType >>= \v -> pure ([], [i :>: toTypePoly v], v)
  PWildcard -> newVar "_PW" KType >>= \v -> pure ([], [], v)
  PAs i pat -> do
    (ps, as, t) <- inferTypePattern pat
    pure (ps, (i :>: toTypePoly t) : as, t)
  PLit l -> inferTypeLiteral l >>= \(ps, t) -> pure (ps, [], t)
  PNPlusK n _ -> newVar "_PNPK" KType >>= \t ->
    pure ([IsIn "Integral" t], [n :>: toTypePoly t], t)
  PConstructor (_, sc) pats -> do
    (ps, as, ts) <- inferTypePatterns pats
    t' <- newVar "_PC" KType
    (qs :=> t) <- freshInst sc
    unify t (S.foldr fun t' ts)
    pure (ps ++ qs, as, t')

inferTypePatterns :: Set Pattern -> Typechecker ([Pred], TypeEnv, Set Type)
inferTypePatterns pats = do
  psats <- mapM inferTypePattern (S.toList pats)
  let ps = join $ fmap (\(x,_,_) -> x) psats
      as = join $ fmap (\(_,x,_) -> x) psats
      ts = fmap (\(_,_,x) -> x) psats
  pure (ps, as, S.fromList ts)


-- |Left and right side of function definition
type Alt = (Set Pattern, Expr)


inferTypeAlt :: Infer Alt Type
inferTypeAlt ce as (pats, e) = do
  (ps, as', ts) <- inferTypePatterns pats
  (qs, t) <- inferTypeExpr ce (as' ++ as) e
  pure (ps ++ qs, S.foldr fun t ts)


inferTypeAlts :: [Alt] -> Type -> Typechecker [Pred]
inferTypeAlts ce as alts t = do
  psts <- mapM (inferTypeAlt ce as) alts
  void $ mapM (unify t) (fmap snd psts)
  pure (join $ fmap fst psts)


-- |Split predicates on deferred and contraints. fs are fixed variables and gs are varaibles over which we want to quantify
split :: [TypeVar] -> [TypeVar] -> [Pred] -> Typechecker ([Pred], [Pred])
split ce fs gs ps = do
  ps' <- reduce ce ps
  let (ds, rs) = partition (all (`elem` fs) . free) ps'
  rs' <- defaultedPreds ce (fs ++ gs) rs
  pure (ds, rs \\ rs')



type Ambiguity = (TypeVar, [Pred])

ambiguities :: [TypeVar] -> [Pred] -> [Ambiguity]
ambiguities vs ps = fmap (\v -> (v, filter (elem v . free) ps)) $ S.toList (free ps) \\ vs


candidates :: Ambiguity -> Typechecker [Type]
candidates ce (v, qs) =
  let is = fmap (\(IsIn i _) -> i) qs
      ts = fmap (\(IsIn _ t) -> t) qs
      filt :: [Type] -> Typechecker [Type]
      filt tts = flip filterM tts $ \t ->
        all id <$> mapM (entail ce []) [IsIn i t | i <- is]
  in if all ((TypeVarWobbly v)==) ts
     && any (`S.member` numClasses) is
     && all (`S.member` stdClasses) is
     then filt (S.toList $ defaults ce)
     else pure []


withDefaults :: ([Ambiguity] -> [Type] -> a)
             -> [TypeVar] -> [Pred]
             -> Typechecker a
withDefaults f ce vs ps = do
  let vps = ambiguities vs ps
  tss <- mapM (candidates ce) vps
  if any null tss
    then throwError "Cannot resolve ambiguity"
    else pure $ f vps (fmap head tss)

defaultedPreds :: [TypeVar] -> [Pred] -> Typechecker [Pred]
defaultedPreds = withDefaults (\vps _ -> join (fmap snd vps))


defaultSubst :: [TypeVar] -> [Pred] -> Typechecker Substitution
defaultSubst  = withDefaults (\vps ts -> Subst $ M.fromList $ zip (fmap (tName . fst) vps) ts)


type ExplBind = (Name, TypePoly, [Alt])

inferTypeExpl :: ExplBind -> Typechecker [Pred]
inferTypeExpl ce as (_, sc, alts) = do
  (qs :=> t) <- freshInst sc
  ps <- inferTypeAlts ce as alts t
  s <- getSubst
  let qs' = substitute s qs
      t'= substitute s t
      fs = S.toList $ free $ substitute s as
      gs = (S.toList $ free t') \\ fs
      sc' = quantify gs (qs' :=> t')
  ps' <- filterM (\x -> not <$> entail ce qs' x) (substitute s ps)
  (ds, rs) <- split ce fs gs ps'
  if | sc /= sc' -> throwError "Signature is too general"
     | not (null rs) -> throwError "Context is too weak"
     | otherwise -> pure ds


type ImplBind = (Name, [Alt])


restricted :: Foldable t => t ImplBind -> Bool
restricted bs = any simple bs where
  simple (_, alts) = any (null . fst) alts


inferTypeImpl :: Infer [ImplBind] TypeEnv
inferTypeImpl ce as bs = do
  ts <- mapM (const $ newVar "IMPL" KType) bs
  let is = fmap fst bs
      scs = fmap toTypePoly ts
      as' = zipWith (:>:) is scs ++ as
      altss = fmap snd bs
  pss <- sequence (zipWith (inferTypeAlts ce as') altss ts)
  s <- getSubst
  let ps' = substitute s (join pss)
      ts' = substitute s ts
      fs = S.toList $ free (substitute s as)
      vss = fmap (S.toList . free) ts'
      gs = foldr1 union vss \\ fs
  (ds, rs) <- split ce fs (foldr1 intersect vss) ps'
  if restricted bs
    then
    let gs' = filter (`S.member` free rs) gs
        scs' = fmap (quantify gs' . ([] :=>)) ts'
    in pure (ds ++ rs, zipWith (:>:) is scs')
    else
    let scs' = fmap (quantify gs . (rs :=>)) ts'
    in pure (ds, zipWith (:>:) is scs')

type Bindings = ([ExplBind], [[ImplBind]])


inferTypeBindings :: Infer Bindings TypeEnv
inferTypeBindings ce as (es, iss) = do
  let as' = [v :>: sc | (v, sc, _) <- es]
  (ps, as'') <- inferTypeSeq inferTypeImpl ce (as' ++ as) iss
  qss <- mapM (inferTypeExpl ce (as'' ++ as' ++ as)) es
  pure (ps ++ join qss, as'' ++ as')


inferTypeSeq :: Infer bg TypeEnv -> Infer [bg] TypeEnv
inferTypeSeq ti ce as = \case
  [] -> pure ([], [])
  (bs:bss) -> do
    (ps, as') <- ti ce as bs
    (qs, as'') <- inferTypeSeq ti ce (as' ++ as) bss
    pure (ps ++ qs, as'' ++ as')

type Program = [Bindings]

inferTypeProgram :: Program -> Typechecker TypeEnv
inferTypeProgram ce as bgs = do
  (ps, as') <- inferTypeSeq inferTypeBindings ce as bgs
  s <- getSubst
  rs <- reduce ce (substitute s ps)
  s' <- defaultSubst ce [] rs
  pure (substitute (s' <> s) as')


-- |Evaluation of typechecker
runTypechecker :: Typechecker a -> Either String a
runTypechecker = flip evalState (TypecheckerState 0 mempty)
  . flip runReaderT ()
  . runExceptT

-- |Toplevel typechecking of expression
typecheck :: Program -> Either ErrMsg TypeEnv
typecheck p = runTypechecker (inferTypeProgram emptyClassEnv [] p)

pat = PVar "wisienka"
expr = ConstLit $ LitInt 3

impl :: ImplBind
impl = ("wisienka", [(S.singleton pat, expr)])

pr :: Program
pr = [([],[[impl]])]
