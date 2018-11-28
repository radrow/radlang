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
import Control.Monad.Except

import Radlang.Types
import Radlang.Typedefs


-- |Gets superclasses of class by name
super :: ClassEnv -> Name -> Typechecker (Set Name)
super ce n = case M.lookup n (classes ce) of
  Just (is, _) -> pure is
  Nothing -> throwError $ "superclass lookup: " <> n <> " not defined"


-- |Gets instances of class by name
instances :: ClassEnv -> Name -> Typechecker (Set Inst)
instances ce n = case M.lookup n (classes ce) of
  Just (_, its) -> pure its
  Nothing -> throwError $ "instances lookup: " <> n <> " not defined"


updateClassEnv :: ClassEnv -> Name -> Class -> ClassEnv
updateClassEnv ce n c = ce {classes = M.insert n c (classes ce)}


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



-- |Merge substitution ensuring that they agree
merge :: Substitution -> Substitution -> Typechecker Substitution
merge s1 s2 =
  let extract (n, t) = TypeVar n (kind t)
      agree = all (liftA2 (==) (substitute s1 . TypeVarWobbly) (substitute s2 .TypeVarWobbly))
        (fmap extract $ M.toList (getSubstMap s1) `intersect` M.toList (getSubstMap s2))
  in if agree then pure (s1 <> s2) else throwError "Cannot merge substitutions"



-- |Most general unifier
mgu :: Type -> Type -> Typechecker Substitution
mgu t1 t2 = case (t1, t2) of
  (TypeInt, TypeInt) -> pure mempty
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
  (TypeInt, TypeInt) -> pure mempty
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


mguPred :: Pred -> Pred -> Typechecker Substitution
mguPred (IsIn i1 t1) (IsIn i2 t2) =
  if i1 == i2 then mgu t1 t2
  else throwError $ "Classes don't unify: " <> i1 <> " vs " <> i2


matchPred :: Pred -> Pred -> Typechecker Substitution
matchPred (IsIn i1 t1) (IsIn i2 t2) =
  if i1 == i2 then match t1 t2
  else throwError $ "Classes don't match: " <> i1 <> " vs " <> i2


-- |Check whether class is defined
classDefined :: ClassEnv -> Name -> Bool
classDefined ce n = M.member n $ classes ce


-- |Introduces new class extending given superclasses
addClass :: Name -> Set Name -> ClassEnv -> Typechecker ClassEnv
addClass n sups ce = do
  when (classDefined ce n) (throwError $ "Class already defined: " <> n)
  case find (not . classDefined ce) (S.toList sups) of
    Nothing -> pure ()
    Just delikwent -> throwError $ "Superclass not defined: " <> delikwent
  pure $ updateClassEnv ce n (sups, S.empty)


-- |Declares new instance
addInst :: Set Pred -> Pred -> ClassEnv -> Typechecker ClassEnv
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
bySuper :: ClassEnv -> Pred -> Typechecker (Set Pred)
bySuper ce p@(IsIn i t) = do
  i' <- S.toList <$> super ce i
  if Prelude.null i'
    then pure $ S.singleton p
    else S.insert p <$> (S.unions <$> (forM i' (\i'' -> bySuper ce (IsIn i'' t))))


-- |Deep search for all matching instances' predicates
byInst :: ClassEnv -> Pred -> Typechecker (Set Pred)
byInst ce p@(IsIn i t) = do -- TODO ensure if it works
  let tryInst (ps :=> h) = do
        u <- matchPred h p
        pure $ fmap (substitute u) ps
  insts <- S.toList <$> instances ce i
  let its :: [Typechecker (Set Pred)]
      its = flip fmap insts $ \it -> tryInst it
  msum its


-- |Check if `p` will hold whenever all of `ps` are satisfied
entail :: ClassEnv -> Set Pred -> Pred -> Typechecker Bool
entail ce ps p = do
  -- all sets of superclasses of `ps`
  sups <- traverse (bySuper ce) (S.toList ps)
  -- all matching instances have this property
  let instCheck = do
        qs <- S.toList <$> byInst ce p
        ents <- traverse (entail ce ps) qs
        pure $ all id ents
  instc <- catchError instCheck (const $ pure False) -- this `catch` may cause problems
  pure $ any (elem p) sups || instc


inHNF :: Pred -> Bool
inHNF (IsIn _ t) = case t of
  (TypeVarWobbly _) -> True
  (TypeVarRigid _) -> False
  (TypeApp tt _) -> inHNF (IsIn undefined tt)
  _ -> error "unimplemented ihnf"


toHNF :: ClassEnv -> Pred -> Typechecker (Set Pred)
toHNF ce p =
  if inHNF p
    then pure $ S.singleton p
    else byInst ce p >>= toHNFs ce


toHNFs :: ClassEnv -> Set Pred -> Typechecker (Set Pred)
toHNFs ce ps = do
  pss <- S.fromList <$> mapM (toHNF ce) (S.toList ps)
  pure $ join pss


simplify :: ClassEnv -> Set Pred -> Typechecker (Set Pred)
simplify ce pps = S.fromList <$> loop [] (S.toList pps) where
  loop :: [Pred] -> [Pred] -> Typechecker [Pred]
  loop rs [] = pure rs
  loop rs (p:ps) = do
    e <- entail ce (S.fromList $ rs ++ ps) p
    if e
      then loop rs ps
      else loop (p:rs) ps


reduce :: ClassEnv -> Set Pred -> Typechecker (Set Pred)
reduce ce ps = toHNFs ce ps >>= simplify ce


quantify :: Set TypeVar -> Qual Type -> Scheme
quantify vs qt = Forall ks (substitute s qt) where
  vs' = [v | v <- S.toList $ free qt, v `S.member` vs]
  ks = fmap kind vs'
  ns = fmap tName vs'
  s = Subst $ M.fromList $ zip ns (fmap TypeADT [0..])

toScheme :: Type -> Scheme
toScheme t = Forall [] (S.empty :=> t)


lookupType :: Name -> [Assumption] -> Typechecker Scheme -- TODO: to map
lookupType i [] = throwError $ "Unbound id: " <> i
lookupType i ((i' :>: sc): as) = if i == i' then pure sc else lookupType i as


getSubst :: Typechecker Substitution
getSubst = gets tsSubst


extendSubst :: Substitution -> Typechecker ()
extendSubst s = modify $ \ts -> ts{tsSubst = s <> tsSubst ts}


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

freshInst :: Scheme -> Typechecker (Qual Type)
freshInst (Forall ks qt) = do
  ts <- mapM (newVar "_Inst") ks
  pure $ inst ts qt

type Infer e t = ClassEnv -> [Assumption] -> e -> Typechecker (Set Pred, t)

inferTypeExpr :: Infer Expr Type
inferTypeExpr ce as = \case
  Val v -> do
    sc <- lookupType v as
    (ps :=> t) <- freshInst sc
    pure (ps, t)
  ConstLit _ -> newVar "_Int" KType >>= \v -> pure (S.singleton $ IsIn "Num" v, v)
  Constructor (_ :>: sc) -> do
    (ps :=> t) <- freshInst sc
    pure (ps, t)
  Application f a -> do
    (ps, tf) <- inferTypeExpr ce as f
    (qs, ta) <- inferTypeExpr ce as a
    t <- newVar "_Arg" KType
    unify (fun ta t) tf
    pure (S.union ps qs, t)

inferTypeLiteral :: Literal -> Typechecker (Set Pred, Type)
inferTypeLiteral = \case
  LitInt _ -> newVar "_LI" KType >>= \v -> pure (S.singleton (IsIn "Num" v), v)

inferTypePattern :: Pattern -> Typechecker (Set Pred, [Assumption], Type)
inferTypePattern = \case
  PVar i -> newVar "_PV" KType >>= \v -> pure (S.empty, [i :>: toScheme v], v)
  PWildcard -> newVar "_PW" KType >>= \v -> pure (S.empty, [], v)
  PAs i pat -> do
    (ps, as, t) <- inferTypePattern pat
    pure (ps, (i :>: toScheme t) : as, t)
  PLit l -> inferTypeLiteral l >>= \(ps, t) -> pure (ps, [], t)
  PNPlusK n k -> newVar "_PNPK" KType >>= \t ->
    pure ( S.singleton $ IsIn "Integral" t, [n :>: toScheme t], t)
  PConstructor (i :>: sc) pats -> do
    (ps, as, ts) <- inferTypePatterns pats
    t' <- newVar "_PC" KType
    (qs :=> t) <- freshInst sc
    unify t (S.foldr fun t' ts)
    pure (S.union ps qs, as, t')

inferTypePatterns :: Set Pattern -> Typechecker (Set Pred, [Assumption], Set Type)
inferTypePatterns pats = do
  psats <- traverse inferTypePattern (S.toList pats)
  let ps = S.unions $ fmap (\(x,_,_) -> x) psats
      as = join $ fmap (\(_,x,_) -> x) psats
      ts = fmap (\(_,_,x) -> x) psats
  pure (ps, as, S.fromList ts)


type Alt = (Set Pattern, Expr)

inferTypeAlt :: Infer Alt Type
inferTypeAlt ce as (pats, e) = do
  (ps, as', ts) <- inferTypePatterns pats
  (qs, t) <- inferTypeExpr ce (as' ++ as) e
  pure (S.union ps qs, S.foldr fun t ts)


inferTypeAlts :: ClassEnv -> [Assumption] -> [Alt] -> Type -> Typechecker (Set Pred)
inferTypeAlts ce as alts t = do
  psts <- traverse (inferTypeAlt ce as) alts
  void $ traverse (unify t) (fmap snd psts)
  pure (S.unions $ fmap fst psts)


split :: ClassEnv -> Set TypeVar -> Set TypeVar -> Set Pred -> Typechecker (Set Pred, Set Pred)
split ce fs gs ps = do
  ps' <- reduce ce ps
  let (ds, rs) = S.partition (all (`S.member` fs) . free) ps'
  rs' <- defaultedPreds ce (S.union fs gs) rs
  pure (ds, rs S.\\ rs')

type Ambiguity = (TypeVar, Set Pred)

ambiguities :: Set TypeVar -> Set Pred -> Set Ambiguity
ambiguities vs ps = fmap (\v -> (v, S.filter (elem v . free) ps)) $ free ps S.\\ vs


candidates :: ClassEnv -> Ambiguity -> Typechecker (Set Type)
candidates ce (v, qs) =
  let is = fmap (\(IsIn i _) -> i) qs
      ts = fmap (\(IsIn _ t) -> t) qs
      filt :: Set Type -> Typechecker (Set Type)
      filt tts = fmap S.fromList $ flip filterM (S.toList tts) $ \t ->
        all id <$> traverse (entail ce S.empty) [IsIn i t | i <- S.toList is]
  in if all ((TypeVarWobbly v)==) ts
     && any (`S.member` numClasses) is
     && all (`S.member` stdClasses) is
     then filt (defaults ce)
     else pure S.empty


withDefaults :: ([Ambiguity] -> [Type] -> a)
             -> ClassEnv -> Set TypeVar -> Set Pred
             -> Typechecker a
withDefaults f ce vs ps = do -- TODO: Ensure if it is not fuckupped
  let vps = ambiguities vs ps
  tss <- traverse (candidates ce) $ S.toList vps
  if any S.null tss
    then throwError "Cannot resolve ambiguity"
    else pure $ f (S.toList vps) (fmap S.findMin tss)

defaultedPreds :: ClassEnv -> Set TypeVar -> Set Pred -> Typechecker (Set Pred)
defaultedPreds = withDefaults (\vps _ -> S.unions (fmap snd vps))


defaultSubst :: ClassEnv -> Set TypeVar -> Set Pred -> Typechecker Substitution
defaultSubst  = withDefaults (\vps ts -> Subst $ M.fromList $ zip (fmap (tName . fst) vps) ts)


type ExplBind = (Name, Scheme, [Alt])

inferTypeExpl :: ClassEnv -> [Assumption] -> ExplBind -> Typechecker (Set Pred)
inferTypeExpl ce as (i, sc, alts) = do
  (qs :=> t) <- freshInst sc
  ps <- inferTypeAlts ce as alts t
  s <- getSubst
  let qs' = substitute s qs
      t'= substitute s t
      fs = free $ substitute s as
      gs = free t' S.\\ fs
      sc' = quantify gs (qs' :=> t')
  ps' <- S.fromList <$> filterM (\x -> not <$> entail ce qs' x) (S.toList $ substitute s ps)
  (ds, rs) <- split ce fs gs ps'
  if | sc /= sc' -> throwError "Signature is too general"
     | not (S.null rs) -> throwError "Context is too weak"
     | otherwise -> pure ds


type ImplBind = (Name, [Alt])


restricted :: Foldable t => t ImplBind -> Bool
restricted bs = any simple bs where
  simple (_, alts) = any (null . fst) alts


inferTypeImpl :: Infer [ImplBind] [Assumption]
inferTypeImpl ce as bs = do
  ts <- traverse (const $ newVar "IMPL" KType) bs
  let is = fmap fst bs
      scs = fmap toScheme ts
      as' = zipWith (:>:) is scs ++ as
      altss = fmap snd bs
  pss <- sequence (zipWith (inferTypeAlts ce as') altss ts)
  s <- getSubst
  let ps' = substitute s (S.unions pss)
      ts' = substitute s ts
      fs = free (substitute s as)
      vss = fmap free ts'
      gs = foldr1 union (fmap S.toList vss) \\ S.toList fs
  (ds, rs) <- split ce fs (foldr1 S.intersection vss) ps'
  if restricted bs
    then
    let gs' = S.fromList gs S.\\ free rs
        scs' = fmap (quantify gs' . (S.empty :=>)) ts'
    in pure (S.union ds rs, zipWith (:>:) is scs')
    else
    let scs' = fmap (quantify (S.fromList gs) . (rs :=>)) ts'
    in pure (ds, zipWith (:>:) is scs')

type Bindings = ([ExplBind], [[ImplBind]])


inferTypeBindings :: Infer Bindings [Assumption]
inferTypeBindings ce as (es, iss) = do
  let as' = [v :>: sc | (v, sc, _) <- es]
  (ps, as'') <- inferTypeSeq inferTypeImpl ce (as' ++ as) iss
  qss <- traverse (inferTypeExpl ce (as'' ++ as' ++ as)) es
  pure (S.union ps $ S.unions qss, as'' ++ as')


inferTypeSeq :: Infer bg [Assumption] -> Infer [bg] [Assumption]
inferTypeSeq ti ce as = \case
  [] -> pure (S.empty, [])
  (bs:bss) -> do
    (ps, as') <- ti ce as bs
    (qs, as'') <- inferTypeSeq ti ce (as' ++ as) bss
    pure (S.union ps qs, as'' ++ as')

type Program = [Bindings]

inferTypeProgram :: ClassEnv -> [Assumption] -> Program -> Typechecker [Assumption]
inferTypeProgram ce as bgs = do
  (ps, as') <- inferTypeSeq inferTypeBindings ce as bgs
  s <- getSubst
  rs <- reduce ce (substitute s ps)
  s' <- defaultSubst ce S.empty rs
  pure (substitute (s' <> s) as')


-- -- |Evaluation of typechecker
-- runTypechecker :: Typechecker a -> Either String a
-- runTypechecker = flip evalState (TypecheckerState 0)
--   . flip runReaderT (Typespace M.empty)
--   . runExceptT

-- -- |Toplevel typechecking of expression
-- typecheck :: Expr -> Either ErrMsg Type
-- typecheck e = uncurry substitute <$> runTypechecker (withStdlib $ inferType e)
