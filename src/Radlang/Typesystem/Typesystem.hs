{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf       #-}
-- |Utilities to solve tasks related to typechecking, kindchecking and building class env
module Radlang.Typesystem.Typesystem where

import           Control.Applicative
import           Control.Monad.Except
import           Data.List                  as DL
import qualified Data.Map.Strict            as M
import           Data.Set                   (Set)
import qualified Data.Set                   as S

import           Radlang.Error
import           Radlang.Types


-- |Get direct superclasses of class by name
super :: HasClassEnv m => Name -> m (Set Name)
super n = getClassEnv >>= \ce -> case M.lookup n (classes ce) of
  Just (Class is _) -> pure is
  Nothing -> classEnvError $ "superclass lookup: " <> n <> " not defined"


-- |Get all superclasses of class by name (slow)
deepSuper :: HasClassEnv m => Name -> m (Set Name)
deepSuper n = getClassEnv >>= \ce -> case M.lookup n (classes ce) of
  Just (Class is _) -> do sups <- traverse deepSuper $ S.toList is
                          pure $ foldr S.union is sups
  Nothing -> classEnvError $ "deep superclass lookup: " <> n <> " not defined"


-- |Get direct subclasses of class by name
sub :: HasClassEnv m => Name -> m (Set Name)
sub n = getClassEnv >>= \ce ->
  pure $ S.fromList $ fmap fst $ filter (\(_, Class is _) -> S.member n is) (M.toList $ classes ce)


-- |Get all subclasses of class by name (slow)
deepSub :: HasClassEnv m => Name -> m (Set Name)
deepSub n = do
  shallow <- sub n
  subs <- traverse deepSub $ S.toList shallow
  pure $ foldr S.union shallow subs


-- |Get instances of class by name
instances :: HasClassEnv m => Name -> m (Set Inst)
instances n = getClassEnv >>= \ce -> case M.lookup n (classes ce) of
  Just (Class _ its) -> pure its
  Nothing -> classEnvError $ "instances lookup: " <> n <> " not defined"


-- |Check whether class is defined
classDefined :: HasClassEnv m => Name -> m Bool
classDefined n = M.member n . classes <$> getClassEnv


-- |Creates substitution with type assigned
bindVar :: MonadError ErrMsg m => TypeVar -> Type -> m Substitution
bindVar tv t = if
    | t == TypeVarWobbly tv -> pure mempty
    | elem tv (free t) ->
      typecheckError $ "Occur check: cannot create infinite type: " <> tName tv <> " := " <> show t
    | kind tv /= kind t -> kindcheckError $ "Kinds don't match: " <> show (kind tv)
      <> " vs " <> show (kind t)
    | otherwise -> pure $ Subst $ M.singleton (tName tv) t



-- |Merge substitutions ensuring that they agree
merge :: MonadError ErrMsg m => Substitution -> Substitution -> m Substitution
merge s1 s2 =
  let extract (n, t) = TypeVar n (kind t)
      agree = all (liftA2 (==) (substitute s1 . TypeVarWobbly) (substitute s2 .TypeVarWobbly))
        (fmap extract $ M.toList (getSubstMap s1) `intersect` M.toList (getSubstMap s2))
  in if agree then pure (s1 <> s2) else typecheckError "Cannot merge substitutions"



-- |Most general unifier
mgu :: MonadError ErrMsg m => Type -> Type -> m Substitution
mgu t1 t2 = case (t1, t2) of
  (TypeVarWobbly tv, _) -> bindVar tv t2
  (_, TypeVarWobbly tv) -> bindVar tv t1
  (TypeApp f1 a1, TypeApp f2 a2) -> do
    sf <- mgu f1 f2
    sa <- mgu (substitute sf a1) (substitute sf a2)
    pure $ sa <> sf
  (TypeVarRigid a, TypeVarRigid b) ->
    if a == b
    then pure mempty
    else typecheckError $ "Cannot unify rigid different type variables: " <> tName a <> " vs " <> tName b
  (TypeVarRigid (TypeVar a _), b) ->
    typecheckError $ "Cannot unify rigid type variable with non-rigid type: " <> a <> " vs " <> show b
  (b, TypeVarRigid (TypeVar a _)) ->
    typecheckError $ "Cannot unify rigid type variable with non-rigid type: " <> show b <> " vs " <> a
  _ -> typecheckError $ "Cannot unify types: " <> show t1 <> " vs " <> show t2



-- |Unifier that uses `merge` instead of `<>`
match :: (MonadError ErrMsg m, MonadIO m)
  => Type -> Type -> m Substitution
match t1 t2 = case (t1, t2) of
  (TypeApp f1 a1, TypeApp f2 a2) -> do
    sf <- match f1 f2
    sa <- match a1 a2
    merge sa sf
  (TypeVarWobbly tv, t) | kind tv == kind t -> bindVar tv t2
  (TypeVarRigid a, TypeVarRigid b) ->
    if a == b
    then pure mempty
    else typecheckError $ "Cannot merge rigid different type variables: " <> tName a <> " vs " <> tName b
  (TypeVarRigid (TypeVar a _), b) ->
    typecheckError $ "Cannot merge rigid type variable with non-rigid type: " <> a <> " vs " <> show b
  (b, TypeVarRigid (TypeVar a _)) ->
    typecheckError $ "Cannot merge rigid type variable with non-rigid type: " <> show b <> " vs " <> a
  _ -> typecheckError $ "Cannot merge types: " <> show t1 <> " vs " <> show t2


-- |mgu for predicates
mguPred :: MonadError ErrMsg m => Pred -> Pred -> m Substitution
mguPred (IsIn i1 t1) (IsIn i2 t2) =
  if i1 == i2 then mgu t1 t2
  else typecheckError $ "Classes don't unify: " <> i1 <> " vs " <> i2


-- |match for predicates
matchPred :: (MonadError ErrMsg m, MonadIO m) => Pred -> Pred -> m (Maybe Substitution)
matchPred (IsIn i1 t1) (IsIn i2 t2) =
  if i1 == i2 then catchError (Just <$> match t1 t2) (const $ pure Nothing)
  else typecheckError $ "Classes don't match: " <> i1 <> " vs " <> i2



-- |Deep search for all superclasses' predicates
predsBySuper :: HasClassEnv m => Pred -> m [Pred]
predsBySuper p@(IsIn i t) = do
  i' <- S.toList <$> super i
  if Prelude.null i'
    then pure [p]
    else insert p <$> (join <$> (forM i' (\i'' -> predsBySuper (IsIn i'' t))))


-- |Deep search for all matching instances' predicates
predsByInstances :: (MonadIO m, HasClassEnv m) => Pred -> m [Pred]
predsByInstances p@(IsIn i _) = do
  -- list of instances of i
  insts <- S.toList <$> instances i
  -- opertation that tries to strictly unify p with instance declaration
  let tryInst (ps :=> h) = do
        u <- matchPred h p
        pure $ u >>= \uu -> Just (fmap (substitute uu) ps)
  d <- msum <$> traverse tryInst insts
  maybe (typecheckError $ "Could not get valid instance for " <> show p) pure d


-- |Check if `p` will hold whenever all of `ps` are satisfied
entail :: (HasClassEnv m, MonadIO m) => [Pred] -> Pred -> m Bool
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
  (TypeVarRigid _)  -> False
  (TypeApp tt _)    -> inHNF (IsIn undefined tt)
  _                 -> error "unimplemented ihnf" -- FIXME


-- |Turn predicate into head normal form
toHNF :: (HasClassEnv m, MonadIO m) => Pred -> m [Pred]
toHNF p =
  if inHNF p
    then pure [p]
    else predsByInstances p >>= toHNFs

-- |Turn a set of predicates into hnf
toHNFs :: (HasClassEnv m, MonadIO m) => [Pred] -> m [Pred]
toHNFs ps = do
  pss <- mapM toHNF ps
  pure $ join pss


-- |Remove predicates that are entailed by others
simplify :: (HasClassEnv m, MonadIO m) => [Pred] -> m [Pred]
simplify pps = loop [] pps where
  loop rs [] = pure rs
  loop rs (p:ps) = do
    e <- entail (rs ++ ps) p
    if e then loop rs ps else loop (p:rs) ps


-- |Turns predicates into head normal form and then simplifies
reduce :: (HasClassEnv m, MonadIO m) => [Pred] -> m [Pred]
reduce ps = toHNFs ps >>= simplify


-- |Create scheme of generic type by its arguments
quantify :: [TypeVar] -> Qual Type -> TypePoly
quantify vs qt = Forall ks (substitute s qt) where
  vs' = [v | v <- free qt, v `elem` vs]
  ks = fmap kind vs'
  ns = fmap tName vs'
  s = Subst $ M.fromList $ zip ns (fmap TypeGeneric [0..])


-- |Quantifies type by all of its free variables
quantifyAll :: Qual Type -> TypePoly
quantifyAll qt = quantify (free qt) qt


-- |Turn plain type into scheme
toTypePoly :: Type -> TypePoly
toTypePoly t = Forall [] ([] :=> t)

