-- |Utilities to solve tasks related to typechecking, kindchecking and building interface env
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE MultiWayIf        #-}
{-# LANGUAGE OverloadedStrings #-}
module Radlang.Typesystem.Typesystem where

import           Control.Applicative
import           Control.Monad.Except
import           Data.List                  as DL
import qualified Data.Map.Strict            as M
import           Data.Set                   (Set)
import qualified Data.Set                   as S
import           Data.Text as T

import           Radlang.Error
import           Radlang.Types

-- |Get direct superinterfaces of interface by name
super :: HasInterfaceEnv m => Name -> m (Set Name)
super n = getInterfaceEnv >>= \ce -> case M.lookup n (interfaces ce) of
  Just (Interface is _) -> pure is
  Nothing -> interfaceEnvError $ "superinterface lookup: " <> n <> " not defined"


-- |Get all superinterfaces of interface by name (slow)
deepSuper :: HasInterfaceEnv m => Name -> m (Set Name)
deepSuper n = getInterfaceEnv >>= \ce -> case M.lookup n (interfaces ce) of
  Just (Interface is _) -> do sups <- traverse deepSuper $ S.toList is
                              pure $ DL.foldr S.union is sups
  Nothing -> interfaceEnvError $ "deep superinterface lookup: " <> n <> " not defined"


-- |Get direct subinterfaces of interface by name
sub :: HasInterfaceEnv m => Name -> m (Set Name)
sub n = getInterfaceEnv >>= \ce ->
  pure $ S.fromList $ fmap fst $ DL.filter (\(_, Interface is _) -> S.member n is) (M.toList $ interfaces ce)


-- |Get all subinterfaces of interface by name (slow)
deepSub :: HasInterfaceEnv m => Name -> m (Set Name)
deepSub n = do
  shallow <- sub n
  subs <- traverse deepSub $ S.toList shallow
  pure $ DL.foldr S.union shallow subs


-- |Get impls of interface by name
impls :: HasInterfaceEnv m => Name -> m (Set Impl)
impls n = getInterfaceEnv >>= \ce -> case M.lookup n (interfaces ce) of
  Just (Interface _ its) -> pure its
  Nothing -> interfaceEnvError $ "impls lookup: " <> n <> " not defined"


-- |Check whether interface is defined
interfaceDefined :: HasInterfaceEnv m => Name -> m Bool
interfaceDefined n = M.member n . interfaces <$> getInterfaceEnv


-- |Creates substitution with type assigned
bindVar :: MonadError ErrMsg m => TypeVar -> Type -> m Substitution
bindVar tv t = if
    | t == TypeVarWobbly tv -> pure mempty
    | elem tv (free t) ->
      typecheckError $ "Occur check: cannot create infinite type: " <> tName tv <> " := " <> T.pack (show t)
    | kind tv /= kind t -> kindcheckError $ "Kinds don't match for " <> tName tv <> ": " <> T.pack (show (kind tv))
      <> " vs " <> T.pack (show (kind t))
    | otherwise -> pure $ Subst $ M.singleton (tName tv) t



-- |Merge substitutions ensuring that they agree
merge :: MonadError ErrMsg m => Substitution -> Substitution -> m Substitution
merge s1 s2 =
  let extract (n, t) = TypeVar n (kind t)
      agree = DL.all (liftA2 (==) (substitute s1 . TypeVarWobbly) (substitute s2 .TypeVarWobbly))
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
    typecheckError $ "Cannot unify rigid type variable with non-rigid type: " <> a <> " vs " <> T.pack (show b)
  (b, TypeVarRigid (TypeVar a _)) ->
    typecheckError $ "Cannot unify rigid type variable with non-rigid type: " <> T.pack (show b) <> " vs " <> a
  _ -> typecheckError $ "Cannot unify types: " <> T.pack (show t1) <> " vs " <> T.pack (show t2)



-- |Unifier that uses `merge` instead of `<>`
match :: MonadError ErrMsg m
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
    else typecheckError $ "Cannot merge different rigid type variables: " <> tName a <> " vs " <> tName b
  (TypeVarRigid (TypeVar a _), b) ->
    typecheckError $ "Cannot merge rigid type variable with non-rigid type: " <> a <> " vs " <> T.pack (show b)
  (b, TypeVarRigid (TypeVar a _)) ->
    typecheckError $ "Cannot merge rigid type variable with non-rigid type: " <> T.pack (show b) <> " vs " <> a
  _ -> typecheckError $ "Cannot merge types: " <> T.pack (show t1) <> " vs " <> T.pack (show t2)

generalizeTo :: MonadError ErrMsg m
             => Type -> Type -> m Substitution
generalizeTo t1 t2 = case (t1, t2) of
  (_, TypeVarWobbly tv) | kind t1 == kind tv -> bindVar tv t1
  (TypeVarRigid a, TypeVarRigid b) ->
    if a == b
    then pure mempty
    else typecheckError $ "Cannot generalize rigid type variable: " <> tName a <> " vs " <> tName b
  (TypeApp f1 a1, TypeApp f2 a2) -> do
    s1 <- generalizeTo f1 f2
    s2 <- generalizeTo a1 a2
    merge s1 s2
  _ -> typecheckError $ "Cannot generalize " <> T.pack (show t1) <> " to " <> T.pack (show t2)


-- |mgu for predicates
mguPred :: MonadError ErrMsg m => Pred -> Pred -> m Substitution
mguPred (IsIn i1 t1) (IsIn i2 t2) =
  if i1 == i2 then mgu t1 t2
  else typecheckError $ "Interfaces don't unify: " <> i1 <> " vs " <> i2


-- |match for predicates
matchPred :: MonadError ErrMsg m => Pred -> Pred -> m (Maybe Substitution)
matchPred (IsIn i1 t1) (IsIn i2 t2) =
  if i1 == i2 then catchError (Just <$> match t1 t2) (const $ pure Nothing)
  else typecheckError $ "Interfaces don't match: " <> i1 <> " vs " <> i2



-- |Deep search for all superinterfaces' predicates
predsBySuper :: HasInterfaceEnv m => Pred -> m [Pred]
predsBySuper p@(IsIn i t) = do
  i' <- S.toList <$> super i
  if Prelude.null i'
    then pure [p]
    else insert p <$> (join <$> (forM i' (\i'' -> predsBySuper (IsIn i'' t))))


-- |Deep search for all matching impls' predicates
predsByImpls :: HasInterfaceEnv m => Pred -> m [Pred]
predsByImpls p@(IsIn i _) = do
  -- list of impls of i
  insts <- S.toList <$> impls i
  -- opertation that tries to strictly unify p with impl declaration
  let tryInst (ps :=> h) = do
        u <- matchPred h p
        pure $ u >>= \uu -> Just (fmap (substitute uu) ps)
  d <- msum <$> traverse tryInst insts
  maybe (typecheckError $ "Could not get valid impl for " <> T.pack (show p)) pure d


-- |Check if predicate will hold whenever all of initial predicates are satisfied
entail :: HasInterfaceEnv m => [Pred] -> Pred -> m Bool
entail ps p = do
  -- all sets of superinterfaces of `ps`
  sups <- mapM predsBySuper ps
  -- all matching impls have this property
  let instCheck = do
        qs <- predsByImpls p
        ents <- mapM (entail ps) qs
        pure $ DL.all id ents
  instc <- catchError instCheck (const $ pure False) -- FIXME this `catch` may cause problems
  pure $ DL.any (elem p) sups || instc


-- |Check if predicate is in head normal form. -- TODO: what does it mean?
inHNF :: Pred -> Bool
inHNF (IsIn _ t) = case t of
  (TypeVarWobbly _) -> True
  (TypeVarRigid _)  -> False
  (TypeApp tt _)    -> inHNF (IsIn undefined tt)
  _                 -> error "unimplemented ihnf" -- FIXME


-- |Turn predicate into head normal form
toHNF :: HasInterfaceEnv m => Pred -> m [Pred]
toHNF p =
  if inHNF p
    then pure [p]
    else predsByImpls p >>= toHNFs

-- |Turn a set of predicates into hnf
toHNFs :: HasInterfaceEnv m => [Pred] -> m [Pred]
toHNFs ps = do
  pss <- mapM toHNF ps
  pure $ join pss


-- |Remove predicates that are entailed by others
simplify :: HasInterfaceEnv m => [Pred] -> m [Pred]
simplify pps = loop [] pps where
  loop rs [] = pure rs
  loop rs (p:ps) = do
    e <- entail (rs ++ ps) p
    if e then loop rs ps else loop (p:rs) ps


-- |Turns predicates into head normal form and then simplifies
reduce :: HasInterfaceEnv m => [Pred] -> m [Pred]
reduce ps = toHNFs ps >>= simplify


-- |Create scheme of generic type by its arguments
quantify :: [TypeVar] -> Qual Type -> TypePoly
quantify vs qt = Forall ks (substitute s qt) where
  vs' = [v | v <- nub (free qt), v `elem` vs]
  ks = fmap kind vs'
  ns = fmap tName vs'
  s = Subst $ M.fromList $ DL.zip ns (fmap TypeGeneric [0..])


-- |Quantifies type by all of its free variables
quantifyAll :: Qual Type -> TypePoly
quantifyAll qt = quantify (free qt) qt


-- |Turn plain type into scheme
toTypePoly :: Type -> TypePoly
toTypePoly t = Forall [] ([] :=> t)
