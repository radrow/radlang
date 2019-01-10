{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedLists     #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Radlang.Kindchecker
  ( runKindchecker
  , getKindspace
  , unionKindspaces
  , kindlookNewType
  , withKindspace
  , kindcheckNewType
  , kindcheckRawTypeDecl
  , toKind
  , kindOf
  ) where

import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State.Strict
import           Data.List.NonEmpty
import qualified Data.Map.Strict            as M
import qualified Data.Set                   as S

import           Radlang.Types              hiding (TypePoly, free, getSubstMap,
                                             substitute)


-- |Returns typespace
getKindspace :: Kindchecker Kindspace
getKindspace = asks fst


-- |Returns class kinds
getClassKinds :: Kindchecker ClassKinds
getClassKinds = asks snd


-- |Lookup kind in kindspace
lookupKind :: Name -> Kindchecker (Maybe KindVar)
lookupKind n = M.lookup n . getKindspaceMap <$> getKindspace


-- |Lookup kind in kindspace handling it's absence
kindOf :: Name -> Kindchecker KindVar
kindOf n = lookupKind n >>= \case
  Nothing -> throwError $ "No such type variable: " <> n
  Just k -> pure k


-- |Lookup kind in class kinds
lookupClassKind :: Name -> Kindchecker (Maybe Kind)
lookupClassKind n = M.lookup n . getClassKindsMap <$> getClassKinds


-- |Runs Kindchecker with different typespace
withKindspace :: Kindspace -> Kindchecker a -> Kindchecker a
withKindspace ts = local (\(_, c) -> (ts, c))


-- |Inserts kind binding into kindspace
insertKind :: Name -> KindVar -> Kindspace -> Kindspace
insertKind n k ks = Kindspace $ M.insert n k (getKindspaceMap ks)


-- |Unions two kindspaces
unionKindspaces :: Kindspace -> Kindspace -> Kindspace
unionKindspaces k1 k2 =
  Kindspace $ M.union (getKindspaceMap k1) (getKindspaceMap k2)


-- |SubstituteKindss variables in typespace of given Kindchecker
withKindSubstitution :: KindSubstitution -> Kindchecker a -> Kindchecker a
withKindSubstitution s tc = getKindspace >>= \t -> withKindspace (substituteKinds s t) tc


-- |Thaw `Kind` into `KindVar`
toKindVar :: Kind -> KindVar
toKindVar = \case
  KType -> KindVarType
  KFunc a b -> KindVarFunc (toKindVar a) (toKindVar b)


-- |Returns new type variable
newKindVar :: String -> Kindchecker KindVar
newKindVar prefix = do
  c <- gets tsSupply
  modify $ \s -> s{ tsSupply = c + 1 }
  pure $ KindVar $ KName $ prefix <> show c


-- |Creates substitution with kind assigned
bindKindVar :: KName -> KindVar -> Kindchecker KindSubstitution
bindKindVar n t = case t of
  KindVar v | v == n -> pure mempty
  _ -> if S.member n (freeKinds t)
       then throwError $ "Occur check: Cannot create infinite kind: " <> kstr n <> " := " <> show t
       else pure $ KSubst $ M.singleton n t


-- |Most general unifier
mgu :: KindVar -> KindVar -> Kindchecker KindSubstitution
mgu t1 t2 = case (t1, t2) of
  (KindVarType, KindVarType) -> pure mempty
  (KindVar n, _) -> bindKindVar n t2
  (_, KindVar n) -> bindKindVar n t1
  (KindVarFunc a1 v1, KindVarFunc a2 v2) -> do
    sa <- mgu a1 a2
    sv <- mgu (substituteKinds sa v1) (substituteKinds sa v2)
    pure $ sa <> sv
  _ -> throwError $ "Cannot unify kinds: " <> show t1 <> " vs " <> show t2


-- |Kind inference along with kindcheck. Returns inferred kind and necessary substitutions
inferKind :: RawType -> Kindchecker (KindSubstitution, KindVar)
inferKind = \case
  RawTypeWobbly n -> lookupKind n >>= \case
    Just kr -> pure (mempty, kr)
    Nothing -> fail $ "This should never happen: wobbly variable undefined: " <> n
  RawTypeRigid tr -> lookupKind tr >>= \case
    Just kr -> pure (mempty, kr)
    Nothing -> throwError $ "Undefined variable " <> tr
  RawTypeApp f (a:|rest) -> do
    (sf, kf) <- inferKind f
    let rollapp :: (KindSubstitution, KindVar) -> RawType -> Kindchecker (KindSubstitution, KindVar)
        rollapp (sfun, kfun) arg = do
          kres <- newKindVar "_AP"
          (sa, ka) <- withKindSubstitution sfun $ inferKind arg
          sr <- mgu (substituteKinds sa kfun) (KindVarFunc ka kres)
          pure (sr <> sa <> sfun, substituteKinds sr kres)
    foldM rollapp (sf, kf) (a:rest)
  RawTypeFunc tf ta -> inferKind $
    RawTypeApp (RawTypeRigid "Func") [tf, ta]


-- |Instantiates type and infers its kind. Returns new kind assumptions and inferred kind
inferInstantiated :: RawType -> Kindchecker (Kindspace, KindVar)
inferInstantiated rt = do
  as <- instantiateKinds rt
  (s, k) <- withKindspace as $ inferKind rt
  pure (substituteKinds s as, substituteKinds s k)


-- |Returns assumptions necessary to kindcheck predicate
kindcheckPred :: RawPred -> Kindchecker Kindspace
kindcheckPred pr =
  let cn = rpClass pr
      t = rpType pr
  in lookupClassKind cn >>= \case
    Nothing -> throwError $ "No such class: " <> cn
    Just kc -> do
      (as, kpr) <- inferInstantiated t
      m <- mgu (toKindVar $ kc) kpr
      pure $ substituteKinds m as


-- |Kindchecks qualified type. Returns assumed kindspace and inferred kind
kindcheckQualRawType :: RawQual RawType -> Kindchecker (Kindspace, KindVar)
kindcheckQualRawType rq = do
  ks <- getKindspace
  let folder :: Kindspace -> RawPred -> Kindchecker Kindspace
      folder kss rp = withKindspace kss (kindcheckPred rp)
  predks <- foldM folder ks (rqPreds rq)
  withKindspace predks (inferInstantiated (rqContent rq))


-- |Unifies kind var with Type
finalizeKind :: KindVar -> Kindchecker (KindSubstitution, KindVar)
finalizeKind k = do
  s <- mgu (toKindVar KType) k
  pure (s, substituteKinds s k)


-- |Check if all constructor arguments have proper kind (Type)
kindcheckConstructor :: ConstructorDef -> Kindchecker ()
kindcheckConstructor c = do
  forM_ (condefArgs c) $ \tr -> do
    (_, ktr) <- inferInstantiated tr
    finalizeKind ktr


-- |For every wobbly type not present in kindspace assign kind variable for it
instantiateKinds :: RawType -> Kindchecker Kindspace
instantiateKinds rt = getKindspace >>= \(ks@(Kindspace ksm)) -> case rt of
  RawTypeWobbly n -> case M.lookup n ksm of
    Nothing -> do
      kvar <- newKindVar $ "_Deferred_" <> n
      pure (insertKind n kvar ks)
    Just _ -> pure (ks :: Kindspace)
  RawTypeRigid _ -> pure ks
  RawTypeApp f args -> do
    asf <- instantiateKinds f
    foldM (\a arg -> withKindspace a (instantiateKinds arg)) asf args
  RawTypeFunc tf ta -> instantiateKinds $
    RawTypeApp (RawTypeRigid "Func") [tf, ta]

-- |Checks whether constructors of `newtype` declaration have proper kinds
kindcheckNewType :: NewType -> Kindchecker ()
kindcheckNewType nt = do
  as <- getKindspace
  forM_ (ntContrs nt) $ \tr -> do
    ntks <- foldM (\a (tn, k) -> case M.lookup tn (getKindspaceMap a) of
                      Nothing -> pure $ insertKind tn (toKindVar k) a
                      Just _ -> throwError $ "Duplicated type argument: " <> tn
                  ) as (ntArgs nt)
    withKindspace ntks $ kindcheckConstructor tr


-- |Gets kind by binding
kindlookNewType :: NewType -> Kindchecker Kindspace
kindlookNewType nt =
  pure $ Kindspace $ M.singleton (ntName nt)
    (toKindVar $ foldr KFunc KType (fmap snd $ ntArgs nt))

-- |Kindchecks type declaration
kindcheckRawTypeDecl :: RawTypeDecl -> Kindchecker Kindspace
kindcheckRawTypeDecl td = do
  (ks, k) <- kindcheckQualRawType (rawtdeclType td)
  (ss, _) <- withKindspace ks $ finalizeKind k
  let out = substituteKinds ss ks
  pure out


-- |FreeKindszes `KindVar` into `Kind`. All unresolved variables are assumed to be Type
toKind :: KindVar -> Kindchecker Kind
toKind = \case
  KindVar _ -> pure KType -- TODO: Can one expliot it?
  KindVarType  -> pure KType
  KindVarFunc f a -> liftM2 KFunc (toKind f) (toKind a)


-- |Runs kindchecker with initial kindspace and class kinds
runKindchecker :: Kindspace -> ClassKinds -> Kindchecker a -> Either ErrMsg a
runKindchecker ks cls kc =
  evalState (runReaderT (runExceptT kc) (ks, cls)) (KindcheckerState 0)
