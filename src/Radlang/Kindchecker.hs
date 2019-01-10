{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedLists #-}

module Radlang.Kindchecker where

import Data.List.NonEmpty
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State.Strict

import Radlang.Types hiding (free, substitute, TypePoly, getSubstMap)

-- |Kindchecker state currently contains only count of runtime generated types
data KindcheckerState = KindcheckerState { tsSupply :: Int}
  deriving (Eq, Show)

-- |Map of typenames into their kinds
newtype Kindspace = Kindspace { getKindspaceMap :: M.Map Name KindVar }
  deriving (Eq, Show, Ord)
-- newtype KindAssumptions = KindAssumptions (M.Map Name Kind)
--   deriving (Show, Eq)
type KindAssumptions = Kindspace


-- |Transformer responsible for typechecking expressions and error handling
type Kindchecker = ExceptT String (ReaderT Kindspace (State KindcheckerState))

newtype KName = KName {kstr :: Name}
  deriving (Eq, Show, Ord)
-- |Primitive type definition
data KindVar
  = KindVar KName
  | KindVarType
  | KindVarFunc KindVar KindVar
  deriving (Eq, Ord)

-- |KindSubstitution of polymorphic types
newtype KindSubstitution = KSubst { getSubstMap :: M.Map KName KindVar }
  deriving (Eq, Show, Ord)

-- |Kinds that may be considered as free types carriers
class Ord t => IsKind t where -- Ord is needed because use of Set
  -- |Free type variables in t
  free :: t -> S.Set KName
  -- |Application of substitution
  substitute :: KindSubstitution -> t -> t


---- INSTANCES ----

instance IsKind t => IsKind (S.Set t) where
  free s = S.unions $ S.map free s
  substitute s = S.map (substitute s)

instance IsKind KindVar where
  free = \case
    KindVar v -> S.singleton v
    KindVarType -> S.empty
    KindVarFunc k1 k2 -> S.union (free k1) (free k2)
  substitute s@(KSubst sm) = \case
    KindVarType -> KindVarType
    KindVarFunc a v -> KindVarFunc (substitute s a) (substitute s v)
    KindVar n -> case M.lookup n sm of
      Just t -> t
      Nothing -> KindVar n

instance IsKind Kindspace where
  free (Kindspace ts) = free $ S.fromList (M.elems ts)
  substitute s (Kindspace ts) = Kindspace $
    M.map (substitute s) ts

instance Semigroup KindSubstitution where
  (<>) s@(KSubst s1) (KSubst s2) =
    KSubst $ M.map (substitute s) s2 `M.union` s1

instance Monoid KindSubstitution where
  mempty = KSubst M.empty


instance Show KindVar where
  show = \case
    KindVar a -> kstr a
    KindVarType -> "Type"
    KindVarFunc a v ->
      let sa = case a of
            KindVarFunc _ _ -> "(" <> show a <> ")"
            _ -> show a
      in sa <> " -> " <> show v


type KindInfer a = a -> Kindchecker KindAssumptions


-- |Lookup type in typespace
lookupKind :: Name -> Kindchecker (Maybe KindVar)
lookupKind n = M.lookup n . getKindspaceMap <$> getKindspace

kindOf :: Name -> Kindchecker KindVar
kindOf n = lookupKind n >>= \case
  Nothing -> throwError $ "No such type variable: " <> n
  Just k -> pure k

-- |Returns typespace
getKindspace :: Kindchecker Kindspace
getKindspace = ask

-- |Runs Kindchecker with another typespace
withKindspace :: Kindspace -> Kindchecker a -> Kindchecker a
withKindspace ts = local (const ts)

insertKind :: Name -> KindVar -> Kindspace -> Kindspace
insertKind n k ks = Kindspace $ M.insert n k (getKindspaceMap ks)
unionKindspaces :: Kindspace -> Kindspace -> Kindspace
unionKindspaces k1 k2 =
  Kindspace $ M.union (getKindspaceMap k1) (getKindspaceMap k2)

-- |Runs Kindchecker with additional type assignment
withKindAssg :: (Name, KindVar) -> Kindchecker a -> Kindchecker a
withKindAssg (n, t) tc = do
  ts <- getKindspace
  let newts = Kindspace . (M.insert n t) . getKindspaceMap $ ts
  withKindspace newts tc

-- |Substitutes variables in typespace of given Kindchecker
withKindSubstitution :: KindSubstitution -> Kindchecker a -> Kindchecker a
withKindSubstitution s tc = getKindspace >>= \t -> withKindspace (substitute s t) tc


-- |Returns new type variable
newVar :: String -> Kindchecker KindVar
newVar prefix = do
  c <- gets tsSupply
  modify $ \s -> s{ tsSupply = c + 1 }
  pure $ KindVar $ KName $ prefix <> show c


-- |Creates substitution with kind assigned
bindVar :: KName -> KindVar -> Kindchecker KindSubstitution
bindVar n t = case t of
  KindVar v | v == n -> pure mempty
  _ -> if S.member n (free t)
          -- Occur check
       then throwError $ "Cannot create infinite kind: " <> kstr n <> " := " <> show t
       else pure $ KSubst $ M.singleton n t

-- |Most general unifier
mgu :: KindVar -> KindVar -> Kindchecker KindSubstitution
mgu t1 t2 = case (t1, t2) of
  (KindVarType, KindVarType) -> pure mempty
  (KindVar n, _) -> bindVar n t2
  (_, KindVar n) -> bindVar n t1
  (KindVarFunc a1 v1, KindVarFunc a2 v2) -> do
    sa <- mgu a1 a2
    sv <- mgu (substitute sa v1) (substitute sa v2)
    pure $ sa <> sv
  _ -> throwError $ "Cannot unify kinds: " <> show t1 <> " vs " <> show t2

toKindVar :: Kind -> KindVar
toKindVar = \case
  KType -> KindVarType
  KFunc a b -> KindVarFunc (toKindVar a) (toKindVar b)

-- |Kind inference along with check
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
          kres <- newVar "_AP"
          (sa, ka) <- withKindSubstitution sfun $ inferKind arg
          sr <- mgu (substitute sa kfun) (KindVarFunc ka kres)
          pure (sr <> sa <> sfun, substitute sr kres)
    foldM rollapp (sf, kf) (a:rest)
  RawTypeFunc tf ta -> inferKind $
    RawTypeApp (RawTypeRigid "Func") [tf, ta]

inferInstantiated :: RawType -> Kindchecker (Kindspace, KindVar)
inferInstantiated rt = do
  as <- instantiateKinds rt
  (s, k) <- withKindspace as $ inferKind rt
  pure (substitute s as, substitute s k)

-- assumeSubst :: KindSubstitution -> Kindchecker a -> Kindchecker a
-- assumeSubst s k = getKindspace >>= \ks ->
--   withKindspace (Kindspace $ M.union (getSubstMap s) (getKindspaceMap ks)) k

kindcheckPred :: M.Map Name Kind -> RawPred -> Kindchecker Kindspace
kindcheckPred cls pr =
  let cn = rpClass pr
      t = rpType pr
  in case M.lookup cn cls of
    Nothing -> throwError $ "No such class: " <> cn
    Just kc -> do
      (as, kpr) <- inferInstantiated t
      m <- mgu (toKindVar $ kc) kpr
      pure $ substitute m as

mergeKinds :: KindVar -> KindVar -> Kindchecker KindVar
mergeKinds k1 k2 = case (k1, k2) of
  (KindVarType, KindVarType) -> pure KindVarType
  (KindVarFunc f1 a1, KindVarFunc f2 a2) ->
    liftM2 KindVarFunc (mergeKinds f1 f2) (mergeKinds a1 a2)
  (KindVar _, k) -> pure k
  (k, KindVar _) -> pure k
  _ -> throwError $ "Cannot merge kinds " <> show k1 <> " and " <> show k2

mergeSubstitutions :: KindSubstitution -> KindSubstitution -> Kindchecker KindSubstitution
mergeSubstitutions s1 s2 = do
  let [lesser, greater] = sortBy (\a b -> compare (M.size a) (M.size b))
        [getSubstMap s1, getSubstMap s2]
      mergeInsert m (k, v) = case M.lookup k m of
        Nothing -> pure $ M.insert k v m
        Just vm -> mergeKinds vm v >>= \kins -> pure (M.insert k kins m)
  KSubst <$> foldM mergeInsert greater (M.toList lesser)

mergeKindspaces :: Kindspace -> Kindspace -> Kindchecker Kindspace
mergeKindspaces k1 k2 = do
  let [lesser, greater] = sortBy (\a b -> compare (M.size a) (M.size b))
        [getKindspaceMap k1, getKindspaceMap k2]
      mergeInsert m (k, v) = case M.lookup k m of
        Nothing -> pure $ M.insert k v m
        Just vm -> mergeKinds vm v >>= \kins -> pure (M.insert k kins m)
  Kindspace <$> foldM mergeInsert greater (M.toList lesser)


kindcheckQualRawType :: M.Map Name Kind -> RawQual RawType -> Kindchecker (Kindspace, KindVar)
kindcheckQualRawType cls rq = do
  ks <- getKindspace
  let folder :: Kindspace -> RawPred -> Kindchecker Kindspace
      folder kss rp = withKindspace kss (kindcheckPred cls rp)
  predks <- foldM folder ks (rqPreds rq)
  withKindspace predks (inferInstantiated (rqContent rq))

testKindchecker :: Kindspace -> Kindchecker a -> Either ErrMsg a
testKindchecker ks kc =
  evalState (runReaderT (runExceptT kc) ks)  (KindcheckerState 0)

finalizeKind :: KindVar -> Kindchecker (KindSubstitution, KindVar)
finalizeKind k = do
  s <- mgu (toKindVar KType) k
  pure (s, substitute s k)

toKind :: KindVar -> Kindchecker Kind
toKind = \case
  KindVar _ -> pure KType -- TODO: Can one expliot it?
  KindVarType  -> pure KType
  KindVarFunc f a -> liftM2 KFunc (toKind f) (toKind a)

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
      kvar <- newVar $ "_Deferred_" <> n
      pure (insertKind n kvar ks)
    Just _ -> pure (ks :: Kindspace)
  RawTypeRigid _ -> pure ks
  RawTypeApp f args -> do
    asf <- instantiateKinds f
    foldM (\a arg -> withKindspace a (instantiateKinds arg)) asf args
  RawTypeFunc tf ta -> instantiateKinds $
    RawTypeApp (RawTypeRigid "Func") [tf, ta]

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

kindcheckRawTypeDecl :: M.Map Name Kind -> RawTypeDecl -> Kindchecker Kindspace
kindcheckRawTypeDecl cls td = do
  (ks, k) <- kindcheckQualRawType cls (rawtdeclType td)
  (ss, _) <- withKindspace ks $ finalizeKind k
  let out = substitute ss ks
  pure out

kindcheckRawProgram :: KindInfer RawProgram
kindcheckRawProgram prg = do -- TODO Instances!
  as <- getKindspace
  newAs <- foldM (\a nt -> (unionKindspaces a) <$> kindlookNewType nt) as (rawprgNewTypes prg)
  withKindspace newAs $ do
    forM_ (rawprgNewTypes prg) kindcheckNewType

    let classAssmps = M.fromList $ fmap (\cd -> (classdefName cd, classdefKind cd)) (rawprgClassDefs prg)
    forM_ (rawprgTypeDecls prg) (kindcheckRawTypeDecl classAssmps)
  pure newAs


processType :: RawType -> Kindchecker Type
processType = \case
  RawTypeWobbly n -> TypeVarWobbly . TypeVar n <$> (toKind =<< kindOf n)
  RawTypeRigid n -> TypeVarRigid . TypeVar n <$> (toKind =<< kindOf n)
  RawTypeApp f args -> do
    ft <- processType f
    as <- forM args processType
    foldM (\ff aa -> pure $ TypeApp ff aa) ft as
  RawTypeFunc tf ta -> processType $ RawTypeApp (RawTypeRigid "Func") [tf, ta]

processPred :: RawPred -> Kindchecker Pred
processPred rp = do
  t <- processType (rpType rp)
  pure $ IsIn (rpClass rp) t

processQualType :: RawQual RawType -> Kindchecker (Qual Type)
processQualType rq = do
  preds <- traverse processPred (rqPreds rq)
  t <- processType (rqContent rq)
  pure $ preds :=> t


processTypeDecl :: RawTypeDecl -> Kindchecker TypeDecl
processTypeDecl rtd = TypeDecl (rawtdeclName rtd) <$> processQualType (rawtdeclType rtd)


processProgram :: RawProgram -> Kindchecker Program
processProgram prg = do -- TODO Instances!
  as <- getKindspace
  newAs <- foldM (\a nt -> (unionKindspaces a) <$> kindlookNewType nt) as (rawprgNewTypes prg)

  forM_ (rawprgNewTypes prg) (withKindspace newAs . kindcheckNewType)

  tdecls <- withKindspace newAs $ do

    let classAssmps =
          M.fromList $ fmap (\cd -> (classdefName cd, classdefKind cd)) (rawprgClassDefs prg)
    forM (rawprgTypeDecls prg) $ \td -> do
      tdas <- kindcheckRawTypeDecl classAssmps td
      withKindspace tdas $ processTypeDecl td
  throwError $ show tdecls

-- processProgram rp = do
--   ce <- buildClassEnv classdefs impldefs
--   pure $ Program
--     { prgBindings = toplevelBindings $ fmap Left typedecls ++ fmap Right datadefs
--     , prgTypespace = undefined
--     , prgClassEnv = ce
--     , prgTypeEnv = undefined
--     }

