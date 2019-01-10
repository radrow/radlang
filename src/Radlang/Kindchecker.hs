{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedLists #-}

module Radlang.Kindchecker where

import Data.List.NonEmpty
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State.Strict

import Radlang.Parser.Expr
import Radlang.ClassEnvBuild
import Radlang.Types hiding (free, substitute, TypePoly, getSubstMap)
import qualified Radlang.Types as RT
import Radlang.Typesystem.Typesystem hiding (mgu, bindVar)
import Radlang.Types.Kindcheck

-- |Lookup type in typespace
lookupKind :: Name -> Kindchecker (Maybe KindVar)
lookupKind n = M.lookup n . getKindspaceMap <$> getKindspace

kindOf :: Name -> Kindchecker KindVar
kindOf n = lookupKind n >>= \case
  Nothing -> throwError $ "No such type variable: " <> n
  Just k -> pure k

-- |Returns typespace
getKindspace :: Kindchecker Kindspace
getKindspace = asks fst

getClassKinds :: Kindchecker ClassKinds
getClassKinds = asks snd

-- |Runs Kindchecker with another typespace
withKindspace :: Kindspace -> Kindchecker a -> Kindchecker a
withKindspace ts = local (\(_, c) -> (ts, c))
withClassKinds cs = local (\(k, _) -> (k, cs))

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

kindcheckPred :: RawPred -> Kindchecker Kindspace
kindcheckPred pr = getClassKinds >>= \cls ->
  let cn = rpClass pr
      t = rpType pr
  in case lookupClassKind cn cls of
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


kindcheckQualRawType :: RawQual RawType -> Kindchecker (Kindspace, KindVar)
kindcheckQualRawType rq = do
  ks <- getKindspace
  let folder :: Kindspace -> RawPred -> Kindchecker Kindspace
      folder kss rp = withKindspace kss (kindcheckPred rp)
  predks <- foldM folder ks (rqPreds rq)
  withKindspace predks (inferInstantiated (rqContent rq))

testKindchecker :: Kindspace -> Kindchecker a -> Either ErrMsg a
testKindchecker ks kc =
  evalState (runReaderT (runExceptT kc) (ks, ClassKinds M.empty))  (KindcheckerState 0)

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

kindcheckRawTypeDecl :: RawTypeDecl -> Kindchecker Kindspace
kindcheckRawTypeDecl td = do
  (ks, k) <- kindcheckQualRawType (rawtdeclType td)
  (ss, _) <- withKindspace ks $ finalizeKind k
  let out = substitute ss ks
  pure out

buildClassKinds cls = ClassKinds $
  M.fromList $ fmap (\cd -> (rawclassdefName cd, rawclassdefKind cd)) cls

-- kindcheckRawProgram :: RawProgram -> Kindchecker Kindspace
-- kindcheckRawProgram prg = do -- TODO Instances!
--   as <- getKindspace
--   newAs <- foldM (\a nt -> (unionKindspaces a) <$> kindlookNewType nt) as (rawprgNewTypes prg)
--   withKindspace newAs $ do
--     forM_ (rawprgNewTypes prg) kindcheckNewType

--     forM_ (rawprgTypeDecls prg) (kindcheckRawTypeDecl classAssmps)
--   pure newAs


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

processClassDef :: RawClassDef -> Kindchecker ClassDef
processClassDef rcd = do
  mts <- forM (rawclassdefMethods rcd) $ \mt -> do
    tdas <- kindcheckRawTypeDecl mt
    withKindspace tdas $ processTypeDecl mt
  pure $ ClassDef
    { classdefName = rawclassdefName rcd
    , classdefArg = rawclassdefArg rcd
    , classdefSuper = rawclassdefSuper rcd
    , classdefMethods = mts
    }

processProgram :: RawProgram -> Kindchecker Program
processProgram prg = withClassKinds (buildClassKinds $ rawprgClassDefs prg) $ do -- TODO Instances!
  as <- getKindspace
  newAs <- foldM (\a nt -> (unionKindspaces a) <$> kindlookNewType nt) as (rawprgNewTypes prg)

  forM_ (rawprgNewTypes prg) (withKindspace newAs . kindcheckNewType)

  tdecls <- withKindspace newAs $ do
    forM (rawprgTypeDecls prg) $ \td -> do
      tdas <- kindcheckRawTypeDecl td
      withKindspace tdas $ processTypeDecl td

  ceny <- either throwError (pure :: ClassEnv -> Kindchecker ClassEnv) =<<
    (flip buildClassEnv [] <$> traverse processClassDef (rawprgClassDefs prg))

  let ddefs = fmap processDataDef (rawprgDataDefs prg)

  pure $ Program
    { prgBindings = toplevelBindings newAs $ fmap Left tdecls ++ fmap Right ddefs
    , prgClassEnv = ceny
    , prgTypeEnv = TypeEnv $ M.empty
    }



toplevelBindings :: Kindspace -> [Either TypeDecl DataDef] -> [BindingGroup]
toplevelBindings ks = pure . Prelude.foldl ins (M.empty, [M.empty]) where
  ins :: BindingGroup -> Either TypeDecl DataDef -> BindingGroup
  ins (exs, [imps]) tl = case tl of
    Left (TypeDecl n qt) -> case (M.lookup n exs, M.lookup n imps) of
      (Nothing, Nothing) ->
        (M.insert n (quantify (S.toList $ RT.free qt) qt, []) exs, [imps])
      (Nothing, Just alts) -> let
        e = M.insert n (quantify (S.toList $ RT.free qt) qt, alts) exs
        i = M.delete n imps
        in (e, [i])
      (Just _, _) -> error "Typedecl duplicate"
    Right (DataDef n args body) -> case (M.lookup n exs, M.lookup n imps) of
      (Nothing, Nothing) -> let
        i = M.insert n [(args, body)] imps
        in (exs, [i])
      (Just (t, alts), Nothing) -> let
        e = M.insert n (t, (args, body):alts) exs
        in (e, [imps])
      (Nothing, Just alts) -> let
        i = M.insert n ((args, body):alts) imps
        in (exs, [i])
      _ -> error "Impossible happened: binding both explicit and implicit"
  ins _ _ = error "toplevelBindings process error: imps not a singleton"


processDataDef dd = DataDef
  { datadefName = rawdatadefName dd
  , datadefArgs = rawdatadefArgs dd
  , datadefVal = processRawExpr $ rawdatadefVal dd
  }

processRawExpr :: RawExpr -> Expr
processRawExpr = \case
  RawExprVal v -> Val v
  RawExprLit l -> Lit l
  RawExprApplication fun args ->
    foldl1 Application (processRawExpr <$> cons fun args)
  -- RawExprLet assgs inWhat ->
    -- let postassg (name, args, ttype, val) = case args of
    --       [] -> (name, ttype, processRawExpr val)
    --       (h:t) -> (name, ttype, processRawExpr $
    --                  RawExprLambda (h:|t) val
    --                )
    -- in Let (toList $ postassg <$> assgs) (processRawExpr inWhat)
  -- RawExprLambda (a:|rest) val -> case rest of
  --   [] -> Lambda a (processRawExpr val)
  --   h:t -> Lambda a (processRawExpr $ RawExprLambda (h:|t) val)
  _ -> error "RawExpr processing not implemented"
  -- RawExprIf ((c,t):|rest) els -> case rest of
  --   [] -> If (processRawExpr c) (processRawExpr t) (processRawExpr els)
  --   hd:tl -> If
  --     (processRawExpr c)
  --     (processRawExpr t)
  --     (processRawExpr $ RawExprIf (hd:|tl) els)
