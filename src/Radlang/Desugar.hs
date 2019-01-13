{-# LANGUAGE OverloadedLists #-}

module Radlang.Desugar where

import Control.Monad
import Control.Monad.Except
import qualified Data.Map.Strict as M
import Data.List.NonEmpty(cons)

import Radlang.Typesystem.Typesystem
import Radlang.Types
import Radlang.Typedefs
import Radlang.Kindchecker
import Radlang.ClassEnvBuild
import Radlang.DependencyAnalysis


dataspaceInsert :: Data -> Dataspace -> (Dataspace, DataId)
dataspaceInsert d (Dataspace ds next) = (Dataspace (M.insert next d ds) (next+1), next)

constructorBindings :: Type -> ConstructorDef -> (Type, Data)
constructorBindings final c =
  let t = foldr fun final (condefArgs c)
      d = error "constructor def not implemented"
  in (t, d)

newTypeBindings :: Dataspace -> NewType -> (TypeEnv, Namespace, Dataspace)
newTypeBindings dats nt =
  let constrs = fmap (\cd -> let (t,d) = constructorBindings (ntType nt) cd
                               in (condefName cd, quantifyAll ([] :=> t), d))
             $ (ntContrs nt)

      tenv = foldl (\te (n, t, _) -> TypeEnv $ M.insert n t (types te))
        (TypeEnv M.empty) constrs

      (dspace, ids) = foldl (\(ds, prids) (_, _, d) -> let (dds, did) = dataspaceInsert d ds
                                                       in (dds, did:prids)
                            ) (dats, []) constrs
      nspace = foldl (\(Namespace ds) ((n, _, _), i) -> Namespace $ M.insert n i ds)
        (Namespace M.empty) $ zip constrs ids
  in (tenv, nspace, dspace)

classBindings :: ClassDef -> [(Name, Qual Type)]
classBindings cd =
  let clspred = IsIn (classdefName cd) (TypeVarWobbly $ TypeVar (classdefArg cd) (classdefKind cd) )

      methodproc :: TypeDecl -> (Name, Qual Type)
      methodproc td =
        let (prds :=> t) = tdeclType td
        in (tdeclName td, (clspred : prds) :=> t)

  in fmap methodproc (classdefMethods cd)

replaceTypeVar :: Name -> Type -> Qual Type -> Qual Type
replaceTypeVar n repl (prd :=> tp) =
  let newt t = case t of
        TypeVarWobbly (TypeVar nw _) -> if n == nw then repl else t
        TypeVarRigid _ -> t
        TypeApp tf ta -> TypeApp (newt tf) (newt ta)
        TypeGeneric _ -> t
      newprd = fmap (\(IsIn c t) -> IsIn c (newt t)) prd
  in newprd :=> newt tp

implBindings :: ClassDef -> ImplDef -> [Either TypeDecl DataDef]
implBindings cl idef =
  let nameMod :: Name -> Name
      nameMod = (<> show (impldefType idef))

      typeMod :: Qual Type -> Qual Type
      typeMod qt =
        let (iprd :=> itp) = impldefType idef  -- get instance predicates and type
            (rprd :=> rtp) = replaceTypeVar (classdefArg cl) itp qt  -- replace original type with instance
        in ((iprd ++ rprd) :=> rtp)  -- join predicates from typedecl and impl contraints

      tdeclMod :: TypeDecl -> TypeDecl
      tdeclMod td = TypeDecl (nameMod $ tdeclName td) (typeMod $ tdeclType td)

      tdecls = fmap tdeclMod (classdefMethods cl)
      tdefs = fmap (\mt -> mt{datadefName = nameMod $ datadefName mt}) $ impldefMethods idef

  in fmap Left tdecls ++ fmap Right tdefs

processImplDef :: RawImplDef -> Kindchecker ImplDef
processImplDef rid = do
  rq <- processQualType (rawimpldefType rid)
  let mt = fmap processDataDef (rawimpldefMethods rid)
  pure $ ImplDef (rawimpldefClass rid) rq mt


-- |Builds Program from raw AST
buildProgram :: RawProgram -> Either ErrMsg Program
buildProgram prg = runKindchecker stdKindspace (buildClassKinds $ rawprgClassDefs prg) (processProgram prg)


unionBindings :: ExplBindings -> ExplBindings -> ExplBindings
unionBindings e1 e2 =
  let unionIns :: ExplBindings -> Name -> (TypePoly, [Alt]) -> ExplBindings
      unionIns m k v = case M.lookup k m of
        Nothing -> M.insert k v m
        Just (t, alts) -> M.insert k (t, snd v ++ alts) m
  in foldl (\e (n, d) -> unionIns e n d) e1 (M.toList e2)


-- |Kindchecker that builds typesystem and returns well kinded (kind!) program ready for typechecking
-- and evaluation
processProgram :: RawProgram -> Kindchecker Program
processProgram prg = do
  as <- getKindspace
  newAs <- foldM (\a nt -> (unionKindspaces a) <$> kindlookNewType nt) as (rawprgNewTypes prg)

  withKindspace newAs $ do
    forM_ (rawprgNewTypes prg) kindcheckNewType
    forM_ (rawprgImplDefs prg) kindcheckImpl

    tdecls <- do
      forM (rawprgTypeDecls prg) $ \td -> do
        tdas <- kindcheckRawTypeDecl td
        withKindspace (unionKindspaces tdas newAs) $ processTypeDecl td

    cdefs <- traverse processClassDef (rawprgClassDefs prg)
    ceny <- either throwError (pure :: ClassEnv -> Kindchecker ClassEnv)
      (buildClassEnv cdefs [])

    newtypes <- traverse processNewType (rawprgNewTypes prg)

    impldefs <- traverse processImplDef (rawprgImplDefs prg)

    let ddefs = fmap processDataDef (rawprgDataDefs prg)
        (ntTEnv, _, _) =
          let folder (t, n, d) (nt, nn, nd) =
                ( (TypeEnv $ M.union (types t) (types nt))
                , (Namespace $ M.union (namespaceMap n) (namespaceMap nn))
                , (Dataspace (M.union (dataspaceMap d) (dataspaceMap nd)) (max (nextId d) (nextId nd)
                                                                          ))
                )
          in foldl folder (TypeEnv M.empty, Namespace M.empty, Dataspace M.empty 0)
             $ fmap (newTypeBindings (Dataspace M.empty 0)) newtypes

        -- classbnds = foldl (\t1 t2 -> TypeEnv $ M.union (types t1) (types t2))
        --   ntTEnv $ fmap classBindings cdefs
        classdefmap = M.fromList $ fmap (\cd -> (classdefName cd, cd)) cdefs

        imps = (uncurry implBindings . \im -> (classdefmap M.! impldefClass im, im)) =<< impldefs
        cdecls = cdefs >>= \cd -> fmap (uncurry TypeDecl) (classBindings cd)

    pure $ Program
      { prgBindings = toplevelBindings $
                      fmap Left tdecls ++ fmap Right ddefs ++ imps ++ fmap Left cdecls
      , prgClassEnv = ceny
      , prgTypeEnv = ntTEnv
      }


-- |Wraps bunch of type and value bindings into a binding group
toplevelBindings :: [Either TypeDecl DataDef] -> [BindingGroup]
toplevelBindings = pure . groupImplicit . Prelude.foldl ins (M.empty, [M.empty]) where
  groupImplicit :: BindingGroup -> BindingGroup
  groupImplicit (e, is) = (e, groupBindings =<< is)
  ins :: BindingGroup -> Either TypeDecl DataDef -> BindingGroup
  ins (exs, [imps]) tl = case tl of
    Left (TypeDecl n qt) -> case (M.lookup n exs, M.lookup n imps) of
      (Nothing, Nothing) ->
        (M.insert n (quantifyAll qt, []) exs, [imps])
      (Nothing, Just alts) -> let
        e = M.insert n (quantifyAll qt, alts) exs
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


-- |Turns value binding AST into real binding
processDataDef :: RawDataDef -> DataDef
processDataDef dd = DataDef
  { datadefName = rawdatadefName dd
  , datadefArgs = rawdatadefArgs dd
  , datadefVal = processRawExpr $ rawdatadefVal dd
  }


-- |Turns expression AST into Expr
processRawExpr :: RawExpr -> Expr
processRawExpr = \case
  RawExprVal v -> Val v
  RawExprLit l -> Lit l
  RawExprApplication kfun args ->
    Prelude.foldl1 Application (processRawExpr <$> cons kfun args)
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


-- |Extracts kinds of class' arguments
buildClassKinds :: [RawClassDef] -> ClassKinds
buildClassKinds cls = ClassKinds $
  M.fromList $ fmap (\cd -> (rawclassdefName cd, rawclassdefKind cd)) cls


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
  ks <- getKindspace
  kps <- kindcheckPred rp
  t <- withKindspace (unionKindspaces kps ks) $ processType (rpType rp)
  pure $ IsIn (rpClass rp) t


processQualType :: RawQual RawType -> Kindchecker (Qual Type)
processQualType rq = do
  ks <- getKindspace
  (krs, _) <- kindcheckQualType rq
  preds <- traverse processPred (rqPreds rq)
  t <- withKindspace (unionKindspaces krs ks) $ processType (rqContent rq)
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
    , classdefKind = rawclassdefKind rcd
    , classdefSuper = rawclassdefSuper rcd
    , classdefMethods = mts
    }

processNewType :: RawNewType -> Kindchecker NewType
processNewType rnt = do
  myks <- kindlookNewType rnt
  prevKs <- getKindspace
  let ks = foldr (\(n, k) pks -> insertKind n (toKindVar k) pks)
        (unionKindspaces prevKs myks)
        (rawntArgs rnt)
  cs <- withKindspace ks $ traverse processConstrDef (rawntContrs rnt)
  let myKind = foldr KFunc KType (fmap snd $ rawntArgs rnt)
      finalType = foldl TypeApp (TypeVarRigid $ TypeVar (rawntName rnt) myKind)
        $ fmap (\(n, k) -> TypeVarWobbly $ TypeVar n k) (rawntArgs rnt)
  pure $ NewType (rawntName rnt) finalType cs


processConstrDef :: RawConstructorDef -> Kindchecker ConstructorDef
processConstrDef rcd = do
  args <- traverse processType (rawcondefArgs rcd)
  pure $ ConstructorDef (rawcondefName rcd) args
