-- |tl;dr this module turns "raw" things into "just" things.
--
--Here are all utils related to kindcheck applying and desugaring work.
--This module builds ready to typecheck program from raw collection of
--definitions and declarations.
module Radlang.Desugar where

import           Data.List(groupBy, sortBy)
import           Control.Monad
import           Control.Monad.Except
import           Data.Bitraversable
import           Data.List.NonEmpty            (NonEmpty ((:|)), cons, toList)
import qualified Data.Map.Strict               as M
import qualified Data.Set                      as S

import           Radlang.InterfaceEnvBuild
import           Radlang.DependencyAnalysis
import           Radlang.Error
import           Radlang.Kindchecker
import           Radlang.Typedefs
import           Radlang.Types
import           Radlang.Typesystem.Typesystem

import Debug.Trace

-- |Innsert element into dataspace and increment the counter
dataspaceInsert :: Data -> EvaluationState -> EvaluationState
dataspaceInsert d (EvaluationState ds next) = (EvaluationState (M.insert next d ds) (next+1))


-- |Generate bindings from constructor definition
constructorBindings :: Type -> ConstructorDef -> (Type, Data)
constructorBindings final c =
  let t = foldr fun final (condefArgs c)
      d = buildC [] (condefArgs c)

      buildC :: [Data] -> [Type] -> StrictData
      buildC acc [] = DataADT (condefName c) $ reverse acc
      buildC acc (_:rest) = DataFunc (condefName c <> "#" <>
                                       show (length (condefArgs c) - length rest)) $
                             \arg -> pure $ Strict $ buildC (arg:acc) rest
  in (t, Strict d)


-- |Extracts informations about its constructors
newtypeConstructorsBindings :: NewType
                            -> [(Name, Qual Type, Data)]
newtypeConstructorsBindings nt = fmap (\cd -> let (t,d) = constructorBindings (ntType nt) cd
                                              in (condefName cd, ([] :=> t), d))
                                 $ (ntContrs nt)


-- |Generate bindings from newtypes definition
newtypeTypeEnv :: [NewType] -> TypeEnv
newtypeTypeEnv nts =
  let constrs = foldr (\nt prev -> newtypeConstructorsBindings nt ++ prev) [] nts
      tdecls = fmap (\(n, t, _) -> (n, quantifyAll t)) constrs
  in TypeEnv $ M.fromList tdecls


-- |Get contructors as data with assigned names
newtypeData :: [NewType] -> M.Map Name Data
newtypeData nts =
  let constrs = foldr (\nt prev -> newtypeConstructorsBindings nt ++ prev) [] nts
  in M.fromList $ fmap (\(n, _, d) -> (n, d)) constrs


-- |Extract type declarations from interface definition
interfaceBindings :: InterfaceDef -> BindingGroup
interfaceBindings cd =
  let clspred = IsIn (interfacedefName cd) (TypeVarWobbly $ TypeVar (interfacedefArg cd) (interfacedefKind cd) )

      methodproc :: TypeDecl -> (Name, Qual Type)
      methodproc td =
        let (prds :=> t) = tdeclType td
        in (tdeclName td, (clspred : prds) :=> t)

      bnds = M.fromList $ fmap ((\(n, qt) -> (n, (quantifyAll qt, []))) . methodproc) (interfacedefMethods cd)
  in (bnds, M.empty, [])


-- |Substitute all name occurences by certain type in a qualified type
replaceTypeVar :: Name -> Type -> Qual Type -> Qual Type
replaceTypeVar n repl (prd :=> tp) =
  let newt t = case t of
        TypeVarWobbly (TypeVar nw _) -> if n == nw then repl else t
        TypeVarRigid _               -> t
        TypeApp tf ta                -> TypeApp (newt tf) (newt ta)
        TypeGeneric _                -> t
      newprd = fmap (\(IsIn c t) -> IsIn c (newt t)) prd
  in newprd :=> newt tp


-- |Extract bindings from impl definition
implBindings :: InterfaceDef -> ImplDef -> BindingGroup
implBindings cl idef = -- Strategy: write once, forget what the fuck is going on here and never go back
  let typeMod :: Qual Type -> Qual Type
      typeMod qt =
        let (iprd :=> itp) = impldefType idef  -- get instance predicates and type
            (rprd :=> rtp) = replaceTypeVar (interfacedefArg cl) itp qt  -- replace original type with instance
        in ((iprd ++ rprd) :=> rtp)  -- join predicates from typedecl and impl contraints

      typeByName :: Name -> Qual Type
      typeByName n =
        maybe (wtf "implbindings lookup fail") id
        $ lookup n (fmap (\mt -> (tdeclName mt, tdeclType mt)) $ interfacedefMethods cl)

      bnds :: InterfaceBindings
      bnds = M.fromList
        $ fmap (\(n, l) ->
                  (n
                  , ( quantifyAll $ typeByName n
                    , [( quantifyAll $ typeMod $ typeByName n
                       , fmap (\dd -> (datadefArgs dd, datadefVal dd)) l)
                      ])))
        $ fmap (\l -> (fst $ head l, fmap snd l)) -- extract names, ie. [[(Name, Defs)]] -> [(Name, [Defs])]
        $ groupBy ((.fst) . (==) . fst) -- group by names
        $ sortBy ((.fst) . compare . fst) -- sort by names
        $ fmap (\dd -> (datadefName dd, dd)) -- expose names
        $ impldefMethods idef -- get method definitions

  in (bnds, M.empty, [])


-- |Kindcheck and desugar impl definition
processImplDef :: RawImplDef -> Kindchecker ImplDef
processImplDef rid = do
  rq <- processQualType (rawimpldefType rid)
  mt <- traverse processDataDef (rawimpldefMethods rid)
  pure $ ImplDef (rawimpldefInterface rid) rq mt


-- |Builds Program from raw AST
buildProgram :: RawProgram -> Either ErrMsg Program
buildProgram prg =
  runKindchecker stdKindspace (buildInterfaceKinds $ rawprgInterfaceDefs prg) (processProgram prg)


-- |Merge two explicit binding sets
unionExplBindings :: ExplBindings -> ExplBindings -> ExplBindings
unionExplBindings e1 e2 =
  let unionIns :: ExplBindings -> Name -> (TypePoly, [Alt]) -> ExplBindings
      unionIns m k v = case M.lookup k m of
        Nothing        -> M.insert k v m
        Just (t, alts) -> M.insert k (t, snd v ++ alts) m
  in foldr (\(n, d) e -> unionIns e n d) e1 (M.toList e2)


-- |Merge two interface binding sets
unionInterBindings :: InterfaceBindings -> InterfaceBindings -> InterfaceBindings
unionInterBindings i1 i2 =
  let unionIns :: InterfaceBindings -> Name -> (TypePoly, [(TypePoly, [Alt])]) -> InterfaceBindings
      unionIns m k v = case M.lookup k m of
        Nothing        -> M.insert k v m
        Just (t, altss) -> M.insert k (t, snd v ++ altss) m
  in foldr (\(n, d) e -> unionIns e n d) i1 (M.toList i2)


-- |Merge two binding groups
unionBindingGroups :: BindingGroup -> BindingGroup -> BindingGroup
unionBindingGroups (i1, e1, is1) (i2, e2, is2) = (unionInterBindings i1 i2, unionExplBindings e1 e2, is1 ++ is2)


-- |Ensure that no variable occurs twice in pattern set
checkUniquePatternVars :: [Pattern] -> Kindchecker ()
checkUniquePatternVars ps = do
  let checkedInsert :: Name -> S.Set Name -> Kindchecker (S.Set Name)
      checkedInsert n s = if S.member n s
        then typecheckError $ "Pattern var overlap: " <> n
        else pure (S.insert n s)
      checkedUnion :: S.Set Name -> S.Set Name -> Kindchecker (S.Set Name)
      checkedUnion s1 s2 = if not (S.null $ S.intersection s1 s2)
        then typecheckError $ "Pattern vars overlap: " <> show (S.intersection s1 s2)
        else pure (S.union s1 s2)
      checkPattern = \case
        PLit _ -> pure S.empty
        PVar n -> pure $ S.singleton n
        PAs n pat -> checkedInsert n =<< checkPattern pat
        PWildcard -> pure S.empty
        PConstructor _ args -> checkPatterns args
      checkPatterns :: [Pattern] -> Kindchecker (S.Set Name)
      checkPatterns p = foldM folder S.empty p where
        folder ns pt = checkPattern pt >>= checkedUnion ns
  void $ checkPatterns ps


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
    ddefs <- traverse processDataDef (rawprgDataDefs prg)
    intdefs <- traverse processInterfaceDef (rawprgInterfaceDefs prg)
    newtypes <- traverse processNewType (rawprgNewTypes prg)
    impldefs <- traverse processImplDef (rawprgImplDefs prg)

    intenv <- either throwError (pure :: InterfaceEnv -> Kindchecker InterfaceEnv)
      (buildInterfaceEnv intdefs impldefs)

    let interfacedefmap = M.fromList $ fmap (\cd -> (interfacedefName cd, cd)) intdefs
        impbnds = foldr unionBindingGroups (M.empty, M.empty, []) [uncurry implBindings $ (interfacedefmap M.! impldefInterface im, im) | im <- impldefs]

        intbnds = foldr unionBindingGroups (M.empty, M.empty, []) [interfaceBindings i | i <- intdefs]

        topbnds = makeBindings $ fmap Left tdecls ++ fmap Right ddefs

        allbnds = foldr unionBindingGroups (M.empty, M.empty, []) [impbnds, intbnds, topbnds]

    pure $ Program
      { prgDatamap = newtypeData newtypes
      , prgBindings = [allbnds]
      , prgInterfaceEnv = intenv
      , prgTypeEnv = newtypeTypeEnv newtypes
      }


-- |Wraps bunch of type and value bindings into a binding group
makeBindings :: [Either TypeDecl DataDef] -> BindingGroup
makeBindings = groupImplicit . Prelude.foldl ins (M.empty, M.empty, [M.empty]) where
  groupImplicit :: BindingGroup -> BindingGroup
  groupImplicit (int, e, is) = (int, e, groupBindings =<< is)
  ins :: BindingGroup -> Either TypeDecl DataDef -> BindingGroup
  ins (int, exs, [imps]) tl = case tl of
    Left (TypeDecl n qt) -> case (M.lookup n exs, M.lookup n imps) of
      (Nothing, Nothing) ->
        (int, M.insert n (quantifyAll qt, []) exs, [imps])
      (Nothing, Just alts) -> let
        e = M.insert n (quantifyAll qt, alts) exs
        i = M.delete n imps
        in (int, e, [i])
      (Just _, _) -> error $ "Typedecl duplicate: " <> n -- FIXME THROWERROR
    Right (DataDef n args body) -> case (M.lookup n exs, M.lookup n imps) of
      (Nothing, Nothing) -> let
        i = M.insert n [(args, body)] imps
        in (int, exs, [i])
      (Just (t, alts), Nothing) -> let
        e = M.insert n (t, (args, body):alts) exs
        in (int, e, [imps])
      (Nothing, Just alts) -> let
        i = M.insert n ((args, body):alts) imps
        in (int, exs, [i])
      _ -> wtf "Impossible happened: binding both explicit and implicit"
  ins _ _ = wtf "toplevelBindings process error: imps not a singleton"


-- |Turns value binding AST into real binding
processDataDef :: RawDataDef -> Kindchecker DataDef
processDataDef dd = do
  checkUniquePatternVars (rawdatadefArgs dd)
  processRawExpr (rawdatadefVal dd) >>= \d -> pure DataDef
    { datadefName = rawdatadefName dd
    , datadefArgs = rawdatadefArgs dd
    , datadefVal = d
    }


-- |Turns expression AST into Expr
processRawExpr :: RawExpr -> Kindchecker Expr
processRawExpr = \case
  RawExprVal v -> pure $ Val v
  RawExprLit l -> pure $ Lit l
  RawExprApplication kfun args -> do
    sq <- traverse processRawExpr $ cons kfun args
    pure $ Prelude.foldl1 Application sq
  RawExprLet assgs inWhat -> do
    passgs <- traverse (bitraverse processTypeDecl processDataDef) assgs
    let bnds = makeBindings (toList passgs)
    ex <- processRawExpr inWhat
    pure $ Let bnds ex
  RawExprLambda (a:|rest) val -> processRawExpr $
    RawExprLet (Right (RawDataDef "_lambda" (a:rest) val) :|[]) (RawExprVal "_lambda")
  RawExprIf ((c,t):|rest) els -> case rest of
    [] -> processRawExpr $ RawExprApplication (RawExprVal "if") (c:|[t,els])
    hd:tl -> processRawExpr $ RawExprApplication (RawExprVal "if")
      (c :|[t, RawExprIf (hd:|tl) els])
  RawExprCase cased matches -> processRawExpr $
    let defs = fmap (\(p, e) -> Right $ RawDataDef "_case" [p] e) matches
    in RawExprLet defs $ RawExprApplication (RawExprVal "_case") (cased:|[])
  RawExprFor (h:t) e -> case h of
    ForVal v -> do
      let cont = RawExprLambda (PWildcard:|[]) (RawExprFor t e)
      processRawExpr $ RawExprApplication (RawExprVal "bind") (v:|[cont])
    ForBind n v -> do
      let cont = RawExprLambda (PVar n:|[]) (RawExprFor t e)
      processRawExpr $ RawExprApplication (RawExprVal "bind") (v:|[cont])
  RawExprFor [] e -> processRawExpr e
  RawExprList [] -> pure $ Val "Nil"
  RawExprList (h:t) ->
      processRawExpr $ RawExprApplication (RawExprVal "Cons") (h:|[RawExprList t])



-- |Extracts kinds of interface' arguments
buildInterfaceKinds :: [RawInterfaceDef] -> InterfaceKinds
buildInterfaceKinds cls = InterfaceKinds $
  M.fromList $ fmap (\cd -> (rawinterfacedefName cd, rawinterfacedefKind cd)) cls


-- |Kindcheck and process raw type
processType :: RawType -> Kindchecker Type
processType = \case
  RawTypeWobbly n -> TypeVarWobbly . TypeVar n <$> (toKind =<< kindOf n)
  RawTypeRigid n -> TypeVarRigid . TypeVar n <$> (toKind =<< kindOf n)
  RawTypeApp f args -> do
    ft <- processType f
    as <- forM args processType
    foldM (\ff aa -> pure $ TypeApp ff aa) ft as
  RawTypeFunc tf ta -> processType $ RawTypeApp (RawTypeRigid "Func") (tf:|[ta])


-- |Kindcheck and process raw predicate
processPred :: RawPred -> Kindchecker Pred
processPred rp = do
  ks <- getKindspace
  kps <- kindcheckPred rp
  t <- withKindspace (unionKindspaces kps ks) $ processType (rpType rp)
  pure $ IsIn (rpInterface rp) t


-- |Kindcheck and process raw qualified type
processQualType :: RawQual RawType -> Kindchecker (Qual Type)
processQualType rq = do
  ks <- getKindspace
  (krs, _) <- kindcheckQualType rq
  preds <- traverse processPred (rqPreds rq)
  t <- withKindspace (unionKindspaces krs ks) $ processType (rqContent rq)
  pure $ preds :=> t


-- |Kindcheck and process raw type declaration
processTypeDecl :: RawTypeDecl -> Kindchecker TypeDecl
processTypeDecl rtd = TypeDecl (rawtdeclName rtd) <$> processQualType (rawtdeclType rtd)


-- |Kindcheck and process raw interface definition
processInterfaceDef :: RawInterfaceDef -> Kindchecker InterfaceDef
processInterfaceDef rcd = do
  mts <- forM (rawinterfacedefMethods rcd) $ \mt -> do
    tdas <- kindcheckRawTypeDecl mt
    withKindspace tdas $ processTypeDecl mt
  pure $ InterfaceDef
    { interfacedefName = rawinterfacedefName rcd
    , interfacedefArg = rawinterfacedefArg rcd
    , interfacedefKind = rawinterfacedefKind rcd
    , interfacedefSuper = rawinterfacedefSuper rcd
    , interfacedefMethods = mts
    }


-- |Kindcheck and process raw newtype definition
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


-- |Kindcheck and process constructor definition
processConstrDef :: RawConstructorDef -> Kindchecker ConstructorDef
processConstrDef rcd = do
  args <- traverse processType (rawcondefArgs rcd)
  pure $ ConstructorDef (rawcondefName rcd) args
