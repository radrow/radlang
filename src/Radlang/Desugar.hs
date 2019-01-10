{-# LANGUAGE OverloadedLists #-}

module Radlang.Desugar where

import Control.Monad
import Control.Monad.Except
import Data.Map.Strict as M
import Data.Set as S
import Data.List.NonEmpty

import Radlang.Typesystem.Typesystem
import Radlang.Types
import Radlang.Kindchecker
import Radlang.ClassEnvBuild
import Radlang.DependencyAnalysis


-- |Builds Program from raw AST
buildProgram :: RawProgram -> Either ErrMsg Program
buildProgram prg = runKindchecker (Kindspace M.empty) (buildClassKinds $ rawprgClassDefs prg) (processProgram prg)


-- |Kindchecker that builds typesystem and returns well kinded (kind!) program ready for typechecking
-- and evaluation
processProgram :: RawProgram -> Kindchecker Program
processProgram prg = do -- TODO Instances!
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
    { prgBindings = toplevelBindings $ fmap Left tdecls ++ fmap Right ddefs
    , prgClassEnv = ceny
    , prgTypeEnv = TypeEnv $ M.empty
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
        (M.insert n (quantify (S.toList $ free qt) qt, []) exs, [imps])
      (Nothing, Just alts) -> let
        e = M.insert n (quantify (S.toList $ free qt) qt, alts) exs
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
