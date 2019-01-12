{-# LANGUAGE FlexibleContexts #-}
{-#LANGUAGE OverloadedLists#-}

module Radlang.ClassEnvBuild where

import qualified Data.List.NonEmpty as NP
import Data.List.NonEmpty(NonEmpty)
import Control.Monad.State.Strict
import Control.Monad.Identity
import Control.Monad.Except
import qualified Data.Set as S
import Data.Set(Set)
import qualified Data.Map.Strict as M

import Radlang.Types
import Radlang.Typedefs
import Radlang.DependencyAnalysis
import Radlang.Typesystem.Typesystem


-- |Inserts new class to env
updateClassEnv :: Name -> Class -> ClassEnvBuilder ()
updateClassEnv n c = modify $ \ce -> ce {classes = M.insert n c (classes ce)}


-- |Empty class environment
emptyClassEnv :: ClassEnv
emptyClassEnv = ClassEnv
  { classes = []
  , defaults = [] -- TODO: defaults!
  }

-- |Introduces new class extending given superclasses
addClass :: Name -> Set Name -> ClassEnvBuilder ()
addClass n sups = do
  nDefined <- classDefined n
  when nDefined (throwError $ "Class already defined: " <> n)
  notDefs <- filterM (\ss -> not <$> classDefined ss) (S.toList sups)
  when (not (null notDefs)) $
    throwError $ "Superclasses not defined: " <> show notDefs
  updateClassEnv n (Class sups S.empty)


-- |Declares new instance with qualification
addInst :: [Pred] -> Pred -> ClassEnvBuilder ()
addInst ps p@(IsIn i _) = do
  iDefined <- classDefined i
  when (not iDefined) (throwError $ "Class not defined: " <> i)
  its <- instances i
  c <- super i
  let overlaps prd q = catchError (mguPred prd q >> pure True) (const $ pure False)
      qs = S.map (\(_ :=> q) -> q) its
  filterM (overlaps p) (S.toList qs) >>= \case
    [] -> pure ()
    (IsIn h _):_ -> throwError $ "Instances overlap: " <> i <> " with " <> h
  updateClassEnv i (Class c $ S.insert (ps :=> p) its)


runClassEnvBuilderT :: Monad m
                    => ClassEnv
                    -> ClassEnvBuilderT m ()
                    -> m (Either ErrMsg ClassEnv)
runClassEnvBuilderT ce (ClassEnvBuilder cb) = runExceptT $ execStateT cb ce


runClassEnvBuilder :: ClassEnv -> ClassEnvBuilder () -> Either ErrMsg ClassEnv
runClassEnvBuilder ce cb = runIdentity $ runClassEnvBuilderT ce cb


onPresent :: MonadError ErrMsg m => Maybe e -> (e -> m ()) -> m ()
onPresent = forM_

onPresentM :: MonadError ErrMsg m => m (Maybe e) -> (e -> m ()) -> m ()
onPresentM cond handle = cond >>= void . traverse handle


buildClassEnv :: [ClassDef] -> [RawImplDef] -> Either ErrMsg ClassEnv
buildClassEnv cses' impls = runClassEnvBuilder (ClassEnv stdClasses []) $ do
  let cses = classHierarchySort cses'
  let groupOn :: Ord b => (a -> b) -> [a] -> M.Map b [a]
      groupOn f =
        let fld m a = case M.lookup (f a) m of
              Nothing -> M.insert (f a) [a] m
              Just as -> M.insert (f a) (a:as) m
        in foldl fld M.empty

      -- Map from interface name to all of its instances
      instmap = groupOn rawimpldefClass impls

  onPresent (isCyclic cses) $ \cyc ->
    throwError $ "Found interface cycle: " <> show cyc

  -- Build superclass environment
  forM_ cses $ \(ClassDef cname _ _ supers _) -> do
    addClass cname supers

  -- Add instances
  forM_ cses $ \c -> do
    forM_ (maybe [] id $ M.lookup (classdefName c) instmap) $ \i -> do
      onPresentM (checkFoundation i c) $ \m ->
        throwError $ "In implementation of " <> show (rawimpldefType i)
        <> ": methods " <> show m
        <> " do not belong to any superinterface of " <> classdefName c

      onPresent (checkCompletness c instmap) $ \m ->
        throwError $ "Methods " <> show m <> " are missing for " <> classdefName c
      -- let (RawQual quals t) = impldefType i
      -- addInst quals $ IsIn (classdefName c) t


-- |Find any cycle in dependency graph
isCyclic :: [ClassDef] -> Maybe [NonEmpty Name]
isCyclic = const Nothing -- TODO


-- |Find all methods in instance definition that are not included in interface DAG
checkFoundation :: ( HasClassEnv m
                   , MonadError ErrMsg m)
                => RawImplDef -> ClassDef -> m (Maybe (NonEmpty Name))
checkFoundation im cd
  = NP.nonEmpty <$> filterM (fmap not . methodInClass cd) (fmap rawdatadefName $ rawimpldefMethods im)


-- |Check whether given name is valid method of interface DAG
methodInClass :: HasClassEnv m => ClassDef -> Name -> m Bool
methodInClass c mname =
  let check = any ((==mname) . tdeclName)
  in pure $ check $ classdefMethods c  -- TODO: Deep search

-- |Find all missing methods for interface
checkCompletness :: ClassDef -> M.Map Name [RawImplDef] -> Maybe (NonEmpty Name)
checkCompletness _ _ =
  Nothing -- TODO: Not necessary, but nice to have
