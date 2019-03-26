-- |This module builds interface environment from raw set of declarations.
--It also ensures that interface hierarchy is valid and not contradict.
{-# LANGUAGE FlexibleContexts #-}
{-#LANGUAGE OverloadedLists#-}

module Radlang.InterfaceEnvBuild where

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
import Radlang.Error
import Radlang.Typesystem.Typesystem


-- |Inserts new interface to env
updateInterfaceEnv :: Name -> Interface -> InterfaceEnvBuilder ()
updateInterfaceEnv n c = modify $ \ce -> ce {interfaces = M.insert n c (interfaces ce)}


-- |Empty interface environment
emptyInterfaceEnv :: InterfaceEnv
emptyInterfaceEnv = InterfaceEnv
  { interfaces = []
  , defaults = [] -- TODO: defaults!
  }


-- |Merge two interface environments
mergeInterfaceEnv :: InterfaceEnv -> InterfaceEnv -> InterfaceEnv
mergeInterfaceEnv c1 c2 = InterfaceEnv
  { interfaces = M.union (interfaces c1) (interfaces c2)
  , defaults = M.union (defaults c1) (defaults c2)
  }


-- |Introduces new interface extending given superinterfaces
addInterface :: Name -> Set Name -> InterfaceEnvBuilder ()
addInterface n sups = do
  nDefined <- interfaceDefined n
  when nDefined (interfaceEnvError $ "Interface already defined: " <> n)
  notDefs <- filterM (\ss -> not <$> interfaceDefined ss) (S.toList sups)
  when (not (null notDefs)) $
    interfaceEnvError $ "Superinterfaces not defined: " <> show notDefs
  updateInterfaceEnv n (Interface sups S.empty)


-- |Declares new impl with qualification
addInst :: [Pred] -> Pred -> InterfaceEnvBuilder ()
addInst ps p@(IsIn i _) = do
  iDefined <- interfaceDefined i
  when (not iDefined) (interfaceEnvError $ "Interface not defined: " <> i)
  its <- impls i
  c <- super i
  let overlaps prd q = catchError (mguPred prd q >> pure True) (const $ pure False)
      qs = S.map (\(_ :=> q) -> q) its
  filterM (overlaps p) (S.toList qs) >>= \case
    [] -> pure ()
    (IsIn h _):_ -> interfaceEnvError $ "Impls overlap: " <> i <> " with " <> h
  updateInterfaceEnv i (Interface c $ S.insert (ps :=> p) its)


-- |Evaluate `InterfaceEnvBuilderT` with initial `InterfaceEnv`
runInterfaceEnvBuilderT :: Monad m
                    => InterfaceEnv
                    -> InterfaceEnvBuilderT m ()
                    -> m (Either ErrMsg InterfaceEnv)
runInterfaceEnvBuilderT ce (InterfaceEnvBuilder cb) = runExceptT $ execStateT cb ce


-- |Evaluation of `InterfaceEnvBuilderT` `Identity`
runInterfaceEnvBuilder :: InterfaceEnv -> InterfaceEnvBuilder () -> Either ErrMsg InterfaceEnv
runInterfaceEnvBuilder ce cb = runIdentity $ runInterfaceEnvBuilderT ce cb


-- |Evaluate action when `Maybe` is a `Just`
onPresent :: MonadError ErrMsg m => Maybe e -> (e -> m ()) -> m ()
onPresent = forM_ -- TODO: Replace with Control.Monad.Extra


-- |Evaluate action when `Maybe` withing the context is a `Just`
onPresentM :: MonadError ErrMsg m => m (Maybe e) -> (e -> m ()) -> m ()
onPresentM cond handle = cond >>= void . traverse handle


-- |Main builder action that builds interface environment from interface definitions and implementations set
buildInterfaceEnv :: [InterfaceDef] -> [ImplDef] -> Either ErrMsg InterfaceEnv
buildInterfaceEnv cses' impls = runInterfaceEnvBuilder (InterfaceEnv stdInterfaces []) $ do
  let cses = interfaceHierarchySort cses'
  let groupOn :: Ord b => (a -> b) -> [a] -> M.Map b [a]
      groupOn f =
        let fld m a = case M.lookup (f a) m of
              Nothing -> M.insert (f a) [a] m
              Just as -> M.insert (f a) (a:as) m
        in foldl fld M.empty

      -- Map from interface name to all of its impls
      instmap = groupOn impldefInterface impls

  onPresent (isCyclic cses) $ \cyc ->
    interfaceEnvError $ "Found interface cycle: " <> show cyc

  -- Build superinterface environment
  forM_ cses $ \(InterfaceDef cname _ _ supers _) -> do
    addInterface cname supers

  -- Add impls
  forM_ cses $ \c -> do
    forM_ (maybe [] id $ M.lookup (interfacedefName c) instmap) $ \i -> do
      onPresentM (checkFoundation i c) $ \m ->
        interfaceEnvError $ "In implementation of " <> show (impldefType i)
        <> ": methods " <> show m
        <> " do not belong to any superinterface of " <> interfacedefName c

      onPresent (checkCompletness c instmap) $ \m ->
        interfaceEnvError $ "Methods " <> show m <> " are missing for " <> interfacedefName c
      let (quals :=> t) = impldefType i
      addInst quals $ IsIn (interfacedefName c) t


-- |Find any cycle in dependency graph
isCyclic :: [InterfaceDef] -> Maybe [NonEmpty Name]
isCyclic = const Nothing -- TODO


-- |Find all methods in impl definition that are not included in interface DAG
checkFoundation :: ( HasInterfaceEnv m
                   , MonadError ErrMsg m)
                => ImplDef -> InterfaceDef -> m (Maybe (NonEmpty Name))
checkFoundation im cd
  = NP.nonEmpty <$> filterM (fmap not . methodInInterface cd) (fmap datadefName $ impldefMethods im)


-- |Check whether given name is valid method of interface DAG
methodInInterface :: HasInterfaceEnv m => InterfaceDef -> Name -> m Bool
methodInInterface c mname =
  let check = any ((==mname) . tdeclName)
  in pure $ check $ interfacedefMethods c  -- TODO: Deep search

-- |Find all missing methods for interface
checkCompletness :: InterfaceDef -> M.Map Name [ImplDef] -> Maybe (NonEmpty Name)
checkCompletness _ _ =
  Nothing -- TODO: Not necessary, but nice to have
