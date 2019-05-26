-- |Type erasure utilities. Removes type tags and replaces interfaces with dictionaries.
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TemplateHaskell #-}
module Radlang.InterfaceResolve(resolveProgram) where

import qualified Data.Text as T
import Data.Text(Text)
import qualified  Data.Map.Strict as M
import Control.Monad.Except
import Control.Monad.Reader
import Control.Lens(over, makeLenses, (^.))
import Data.List
import qualified Data.Set as S
import Data.Maybe
import Data.Functor

import Radlang.Types
import Radlang.Error
import Radlang.DependencyAnalysis
import Radlang.Typesystem.Typesystem


-- |Environment of Resolver runtime
data ResolverEnv = ResolverEnv
  { _rsenvTypespace    :: Typespace
  , _rsenvInterfaceEnv :: InterfaceEnv
  , _rsenvPredContext  :: [Pred]
  }
makeLenses ''ResolverEnv

-- |Resolver performs type erasure on typed expression
newtype Resolver a = Resolver (ExceptT ErrMsg (Reader ResolverEnv) a)
  deriving (MonadError ErrMsg, MonadReader ResolverEnv, Monad, Applicative, Functor)

instance HasInterfaceEnv Resolver where getInterfaceEnv = asks (^. rsenvInterfaceEnv)


-- |Get current typespace
getTypespace :: Resolver Typespace
getTypespace = asks _rsenvTypespace


-- |Get current predicate context
getPredContext :: Resolver [Pred]
getPredContext = asks _rsenvPredContext


-- |Run an action with predicate context
withPreds :: [Pred] -> Resolver a -> Resolver a
withPreds p = local $ over rsenvPredContext (p++)


-- |Run an action in given typespace
withTypespace :: Typespace -> Resolver a -> Resolver a
withTypespace ts = local (over rsenvTypespace (const ts))


-- |Return rightmost name of a type
getName :: Type -> Name
getName (TypeVarWobbly (TypeVar n _)) = n
getName (TypeVarRigid (TypeVar n _)) = n
getName (TypeApp t _) = getName t
getName t = wtf $ "Generic name? " <> T.pack (show t)


-- |Generate dictionary name out of predicate
dictName :: Pred -> Text
dictName (IsIn c t) = "dict_" <> c <> "_" <> getName t


-- |Generate method impl name
methodName :: Pred -> Name -> Name
methodName (IsIn c t) n = "@impl_" <> n <> "_for_" <> c <> "_" <> getName t


-- |Resolve single typed assignment
resolveAssg :: (Qual Type, [TypedAlt]) -> Resolver [([Pattern], EvalExpr)]
resolveAssg ((prds :=> _), talts) = do
  ts <- getTypespace
  flip mapM talts $ \(targs, te) -> do
    let frees = S.unions $ fmap patternFree targs
    withPreds prds $ withTypespace (foldr (\n m -> M.delete n m) ts frees)$ do
      tre <- resolveExpr te
      pure (fmap (PVar . dictName) prds ++ targs, tre)


-- |Resolve typed bindings
resolveAssgs :: TypedBindings -> Resolver (Bindings, Typespace)
resolveAssgs tb = do
  ts <- getTypespace
  let newts = fmap fst tb <> ts
  (mapped :: Bindings) <- withTypespace newts $ mapM resolveAssg tb
  pure (mapped, newts)


-- |Extract Typespace from Polyspace
polyTypespace :: PolyBindings -> Typespace
polyTypespace = fmap (\(_, _, qt, _) -> qt)


-- |Resolves single ad-hoc polymorphic binding
resolvePolyBinding :: (Name, (Name, (TypeVar, Qual Type), Qual Type, [(Qual Type, [TypedAlt])]))
                   -> Resolver (Name, [([Pattern], EvalExpr)])
resolvePolyBinding (name, (iname, (iarg, _ :=> itype), (ps :=> t), _)) = do
  s <- mgu itype t
  let args = fmap (PVar . dictName) ps
      dtype = substitute s $ TypeVarWobbly iarg
  pure $ (name, [(args, Application (Dict $ dictName $ IsIn iname dtype) (Val name))])


-- |Resolves ad-hoc polymorphic bindings
resolvePolyBindings :: PolyBindings -> Resolver Bindings
resolvePolyBindings = fmap M.fromList . mapM resolvePolyBinding . M.toList


-- |Resolves method implementations and allocates dictionaries
resolveImpls :: PolyBindings -> Resolver (Bindings, DataMap)
resolveImpls pb = let asList = M.toList pb
  in (,) <$> fmap M.unions (mapM implBind asList) <*> (mergeDictMap . join <$> mapM implDict asList)


-- |Merge two interface dictionaries
mergeDictMap :: [(Name, Data)] -> DataMap
mergeDictMap = foldr folder M.empty where
  folder (n, pd@(PolyDict _ sups dm)) prev = case M.lookup n prev of
    Nothing -> M.insert n pd prev
    Just (PolyDict _ _ dm2) -> M.insert n (PolyDict [] sups $ M.union dm dm2) prev
    Just boi -> wtf $ "dict map prev had this boi: " <> T.pack (show boi)
  folder (_, boi) _ = wtf $ "dict map had this boi: " <> T.pack (show boi)


-- |Resolve bindings of method implementations
implBind :: (Name, (Name, (TypeVar, Qual Type), Qual Type, [(Qual Type, [TypedAlt])])) -> Resolver Bindings
implBind (n, (iname, (iarg, _ :=> itype), _, mimpls)) = fmap M.fromList $ flip mapM mimpls $ \impl@(_ :=> qt, _) -> do
  rimpl <- resolveAssg impl
  s <- mgu qt itype
  pure (methodName (IsIn iname (substitute s (TypeVarWobbly iarg))) n, rimpl)


-- |Creates global interface dictionaries for impls
implDict :: (Name, (Name, (TypeVar, Qual Type), Qual Type, [(Qual Type, [TypedAlt])])) -> Resolver [(Name, Data)]
implDict (n, (iname, (iarg, _ :=> itype), _, mimpls)) = flip mapM mimpls $ \(_ :=> qt, _) -> do
  cl <- getInterfaceEnv
  s <- mgu qt itype
  let dictArg = substitute s $ TypeVarWobbly iarg
      supers = S.toList $ interfaceSuper $ interfaces cl M.! iname
  pure $ (dictName (IsIn iname dictArg)
         , PolyDict [] (fmap (dictName . flip IsIn dictArg) supers)
           $ M.singleton n (methodName (IsIn iname dictArg) n)
         )


-- |Choose which dictionaries from the current context will solve preidcates
solvePreds :: [Pred] -> Resolver [EvalExpr]
solvePreds ps = mapM solvePred ps


-- |Choose which dictionary from the current context will solve given predicate
solvePred :: Pred -> Resolver EvalExpr
solvePred p@(IsIn c t) = do
  cl <- getInterfaceEnv
  ctx <- getPredContext
  let implPreds = (fmap (\(prds :=> (IsIn _ pt)) -> prds :=> pt) $ S.toList $ interfaceImpls $ interfaces cl M.! c)
      tryInst :: Qual Type -> Resolver (Maybe EvalExpr)
      tryInst (pr :=> itp) = flip catchError (const $ pure Nothing) $ do
        s <- generalizeTo t itp
        dicts <- solvePreds $ substitute s pr
        pure $ Just $ foldl' Application (Dict $ dictName p) dicts
  fromImpls <- flip mapM implPreds tryInst
  let tryInterface :: Name -> Resolver Bool
      tryInterface c' =
        if c' == c
        then pure True
        else do
          let supers = S.toList $ interfaceSuper $ interfaces cl M.! c'
          and <$> mapM tryInterface supers
  fromContext <- flip mapM ctx $ \p'@(IsIn c' t') -> flip catchError (const $ pure Nothing) $ do
    void $ generalizeTo t t'
    matches <- tryInterface c'
    pure $ if matches then Just (Dict $ dictName p') else Nothing
  pure $ fromMaybe (wtf $ "Couldn't solve pred (" <> T.pack (show p) <> ") in context " <> T.pack (show ctx)) $
    msum $ fromImpls ++ fromContext


-- |Type erasure on given typed expression
resolveExpr :: TypedExpr -> Resolver EvalExpr
resolveExpr = \case
  TypedVal (_ :=> tv) v -> getTypespace <&> (M.lookup v) >>= \case
    Just (ps :=> to) -> do
      s <- mgu to tv
      dictArgs <- solvePreds $ substitute s ps
      pure $ Prelude.foldl Application (Val v) dictArgs
    Nothing -> pure $ Val v
  TypedLit _ l -> pure $ Lit l
  TypedApplication _ f a -> Application <$> resolveExpr f <*> resolveExpr a
  TypedLet _ assgs ine -> do
    (eassgs, ts) <- resolveAssgs assgs
    eine <- withTypespace ts $ resolveExpr ine
    pure $ Let eassgs eine


-- |Run given Resolver in certain environment
runResolver :: Typespace -> InterfaceEnv -> Resolver a -> Either ErrMsg a
runResolver ts ie = flip runReader (ResolverEnv ts ie []) .  runExceptT . (\(Resolver r) -> r)


-- |Type erasure on whole typed program
resolveProgram :: TypedProgram -> Either ErrMsg Program
resolveProgram tp = runResolver M.empty (tprgInterfaceEnv tp) $ do
  let tsp = polyTypespace (tprgPolyBindings tp)
  (bnds, ts) <- resolveAssgs (tprgBindings tp `M.union` fmap (\(_, _, t, _) -> (t, [])) (tprgPolyBindings tp))
  ibnds <- withTypespace (M.union ts tsp) $ resolvePolyBindings $ tprgPolyBindings tp
  (imps, polyDmap) <- withTypespace (M.union ts tsp) $ resolveImpls $ tprgPolyBindings tp
  pure Program
    { prgBindings = imps `M.union` ibnds `M.union` bnds
    , prgDataMap = polyDmap `M.union` tprgDataMap tp
    , prgPolyBindings = tprgPolyBindings tp
    }
