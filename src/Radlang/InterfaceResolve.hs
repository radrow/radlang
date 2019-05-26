{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TemplateHaskell #-}
module Radlang.InterfaceResolve where

import qualified Data.Text as T
import Data.Text(Text)
import qualified  Data.Map.Strict as M
import Control.Monad.Except
import Control.Monad.Reader
import Control.Lens(over, makeLenses)
import Data.List
import qualified Data.Set as S
import Data.Maybe
import Data.Bifunctor
import Data.Functor

import Radlang.Types
import Radlang.Pretty
import Radlang.Typedefs
import Radlang.Error
import Radlang.DependencyAnalysis
import Radlang.Typesystem.Typesystem

import Debug.Trace


data ResolverEnv = ResolverEnv
  { _rsenvTypespace    :: Typespace
  , _rsenvInterfaceEnv :: InterfaceEnv
  , _rsenvPredContext  :: [Pred]
  }
makeLenses ''ResolverEnv
newtype Resolver a = Resolver (ExceptT ErrMsg (Reader ResolverEnv) a)
  deriving (MonadError ErrMsg, MonadReader ResolverEnv, Monad, Applicative, Functor)

getTypespace :: Resolver Typespace
getTypespace = asks _rsenvTypespace
instance HasInterfaceEnv Resolver where getInterfaceEnv = asks _rsenvInterfaceEnv
getPredContext :: Resolver [Pred]
getPredContext = asks _rsenvPredContext

withPreds :: [Pred] -> Resolver a -> Resolver a
withPreds p = local $ over rsenvPredContext (p++)

dictName :: Pred -> Text
dictName (IsIn c t) = "dict_" <> c <> "_" <> getName t


methodDictName :: Pred -> Name -> Name
methodDictName (IsIn c t) n = "@impl_" <> n <> "_for_" <> c <> "_" <> getName t


resolveAssg :: (Qual Type, [TypedAlt]) -> Resolver [([Pattern], EvalExpr)]
resolveAssg ((prds :=> _), talts) = do
  ts <- getTypespace
  flip mapM talts $ \(targs, te) -> do
    let frees = S.unions $ fmap patternFree targs
    withPreds prds $ withTypespace (foldr (\n m -> M.delete n m) ts frees)$ do
      tre <- resolve te
      pure (fmap (PVar . dictName) prds ++ targs, tre)


resolveAssgs :: TypedBindings -> Resolver (Bindings, Typespace)
resolveAssgs tb = do
  ts <- getTypespace
  let newts = fmap fst tb <> ts
  (mapped :: Bindings) <- withTypespace newts $ mapM resolveAssg tb
  pure (mapped, newts)


polyTypespace :: PolyBindings -> Typespace
polyTypespace = fmap (\(_, _, qt, _) -> qt)


resolvePolyBindings :: PolyBindings -> Resolver Bindings
resolvePolyBindings = fmap M.fromList . mapM resolvePolyBinding . M.toList


resolvePolyBinding :: (Name, (Name, (TypeVar, Qual Type), Qual Type, [(Qual Type, [TypedAlt])]))
                   -> Resolver (Name, [([Pattern], EvalExpr)])
resolvePolyBinding (name, (iname, (iarg, _ :=> itype), (ps :=> t), _)) = do
  s <- mgu itype t
  let args = fmap (PVar . dictName) ps
      dtype = substitute s $ TypeVarWobbly iarg
  pure $ (name, [(args, Application (Dict $ dictName $ IsIn iname dtype) (Val name))])


resolveImpls :: PolyBindings -> Resolver (Bindings, DataMap)
resolveImpls pb = let asList = M.toList pb
  in (,) <$> fmap M.unions (mapM implBind asList) <*> (mergeDictMap . join <$> mapM implDict asList)


mergeDictMap :: [(Name, Data)] -> DataMap
mergeDictMap = foldr folder M.empty where
  folder (n, pd@(PolyDict _ sups dm)) prev = case M.lookup n prev of
    Nothing -> M.insert n pd prev
    Just (PolyDict _ _ dm2) -> M.insert n (PolyDict [] sups $ M.union dm dm2) prev
    Just boi -> wtf $ "dict map prev had this boi: " <> T.pack (show boi)
  folder (_, boi) _ = wtf $ "dict map had this boi: " <> T.pack (show boi)


implBind :: (Name, (Name, (TypeVar, Qual Type), Qual Type, [(Qual Type, [TypedAlt])])) -> Resolver Bindings
implBind (n, (iname, (iarg, _ :=> itype), _, mimpls)) = fmap M.fromList $ flip mapM mimpls $ \impl@(_ :=> qt, _) -> do
  rimpl <- resolveAssg impl
  s <- mgu qt itype
  pure (methodDictName (IsIn iname (substitute s (TypeVarWobbly iarg))) n, rimpl)


implDict :: (Name, (Name, (TypeVar, Qual Type), Qual Type, [(Qual Type, [TypedAlt])])) -> Resolver [(Name, Data)]
implDict (n, (iname, (iarg, _ :=> itype), _, mimpls)) = flip mapM mimpls $ \(_ :=> qt, _) -> do
  cl <- getInterfaceEnv
  s <- mgu qt itype
  let dictArg = substitute s $ TypeVarWobbly iarg
      supers = S.toList $ interfaceSuper $ interfaces cl M.! iname
  pure $ (dictName (IsIn iname dictArg)
         , PolyDict [] (fmap (dictName . flip IsIn dictArg) supers)
           $ M.singleton n (methodDictName (IsIn iname dictArg) n)
         )


getName :: Type -> Name
getName (TypeVarWobbly (TypeVar n _)) = n
getName (TypeVarRigid (TypeVar n _)) = n
getName (TypeApp t _) = getName t
getName t = wtf $ "Generic name? " <> T.pack (show t)


solvePreds :: [Pred] -> Resolver [EvalExpr]
solvePreds ps = mapM solvePred ps


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


withTypespace :: Typespace -> Resolver a -> Resolver a
withTypespace ts = local (over rsenvTypespace (const ts))


resolve :: TypedExpr -> Resolver EvalExpr
resolve = \case
  TypedVal (_ :=> tv) v -> getTypespace <&> (M.lookup v) >>= \case
    Just (ps :=> to) -> do
      s <- mgu to tv
      dictArgs <- solvePreds $ substitute s ps
      pure $ Prelude.foldl Application (Val v) dictArgs
    Nothing -> pure $ Val v
  TypedLit _ l -> pure $ Lit l
  TypedApplication _ f a -> Application <$> resolve f <*> resolve a
  TypedLet _ assgs ine -> do
    (eassgs, ts) <- resolveAssgs assgs
    eine <- withTypespace ts $ resolve ine
    pure $ Let eassgs eine


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


runResolver :: Typespace -> InterfaceEnv -> Resolver a -> Either ErrMsg a
runResolver ts ie = flip runReader (ResolverEnv ts ie []) .  runExceptT . (\(Resolver r) -> r)
