{-# LANGUAGE ScopedTypeVariables #-}
module Radlang.InterfaceResolve where

import qualified Data.Text as T
import Data.Text(Text)
import qualified  Data.Map.Strict as M
import Control.Monad.Except
import Control.Monad.Reader
import Data.List
import qualified Data.Set as S
import Data.Maybe
import Data.Bifunctor

import Radlang.Types
import Radlang.Pretty
import Radlang.Typedefs
import Radlang.Error
import Radlang.Typesystem.Typesystem


dictName :: Pred -> Text
dictName (IsIn c t) = "@dict_" <> c <> "_" <> getName t

resolveAssg :: (Qual Type, [TypedAlt]) -> Resolver [([Pattern], Expr)]
resolveAssg ((prds :=> _), talts) =
  flip mapM talts $ \(targs, te) -> do
    tre <- resolve te
    pure (fmap (PVar . dictName) prds ++ targs, tre)

resolveAssgs :: TypedBindings -> Resolver (Bindings, Typespace)
resolveAssgs tb = do
  ts <- asks fst
  let newts = fmap fst tb <> ts
  (mapped :: Bindings) <- withTypespace newts $ flip mapM tb $ resolveAssg
  pure (mapped, newts)

resolvePolyBindings :: PolyBindings -> Resolver Bindings
resolvePolyBindings = fmap M.fromList . mapM resolvePolyBinding . M.toList

resolvePolyBinding :: (Name, (Name, Qual Type, [(Qual Type, [TypedAlt])])) -> Resolver (Name, [([Pattern], Expr)])
resolvePolyBinding (name, (iname, (ps :=> t), bimpls)) = do
  let args = fmap (PVar . dictName) ps
  pure $ (name, [(args, Application (Val $ dictName $ IsIn iname t) (Val name))])

resolveImpls :: PolyBindings -> Resolver (Bindings, DataMap)
resolveImpls pb = let asList = M.toList pb in (,) <$> fmap M.unions (mapM implBind asList) <*> fmap M.fromList (mapM implDict asList)

implBind :: (Name, (Name, Qual Type, [(Qual Type, [TypedAlt])])) -> Resolver Bindings
implBind (n, (_, _, impls)) = fmap M.fromList $ flip mapM impls $ \impl@(qt, _) -> do
  rimpl <- resolveAssg impl
  pure (n <> "AAAA" <> T.pack (show qt), rimpl)

implDict :: (Name, (Name, Qual Type, [(Qual Type, [TypedAlt])])) -> Resolver (Name, Data)
implDict (n, _) = pure (n, Strict $ DataPolyDict M.empty)

getName :: Type -> Name
getName (TypeVarWobbly (TypeVar n _)) = n
getName (TypeVarRigid (TypeVar n _)) = n
getName (TypeApp t _) = getName t
getName t = wtf $ "Generic name? " <> T.pack (show t)


type Resolver = ExceptT ErrMsg (Reader (Typespace, InterfaceEnv))


solvePreds :: [Pred] -> Resolver [Expr]
solvePreds = mapM solvePred

{-
class A a where dupa :: a -> a
instance A (Option Int) where dupa :: Option Int -> Option Int

a

s <- mgu (Option Int) a

subst s a
-}

solvePred :: Pred -> Resolver Expr
solvePred p@(IsIn c t) = asks snd >>= \cl ->
  fmap (fromMaybe (Val $ dictName p) . msum) $ flip mapM (fmap (\(prds :=> (IsIn _ pt)) -> prds :=> pt) $ S.toList $ interfaceImpls $ interfaces cl M.! c) $
  \(pr :=> itp) -> flip catchError (const $ pure Nothing) $ do
    s <- generalizeTo t itp
    dicts <- solvePreds $ substitute s pr
    pure $ Just $ foldl' Application (Val $ dictName p) dicts


withTypespace :: Typespace -> Resolver a -> Resolver a
withTypespace ts = local (first (const ts))

resolve :: TypedExpr -> Resolver Expr
resolve = \case
  TypedVal (_ :=> tv) v -> asks (M.lookup v . fst) >>= \case
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
  ibnds <- resolvePolyBindings $ tprgPolyBindings tp
  (bnds, _) <- resolveAssgs (tprgBindings tp `M.union` fmap (\(_, t, _) -> (t, [])) (tprgPolyBindings tp))
  (imps, polyDmap) <- resolveImpls $ tprgPolyBindings tp
  pure Program
    { prgBindings = imps `M.union` ibnds `M.union` bnds
    , prgDataMap = polyDmap `M.union` tprgDataMap tp
    , prgPolyBindings = tprgPolyBindings tp
    }

ci = M.fromList
  [ ("D", [ [] :=> tRigid "Int"
          , [IsIn "D" (tWobbly "~A")] :=> TypeApp (TypeVarRigid $ TypeVar "Option" (KFunc KType KType)) (tWobbly "~A")])
  , ("C", [ [] :=> tRigid "Int"
          , [IsIn "C" (tWobbly "~A")] :=> TypeApp (TypeVarRigid $ TypeVar "Option" (KFunc KType KType)) (tWobbly "~A")])
  , ("W", [[] :=> (TypeVarRigid $ TypeVar "Option" (KFunc KType KType))])
  ]

ex :: TypedExpr
ex =
  TypedApplication ([IsIn "D" (tWobbly "d1")] :=> (tWobbly "d1"))
  (TypedApplication ([IsIn "D" (tWobbly "d1")] :=> (fun (tWobbly "d1") (tRigid "Int")))
    (TypedVal ([IsIn "D" (tWobbly "d1")] :=> fun (tRigid "Int") (fun (tWobbly "d1") (tRigid "Int"))) "f")
    (TypedLit ([] :=> tRigid "Int") (LitInt 1))
  )
  (TypedVal ([IsIn "D" (tWobbly "d1")] :=> tWobbly "d1") "a")

runResolver :: Typespace -> InterfaceEnv -> Resolver a -> Either ErrMsg a
runResolver ts ie = flip runReader (ts, ie) .  runExceptT
