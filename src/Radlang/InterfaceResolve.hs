{-# LANGUAGE ScopedTypeVariables #-}
module Radlang.InterfaceResolve where

import qualified  Data.Map.Strict as M
import Control.Monad.Except
import Control.Monad.Reader

import Radlang.Types
import Radlang.Typedefs
import Radlang.Error
import Radlang.EvaluationUtils hiding (withTypespace)
import Radlang.Typesystem.Typesystem


matchPatternToType :: Qual Type -> Pattern -> Typespace
matchPatternToType t = \case
  PLit _ -> M.empty
  PVar v -> M.singleton v t
  PWildcard -> M.empty
  PAs a p -> M.insert a t $ matchPatternToType t p
  -- PConstructor _ args ->
  --   let unapply (TypeApp a b) = a : unapply 


reduceType :: Qual Type -> Qual Type
reduceType (ps :=> t) = (filter (\(IsIn _ pt) -> getName pt `elem` fmap (\(TypeVar n _) -> n) (free t)) ps :=> t)


resolveAssgs :: TypedBindings -> ExceptT ErrMsg (Reader Typespace) (BindingGroup, Typespace)
resolveAssgs tb = do
  ts <- ask
  let newts = fmap fst tb <> ts
  (mapped :: ImplBindings) <- flip mapM tb $ \(t, talts) ->
    let unapply (TypeApp (TypeApp _ ta) tv) = ta : unapply tv
        unapply _ = []
        args :: [Qual Type]
        args = fmap (reduceType . (getPreds t :=>)) $ unapply (getQualified t)
    in flip mapM talts $ \(targs, te) -> do
      let argts = foldr (<>) newts (zipWith matchPatternToType args targs)
      tre <- withTypespace argts $ resolve te
      pure (targs, tre)
  pure ((M.empty, M.empty, [mapped]), newts)


getName :: Type -> Name
getName (TypeVarWobbly (TypeVar n KType)) = n
getName _ = wtf "Non wobbly interface constraint"

makeArgs :: Substitution -> [Pred] -> [Expr]
makeArgs (Subst s) = fmap $ \(IsIn cname tp) ->
  Val $ "dict_" <> cname <> "_" <> maybe (getName tp) show (M.lookup (getName tp) s)

withTypespace = local . const

resolve :: TypedExpr -> ExceptT ErrMsg (Reader Typespace) Expr
resolve = \case
  TypedVal (_ :=> tv) v -> do
    (ps :=> to) <- asks (M.lookup v) >>= maybe (wtf $ "No such var " <> v) pure
    s <- mgu to tv
    let dictArgs = makeArgs s ps
    pure $ foldl Application (Val v) dictArgs
  TypedLit _ l -> pure $ Lit l
  TypedApplication _ f a -> Application <$> resolve f <*> resolve a
  TypedLet _ assgs ine -> do
    (eassgs, ts) <- resolveAssgs assgs
    eine <- withTypespace ts $ resolve ine
    pure $ Let eassgs eine

ex :: TypedExpr
ex =
  TypedApplication ([IsIn "D" (tWobbly "d1")] :=> (tWobbly "d1"))
  (TypedApplication ([IsIn "D" (tWobbly "d1")] :=> (fun (tWobbly "d1") (tRigid "Int")))
    (TypedVal ([IsIn "D" (tWobbly "d1")] :=> fun (tRigid "Int") (fun (tWobbly "d1") (tRigid "Int"))) "f")
    (TypedLit ([] :=> tRigid "Int") (LitInt 1))
  )
  (TypedVal ([IsIn "D" (tWobbly "d1")] :=> tWobbly "d1") "a")

runResolver :: Typespace -> ExceptT ErrMsg (Reader Typespace) a -> Either ErrMsg a
runResolver ts = flip runReader ts .  runExceptT
