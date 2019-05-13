{-# LANGUAGE ScopedTypeVariables #-}
module Radlang.InterfaceResolve where

import Data.Text as T
import qualified  Data.Map.Strict as M
import Control.Monad.Except
import Control.Monad.Reader

import Radlang.Types
import Radlang.Typedefs
import Radlang.Error
import Radlang.Typesystem.Typesystem


dictName :: Pred -> Text
dictName (IsIn c t) = "@dict_" <> c <> "_" <> getName t


resolveAssgs :: TypedBindings -> ExceptT ErrMsg (Reader Typespace) (Bindings, Typespace)
resolveAssgs tb = do
  ts <- ask
  let newts = fmap fst tb <> ts
  (mapped :: Bindings) <- flip mapM tb $ \((prds :=> _), talts) ->
    flip mapM talts $ \(targs, te) -> do
      tre <- withTypespace newts $ resolve te
      pure (fmap (PVar . dictName) prds ++ targs, tre)
  pure (mapped, newts)


getName :: Type -> Name
getName (TypeVarWobbly (TypeVar n KType)) = n
getName _ = wtf "Non wobbly interface constraint"

makeArgs :: Substitution -> [Pred] -> [Expr]
makeArgs (Subst s) = fmap $ \(IsIn cname tp) ->
  Val $ dictName (IsIn cname $ maybe tp id (M.lookup (getName tp) s))

withTypespace :: Typespace -> ExceptT ErrMsg (Reader Typespace) a -> ExceptT ErrMsg (Reader Typespace) a
withTypespace = local . const

resolve :: TypedExpr -> ExceptT ErrMsg (Reader Typespace) Expr
resolve = \case
  TypedVal (_ :=> tv) v -> asks (M.lookup v) >>= \case
    Just (ps :=> to) -> do
      s <- mgu to tv
      let dictArgs = makeArgs s ps
      pure $ Prelude.foldl Application (Val v) dictArgs
    Nothing -> pure $ Val v
  TypedLit _ l -> pure $ Lit l
  TypedApplication _ f a -> Application <$> resolve f <*> resolve a
  TypedLet _ assgs ine -> do
    (eassgs, ts) <- resolveAssgs assgs
    eine <- withTypespace ts $ resolve ine
    pure $ Let eassgs eine


resolveProgram :: TypedProgram -> ExceptT ErrMsg (Reader Typespace) Program
resolveProgram tp = do
  (bnds, _) <- resolveAssgs (tprgBindings tp)
  pure Program
    { prgBindings = bnds
    , prgDataspace = tprgDataspace tp
    , prgNamespace = tprgNamespace tp
    , prgPolyBindings = tprgPolyBindings tp
    }


ex :: TypedExpr
ex =
  TypedApplication ([IsIn "D" (tWobbly "d1")] :=> (tWobbly "d1"))
  (TypedApplication ([IsIn "D" (tWobbly "d1")] :=> (fun (tWobbly "d1") (tRigid "Int")))
    (TypedVal ([IsIn "D" (tWobbly "d1")] :=> fun (tRigid "Int") (fun (tWobbly "d1") (tRigid "Int"))) "f")
    (TypedLit ([] :=> tRigid "Int") (LitInt 1))
  )
  (TypedVal ([IsIn "D" (tWobbly "d1")] :=> tWobbly "d1") "a")

runResolver :: ExceptT ErrMsg (Reader Typespace) a -> Either ErrMsg a
runResolver = flip runReader M.empty .  runExceptT
