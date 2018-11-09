module Radlang.Typechecker where

import Data.Map.Strict as M
import Data.Set.Monad as S
import Control.Monad.State.Strict
import Control.Monad.Reader
import Control.Monad.Except

import Radlang.Types
import Radlang.Stdlib
import Radlang.Helpers

-- |Lookup type in typespace
lookupType :: Name -> Typechecker (Maybe TypePoly)
lookupType n = M.lookup n . getTypespaceMap <$> getTypespace

getTypespace :: Typechecker Typespace
getTypespace = ask

withTypespace :: Typespace -> Typechecker a -> Typechecker a
withTypespace ts = local (const ts)

withSubstitution :: Substitution -> Typechecker a -> Typechecker a
withSubstitution s tc = ask >>= \t -> withTypespace (substitute s t) tc

-- |Abstracts out types that are free in t but not in typespace
generalize :: Typespace -> Type -> TypePoly
generalize ts t = Poly vars t where
  vars = free t S.\\ free ts

-- |Evaluation of typechecker
runTypechecker :: Typechecker a -> Either String a
runTypechecker = flip evalState (TypecheckerState mempty 0)
  . flip runReaderT (Typespace M.empty)
  . runExceptT

-- |Returns new type variable
newVar :: String -> Typechecker Type
newVar prefix = do
  c <- gets tsSupply
  modify $ \s -> s{ tsSupply = c + 1 }
  pure $ TypeVal $ prefix <> show c

-- |Replace all bound typevars in scheme with fresh typevars
instantiate :: TypePoly -> Typechecker Type
instantiate (Poly vars t) = do
  nvars <- traverse (const newVar "_I") (S.toList vars)
  let newsub = Subst $ M.fromList $ zip (S.toList vars) nvars
  pure $ substitute newsub t

-- |Creates substitution with type assigned
bindVar :: Name -> Type -> Typechecker Substitution
bindVar n t = case t of
  TypeVal v | v == n -> pure mempty
  _ -> if S.member n (free t)
       then throwError $ "Occur check fail: " <> show n <> " vs " <> show t
       else pure $ Subst $ M.singleton n t

-- |Most general unifier
mgu :: Type -> Type -> Typechecker Substitution
mgu t1 t2 = case (t1, t2) of
  (TypeInt, TypeInt) -> pure mempty
  (TypeBool, TypeBool) -> pure mempty
  (TypeVal n, _) -> bindVar n t2
  (_, TypeVal n) -> bindVar n t1
  (TypeFunc a1 v1, TypeFunc a2 v2) -> do
    sa <- mgu a1 a2
    sv <- mgu (substitute sa v1) (substitute sa v2)
    pure $ sa <> sv
  _ -> throwError $ "Cannot unify types: " <> show t1 <> " vs " <> show t2

-- |Type inference along with check
inferType :: Expr -> Typechecker (Substitution, Type)
inferType = \case
  ConstBool _ -> pure (mempty, TypeBool)

  ConstInt _ -> pure (mempty, TypeInt)

  Val e -> lookupType e >>= \case
    Nothing -> throwError $ "Unbound value: " <> e
    Just pt -> instantiate pt >>= \nt -> pure (mempty, nt)

  Application f a -> do
    tvar <- newVar "_A"
    (s1, t1) <- inferType f
    (s2, t2) <- withSubstitution s1 $ inferType a
    s3 <- mgu (substitute s2 t1) (TypeFunc t2 tvar)
    pure $ (s3 <> s2 <> s1, substitute s3 tvar)

  Let assgs e -> do
    ts <- getTypespace
    (newSub, newTypes) <- foldM
      (\(prevsub, prevts@(Typespace prevtsmap)) (name, typeAnn, value) -> do
          (sv, tv) <- withTypespace prevts $ inferType value
          let dropts = Typespace $ M.delete name prevtsmap
          tvgen <- maybe
                   (pure $ generalize dropts tv)
                   (\annT -> mgu annT tv >>
                     pure (generalize (Typespace M.empty) annT)
                   )
                   typeAnn
          pure $ (sv <> prevsub, Typespace $ M.insert name tvgen prevtsmap)
      )
      (mempty, ts)
      assgs
    (se, te) <- withTypespace newTypes $ inferType e
    pure $ (se <> newSub, te)

  Lambda arg expr -> do
    argT <- newVar "_L"
    (Typespace ts) <- getTypespace
    let newTs = Typespace $ M.insert arg (Poly S.empty argT) ts
    (s, exprT) <- withTypespace newTs $ inferType expr
    pure (s, TypeFunc (substitute s argT) exprT)

  If cond th el -> do
    (scond, condT) <- inferType cond
    sbool <- mgu condT TypeBool
    (sth, thT) <- withSubstitution (sbool <> scond) $ inferType th
    (sel, elT) <- withSubstitution (sth <> sbool <> scond) $ inferType el
    sval <- mgu thT elT
    let s = sval <> sel <> sth <> sbool <> scond
    pure (s, substitute s thT)

typecheck :: Expr -> Either ErrMsg Type
typecheck e = uncurry substitute <$> runTypechecker (withStdlib $ inferType e)

withStdlib :: Typechecker a -> Typechecker a
withStdlib tc = do
  let ts = Typespace $ M.fromList $ flip fmap stdlib $ \(name, _ ::: typ) -> (name <~ typ)
  withTypespace ts tc
