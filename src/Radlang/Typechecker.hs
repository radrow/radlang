-- |Implementation of the W Algorithm for typechecking

module Radlang.Typechecker(typecheck) where

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

-- |Returns typespace
getTypespace :: Typechecker Typespace
getTypespace = ask

-- |Runs Typechecker with another typespace
withTypespace :: Typespace -> Typechecker a -> Typechecker a
withTypespace ts = local (const ts)

-- |Runs Typechecker with additional type assignment
withTypeAssg :: (Name, Type) -> Typechecker a -> Typechecker a
withTypeAssg (n, t) tc = do
  ts <- getTypespace
  let newts = Typespace . (M.insert n (Poly S.empty t)) . getTypespaceMap $ ts
  withTypespace newts tc

-- |Substitutes variables in typespace of given Typechecker
withSubstitution :: Substitution -> Typechecker a -> Typechecker a
withSubstitution s tc = ask >>= \t -> withTypespace (substitute s t) tc

-- |Runs Typecheker with standard library
withStdlib :: Typechecker a -> Typechecker a
withStdlib tc = do
  let ts = Typespace $ M.fromList $ flip fmap stdlib $ \(name, _ ::: typ) -> (name <~ typ)
  withTypespace ts tc

-- |Abstracts out types that are free in t but not in typespace
generalize :: Typespace -> Type -> TypePoly
generalize ts t = Poly vars t where
  vars = free t S.\\ free ts

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
          -- Occur check
       then throwError $ "Cannot create infinite type: " <> n <> " := " <> show t
       else pure $ Subst $ M.singleton n t

-- |Most general unifier
mgu :: Type -> Type -> Typechecker Substitution
mgu t1 t2 = case (t1, t2) of
  (TypeInt, TypeInt) -> pure mempty
  (TypeBool, TypeBool) -> pure mempty
  (TypeVal n, _) -> bindVar n t2
  (_, TypeVal n) -> bindVar n t1
  (TypeValRigid a, TypeValRigid b) ->
    if a == b
    then pure mempty
    else throwError $ "Cannot unify rigid different type variables: " <> a <> " vs " <> b
  (TypeFunc a1 v1, TypeFunc a2 v2) -> do
    sa <- mgu a1 a2
    sv <- mgu (substitute sa v1) (substitute sa v2)
    pure $ sa <> sv
  (TypeValRigid a, b) -> throwError $ "Cannot unify rigid type variable with non-rigid type: " <> a <> " vs " <> show b
  (b, TypeValRigid a) -> throwError $ "Cannot unify rigid type variable with non-rigid type: " <> show b <> " vs " <> a
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
      (\(prevsub, (Typespace prevtsmap)) (name, typeAnn, value) -> do
          -- I need to predict my type to check if recursion typechecks.
          -- This will be substituted by real me
          me <- Poly S.empty <$> newVar ("_L_" <> name)

          -- Typespace that includes type of me
          let withMe = Typespace $ M.insert name me prevtsmap

          -- Get my real type
          (subVal, valueType) <- withTypespace withMe $ inferType value

          -- Substitute my typename with type inferred previously
          let withMeSub@(Typespace withMeSubMap) = substitute subVal withMe

          -- Now search my name in substituted typespace and un-poly
          nameType <- instantiate $ withMeSubMap M.! name

          -- Typecheck me against real me
          subUnify <- mgu nameType valueType

          -- Build output substitution and typespace
          let news = subUnify <> subVal <> prevsub
              newts = substitute subUnify withMeSub

          -- Consider type annotation and generalize
          tvgen <- maybe
                   -- If type is unspecified, leave it polymorphic
                   (pure $ generalize newts valueType)
                   -- Unify types make perform full generalization
                   (\annT -> mgu annT valueType >>
                     pure (generalize (Typespace M.empty) annT)
                   )
                   typeAnn
          pure $ (news, Typespace $ M.insert name tvgen prevtsmap)
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


-- |Evaluation of typechecker
runTypechecker :: Typechecker a -> Either String a
runTypechecker = flip evalState (TypecheckerState 0)
  . flip runReaderT (Typespace M.empty)
  . runExceptT

-- |Toplevel typechecking of expression
typecheck :: Expr -> Either ErrMsg Type
typecheck e = uncurry substitute <$> runTypechecker (withStdlib $ inferType e)
