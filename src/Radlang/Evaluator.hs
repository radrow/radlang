module Radlang.Evaluator where

import Data.Traversable
import Control.Applicative
import Control.Monad.State.Strict
import Control.Monad.Reader
import Control.Monad.Except
import Prelude hiding (lookup)
import qualified Data.Map.Strict as M

import Radlang.Types

getNamespace :: Evaluator Namespace
getNamespace = lift ask

getDataspace :: Evaluator Dataspace
getDataspace = lift $ lift get

setDataspace :: Dataspace -> Evaluator ()
setDataspace d = lift $ lift $ put d

inserts :: [(Name, Int)] -> Namespace -> Namespace
inserts as ns = foldl (flip $ uncurry M.insert) ns as

update :: Namespace -> Namespace -> Namespace
update = M.union

-- registerConstructor :: String -> Int -> Namespace -> Namespace
-- registerConstructor name arity ns =
--   M.insert name (cons arity) ns where
--   cons 0 = DataADT name []
--   cons n = let (DataADT _ l) = cons (n-1)
--                argname = uniqueName $ name <> show n
--            in DataLambda ns argname (Data $ DataADT name (Val argname : l))

-- |Try to get data by name
lookupName :: Name -> Evaluator (Maybe DataEntry)
lookupName n = do
  ns <- getNamespace
  ds <- fst <$> getDataspace
  case M.lookup n ns of
    Just i -> case M.lookup i ds of
      Just d -> pure $ Just d
      Nothing -> throwError $ "Unbound id: " <> show i
    Nothing -> pure Nothing

force :: DataEntry -> Evaluator Data
force (Strict d) = pure d
force (Lazy ns e) = withNsExpr ns e

lookupNameForce :: Name -> ExceptT String (ReaderT Namespace (State Dataspace)) (Maybe Data)
lookupNameForce n = lookupName n >>= (traverse force)

-- |Allocates new data and returns id
registerData :: DataEntry -> Evaluator DataId
registerData d = do
  (ds, count) <- getDataspace
  put $ (M.insert (count + 1) d ds, count + 1)
  pure $ count + 1

(<~) :: a -> b -> (a, b)
(<~) = (,)

-- |Evals with overbound variable id
withAssg :: (Name, Int) -> Evaluator Data -> Evaluator Data
withAssg (n, d) = local (M.insert n d)

-- |Same as `withAssg`, but evaluation performed
withAssgExpr :: (Name, Int) -> Expr -> Evaluator Data
withAssgExpr a e = withAssg a (eval e)

-- |Evals with data bound to name
withData :: (Name, DataEntry) -> Evaluator Data -> Evaluator Data
withData (n, d) e = registerData d >>= \i -> withAssg (n <~ i) e

-- |Same as `withData`, but evaluation performed
withDataExpr :: (Name, DataEntry) -> Expr -> Evaluator Data
withDataExpr a e = withData a (eval e)

-- |Evals with updated namespace
withNs :: Namespace -> Evaluator Data -> Evaluator Data
withNs n = local (update n)

-- |Same as `withNs`, but evaluation performed
withNsExpr :: Namespace -> Expr -> ExceptT String (ReaderT Namespace (State Dataspace)) Data
withNsExpr n e = local (update n) (eval e)


eval :: Expr -> Evaluator Data
eval expr =
  case expr of
    Val a -> lookupNameForce a >>= \case
      Just x -> pure x
      Nothing -> throwError $ "Unbound value: " <> a
    Data d -> pure d
    Application f arg ->
      eval f >>= \case
        DataLambda ns argname e -> do
          withData (argname <~ Lazy ns arg) $ withNsExpr ns e
        _ -> throwError "Function application not into lambda"
    Let assgs e -> do
      ns <- getNamespace
      (_, count) <- getDataspace
      let newns = Prelude.foldl (\m ((name, _, _), i) ->
                            M.insert name i m
                         ) ns (zip assgs [count + 1..])
      forM_ assgs $ \(_, _, ee) -> registerData (Lazy newns ee)
      withNsExpr ns e

    Lambda name e -> (\ns -> DataLambda ns name e) <$> ask

    Case ecased cases -> do
      let cas = msum . flip fmap cases
      cased <- eval ecased
      namespace <- ask
      newe <- pure $ case cased of
        DataInt i -> cas (\(c, e) -> case c of
                             Val v -> Just $ ((insert v (DataInt i) namespace), e)
                             Data (DataInt ic) ->
                               if ic == i
                               then Just (namespace, e)
                               else Nothing
                             _ -> Nothing
                         )
        DataADT name vals ->
          cas (\(c, e) ->
                 case c of
                   Val v -> Just $ ((insert v cased namespace), e)
                   Application _ _ -> do
                     let ((Val cname):cvals) = rollApplication c
                     guard $ cname == name
                     guard $ length cvals == length vals
                     guard $ let zipper (Data cd) d = cd == d
                                 zipper _ _ = True
                             in all id (zipWith zipper cvals vals)
                     let ins n (Val v, d) = insert v d n
                         ins n _ = n
                         ns = foldl ins namespace (zip cvals vals)
                     pure (ns, e)
                   _ -> Nothing
                  )
        _ -> Nothing
      case newe of
        Nothing -> error "Lambda exhaustion"
        Just ee -> pure ee


evalProgram :: Namespace -> Expr -> Either String Data
evalProgram ns ex = evalState (runReaderT (runExceptT $ eval ex) ns) (M.empty, 0)
