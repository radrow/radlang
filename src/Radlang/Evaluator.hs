module Radlang.Evaluator where

import Data.Maybe (catMaybes)
import Data.Traversable (for)
import Control.Applicative
import Control.Monad.State.Strict
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.Trans.Maybe
import Prelude hiding (lookup)
import qualified Data.Map.Strict as M

import Radlang.Helpers
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
withAssg :: (Name, Int) -> Evaluator a -> Evaluator a
withAssg (n, d) = local (M.insert n d)

-- |Same as `withAssg`, but evaluation performed
withAssgExpr :: (Name, Int) -> Expr -> Evaluator Data
withAssgExpr a e = withAssg a (eval e)

-- |Evals with data bound to name
withData :: (Name, DataEntry) -> Evaluator a -> Evaluator a
withData (n, d) e = registerData d >>= \i -> withAssg (n <~ i) e

-- |Same as `withData`, but evaluation performed
withDataExpr :: (Name, DataEntry) -> Expr -> Evaluator Data
withDataExpr a e = withData a (eval e)

-- |Evals with updated namespace
withNs :: Namespace -> Evaluator a -> Evaluator a
withNs n = local (update n)

-- |Same as `withNs`, but evaluation performed
withNsExpr :: Namespace -> Expr -> Evaluator Data
withNsExpr n e = local (update n) (eval e)

eval :: Expr -> Evaluator Data
eval expr =
  case expr of
    Val a -> lookupName a >>= \case
      Just x -> force x
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
      withNsExpr newns e

    Lambda name e -> (\ns -> DataLambda ns name e) <$> ask

    Case ecased cases -> do
      let caseWith :: ((Expr, Expr) -> Evaluator (Maybe Data)) -> Evaluator (Maybe Data)
          caseWith = msum . flip fmap cases
      cased <- eval ecased
      namespace <- ask
      newe <- case cased of
        DataInt i -> caseWith (\(c, e) -> case c of
                                  Val v -> Just <$> withDataExpr (v <~ Strict (DataInt i)) e
                                  Data d -> case d of
                                    DataInt ic ->
                                        if ic == i
                                        then Just <$> eval e
                                        else pure Nothing
                                    _ -> pure Nothing
                                  _ -> pure Nothing
                              )
        DataADT name vals ->
          caseWith (\(c, e) ->
                 case c of
                   Val v -> Just <$> withDataExpr (v <~ Strict cased) e
                   Application _ _ -> case rollApplication c of
                     ((Val cname):cvals) -> runMaybeT $ do
                       -- check if matches
                       guard $ cname == name
                       guard $ length cvals == length vals
                       forcedVals <- lift $ for vals force
                       guard $ let zipper (Data cd) d = cd == d
                                   zipper _ _ = True
                               in all id (zipWith zipper cvals forcedVals)

                       -- matched – now we may eval expr
                       -- create new namespace for evaluation of `e`
                       let insd (Val v, d) = do
                             i <- registerData d
                             pure $ Just (v <~ i)
                           insd _ = pure Nothing
                       nsbuild <- lift $ for (zip cvals vals) $ insd
                       let insn :: (Namespace -> (Name, DataId) -> Namespace)
                           insn n (valname, dataid) = M.insert valname dataid n
                           newns :: Namespace
                           newns = foldl insn namespace (catMaybes nsbuild)

                       lift $ withNsExpr newns e

                     _ -> throwError "Invalid ADT match"
                   _ -> pure Nothing
                   )
        _ -> pure Nothing
      case newe of
        Nothing -> throwError "Case match exhaustion"
        Just dd -> pure dd

evalProgram :: Namespace -> Expr -> Either String Data
evalProgram ns ex = evalState (runReaderT (runExceptT $ eval ex) ns) (M.empty, 0)
