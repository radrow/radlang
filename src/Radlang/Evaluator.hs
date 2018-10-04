module Radlang.Evaluator where

import Control.Monad.State.Strict
import qualified Data.Map.Strict as M

import Radlang.Types
import Radlang.Helpers

evalProgram :: Namespace -> Expr -> Data
evalProgram namespace expr =
  case expr of
    Val a -> case M.lookup a namespace of
      Just x -> x
      Nothing -> error $ "Unbound value: " <> a
    Data d -> d
    Application f arg ->
      case evalProgram namespace f of
        DataLambda ns argname e ->
          evalProgram (M.union namespace
                       (M.insert argname (evalProgram namespace arg) ns)) e
        _ -> error "Function application not into lambda"
    Let assgs e -> evalProgram ns e where
      ns = Prelude.foldl (\m (name, _, ee) ->
                            M.insert
                            name
                            (evalProgram m ee)
                            m
                         ) namespace assgs
    Lambda name e -> DataLambda namespace name e

    Case ecased cases ->
      let cas = msum . flip fmap cases
          cased =  evalProgram namespace ecased
          newe = case cased of
            DataInt i -> cas (\(c, e) -> case c of
                                 Val v -> Just $ ((M.insert v (DataInt i) namespace), e)
                                 Data (DataInt ic) ->
                                   if ic == i
                                   then Just (namespace, e)
                                   else Nothing
                                 _ -> Nothing
                             )
            DataADT name vals ->
              cas (\(c, e) ->
                     case c of
                       Val v -> Just $ ((M.insert v cased namespace), e)
                       Application _ _ -> do
                         let ((Val cname):cvals) = rollApplication c
                         guard $ cname == name
                         guard $ length cvals == length vals
                         guard $ let zipper (Data cd) d = cd == d
                                     zipper _ _ = True
                                 in all id (zipWith zipper cvals vals)
                         let ins n (Val v, d) = M.insert v d n
                             ins n _ = n
                             ns = foldl ins namespace (zip cvals vals)
                         Just (ns, e)
                       _ -> Nothing
                  )
            _ -> Nothing
      in case newe of
        Nothing -> error "Lambda exhaustion"
        Just (ns, ee) -> evalProgram ns ee

