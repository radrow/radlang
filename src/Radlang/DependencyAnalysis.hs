module Radlang.DependencyAnalysis where


import Data.Graph
import Data.Map.Strict as M
import Data.Set.Monad as S
import Data.Set as DS

import Radlang.Types


exprDependencies :: Expr -> S.Set Name
exprDependencies = go S.empty where
  go acc = \case
    Val n -> S.insert n acc
    Lit _ -> acc
    Application f a -> go (go acc a) f
    _ -> error "Dep calc not implemented"


exprGroupDependencies :: [Expr] -> S.Set Name
exprGroupDependencies = S.unions . fmap exprDependencies


allNames :: [(Name, [Expr])] -> S.Set Name
allNames = S.unions . fmap (\(n, es) -> S.insert n (exprGroupDependencies es))


sccOfExprs :: [(Name, [Expr])] -> [[Name]]
sccOfExprs inp =
  let names = S.toList $ allNames inp
      nameToKey :: Name -> Int
      nameToKey = go (zip names [1..]) where
        go [] n = error $ "Indexation failed: " <> n <> " not in " <> show names
        go ((h, i):t) n = if n == h
                          then i
                          else go t n
      descr :: [(Name, Int, [Int])]
      descr = fmap (\((n, es), i) -> (n, i, fmap nameToKey (S.toList $ exprGroupDependencies es))) (zip inp [1..])
  in stronglyConnComp descr >>= \case
    AcyclicSCC n -> pure [n]
    CyclicSCC n -> pure n


groupBindings :: ImplBindings -> [ImplBindings]
groupBindings im =
  let entries = fmap (\(n, alts) -> (n, fmap snd alts)) (M.toList im)
      toposorted = sccOfExprs entries
  in fmap (\ns -> M.restrictKeys im (DS.fromList ns)) toposorted
