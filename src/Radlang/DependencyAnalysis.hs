-- |Utilities to discover dependencies between objects in the program
module Radlang.DependencyAnalysis where

import           Data.Graph
import           Data.Map.Strict as M
import           Data.Set        as S
import qualified Data.Text as T

import           Radlang.Types
import           Radlang.Error


-- |Get names of variables that expression depends on
exprDependencies :: UntypedExpr -> S.Set Name
exprDependencies = go S.empty where
  go acc = \case
    UntypedVal n -> S.insert n acc
    UntypedLit _ -> acc
    UntypedApplication f a -> go (go acc a) f
    UntypedLet (p, e, i) expr -> S.unions (exprDependencies expr : fromP ++ fromE ++ fromI) S.\\ (S.unions [ims, exs, pos]) where
      ims = S.fromList $ M.keys =<< i
      exs = S.fromList $ M.keys e
      pos = S.fromList $ M.keys p
      fromP :: [S.Set Name]
      fromP = fmap (S.unions . fmap (altsDeps . snd) . (\(_, _, _, x) -> x)) $ M.elems p
      fromE = fmap (altsDeps . snd) $ M.elems e
      fromI = fmap (S.unions . fmap altsDeps . M.elems) i


-- |Get all variables' names in the pattern
patternFree :: Pattern -> S.Set Name
patternFree = \case
  PLit _ -> S.empty
  PAs n p -> S.insert n (patternFree p)
  PWildcard -> S.empty
  PConstructor _ ps -> S.unions $ fmap patternFree ps
  PVar n -> S.singleton n


-- |Get names of variables that alt depends on
altDeps :: Alt -> S.Set Name
altDeps (ps, e) = exprDependencies e S.\\ S.unions (fmap patternFree ps)


-- |Get names of variables that collection of alt depends on
altsDeps :: [Alt] -> S.Set Name
altsDeps = S.unions . fmap altDeps


-- |Topologically sorted strongly connected components of dependency graph between alts
sccOfAlts :: [(Name, [Alt])] -> [[Name]]
sccOfAlts inp =
  let names = zip (fmap fst inp) [1..]
      nameToKey :: Name -> Int
      nameToKey = go names where
        go [] n = wtf $ "Indexation failed: " <> n <> " not in " <> T.pack (show names)
        go ((h,i):t) n = if n == h
                          then i
                          else go t n
      descr :: [(Name, Int, [Int])]
      descr = fmap (\((n, es), i) ->
                      (n, i, fmap nameToKey (Prelude.filter (`elem` fmap fst inp) $ S.toList $ altsDeps es)))
              (zip inp [1..])
  in stronglyConnComp descr >>= \case
    AcyclicSCC n -> pure [n]
    CyclicSCC n -> pure n


-- |Group implicit bindings by the SCC
groupBindings :: ImplBindings -> [ImplBindings]
groupBindings im =
  let entries = M.toList im
      toposorted = sccOfAlts entries
  in fmap (\ns -> M.restrictKeys im (S.fromList ns)) toposorted


-- |Toposort the interface hierarchy
interfaceHierarchySort :: [InterfaceDef] -> [InterfaceDef]
interfaceHierarchySort cds =
  let cdi = zip cds [0::Int ..]
      connect c = [i | (other, i) <- cdi, S.member (interfacedefName other) (interfacedefSuper c)]
      (gr, fromVer, _) = graphFromEdges (fmap (\(c, i) -> (c, i, connect c)) cdi)
      topos = topSort gr
  in reverse $ fmap ((\(c, _, _) -> c) . fromVer) topos
