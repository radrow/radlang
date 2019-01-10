module Radlang.Desugar where

import Data.Map.Strict as M
import Data.Set as S

import Radlang.Typesystem.Typesystem
import Radlang.Types
import Radlang.Helpers
import qualified Radlang.Kindchecker as K
import Radlang.Kindchecker hiding (free)


toplevelBindings :: Kindspace -> [Either TypeDecl DataDef] -> [BindingGroup]
toplevelBindings ks = pure . Prelude.foldl ins (M.empty, [M.empty]) where
  ins :: BindingGroup -> Either TypeDecl DataDef -> BindingGroup
  ins (exs, [imps]) tl = case tl of
    Left (TypeDecl n qt) -> case (M.lookup n exs, M.lookup n imps) of
      (Nothing, Nothing) ->
        (M.insert n (quantify (S.toList $ free qt) qt, []) exs, [imps])
      (Nothing, Just alts) -> let
        e = M.insert n (quantify (S.toList $ free qt) qt, alts) exs
        i = M.delete n imps
        in (e, [i])
      (Just _, _) -> error "Typedecl duplicate"
    Right (DataDef n args body) -> case (M.lookup n exs, M.lookup n imps) of
      (Nothing, Nothing) -> let
        i = M.insert n [(args, body)] imps
        in (exs, [i])
      (Just (t, alts), Nothing) -> let
        e = M.insert n (t, (args, body):alts) exs
        in (e, [imps])
      (Nothing, Just alts) -> let
        i = M.insert n ((args, body):alts) imps
        in (exs, [i])
      _ -> error "Impossible happened: binding both explicit and implicit"
  ins _ _ = error "toplevelBindings process error: imps not a singleton"


