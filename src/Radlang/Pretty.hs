module Radlang.Pretty where

import Radlang.Types
import qualified Data.Map.Strict as M

prefix :: Int -> [Char]
prefix ident = take ident (repeat ' ')

prettyBnds :: Int -> TypedBindings -> String
prettyBnds ident p = unlines $ flip fmap (M.toList p) $ \(n, (t, talts)) ->
  prefix ident <> n <> " : " <> show t <> "\n" <> ((prettyTAlt ident n) =<< talts)

prettyPBnds :: PolyBindings -> String
prettyPBnds p = unlines $ flip fmap (M.toList p) $ \(n, dl) -> unlines $ flip fmap dl $ \(t, talts) ->
  "POLY " <> n <> " : " <> show t <> "\n" <> ((prettyTAlt 0 n) =<< talts)

prettyTAlt :: Int -> Name -> TypedAlt -> String
prettyTAlt ident n (args, te) = prefix ident <> n <> " " <> show args <> " :=\n" <>
  prettyTE (ident + 4) te

prettyTE :: Int -> TypedExpr -> String
prettyTE ident = \case
  TypedLet _ bnds te -> prefix ident <> "let\n" <> prettyBnds (ident + 4) bnds
    <> prefix ident <> "in\n" <> prettyTE ident te
  a -> prefix ident <> show a <> "\n"
