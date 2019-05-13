module Radlang.Pretty where

import Radlang.Types
import qualified Data.Map.Strict as M
import Data.Text as T
import Data.List as DL

prefix :: Int -> [Char]
prefix ident = DL.take ident (repeat ' ')

prettyBnds :: Int -> TypedBindings -> String
prettyBnds ident p = DL.unlines $ flip fmap (M.toList p) $ \(n, (t, talts)) ->
  prefix ident <> T.unpack n <> " : " <> show t <> "\n" <> ((prettyTAlt ident n) =<< talts)

prettyPBnds :: PolyBindings -> String
prettyPBnds p = DL.unlines $ flip fmap (M.toList p) $ \(n, dl) ->
  (("FOR " <> T.unpack n <> " : " <> show (fst dl) <> "\n")<>) $ DL.unlines $ flip fmap (snd dl) $ \(t, talts) ->
  "POLY " <> T.unpack n <> " : " <> show t <> "\n" <> ((prettyTAlt 0 n) =<< talts)

prettyTAlt :: Int -> Name -> TypedAlt -> String
prettyTAlt ident n (args, te) = prefix ident <> T.unpack n <> " " <> show args <> " :=\n" <>
  prettyTE (ident + 4) te

prettyTE :: Int -> TypedExpr -> String
prettyTE ident = \case
  TypedLet _ bnds te -> prefix ident <> "let\n" <> prettyBnds (ident + 4) bnds
    <> prefix ident <> "in\n" <> prettyTE ident te
  a -> prefix ident <> show a <> "\n"

prettyBndsE :: Int -> ImplBindings -> String
prettyBndsE ident p = DL.unlines $ flip fmap (M.toList p) $ \(n, alts) ->
  prefix ident <> T.unpack n <> "\n" <> ((prettyAlt ident n) =<< alts)


prettyAlt :: Int -> Name -> Alt -> String
prettyAlt ident n (args, e) = prefix ident <> T.unpack n <> " " <> show args <> " :=\n" <>
  prettyE (ident + 4) e

prettyE :: Int -> UntypedExpr -> String
prettyE ident = \case
  UntypedLet (_, _, [bnds]) te -> prefix ident <> "let\n" <> prettyBndsE (ident + 4) bnds
    <> prefix ident <> "in\n" <> prettyE ident te
  a -> prefix ident <> show a <> "\n"
