{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE DeriveDataTypeable #-}
module Radlang.QQ where

import Data.List.NonEmpty as DLNE
import Data.Generics
import qualified Language.Haskell.TH as TH
import Language.Haskell.TH.Quote
import Text.Megaparsec
import Text.Megaparsec.Char
import Data.Data
import Data.Set.Internal as S
import Data.Map.Strict as M
import System.IO.Unsafe

import Radlang.Parser
import Radlang.Types hiding (Data)
import Radlang.Desugar
import Radlang.Typechecker

{-# OPTIONS_GHC -fno-warn-orphans #-}
deriving instance Data RawProgram
deriving instance Data Program
deriving instance Data TypedProgram
deriving instance Data TypedExpr
deriving instance Data TypeEnv
deriving instance Data ClassEnv
deriving instance Data Class
deriving instance Data NewType
deriving instance Data RawNewType
deriving instance Data ConstructorDef
deriving instance Data RawConstructorDef
deriving instance Data RawType
deriving instance Data ImplDef
deriving instance Data RawImplDef
deriving instance Data DataDef
deriving instance Data RawDataDef
deriving instance Data TypeDecl
deriving instance Data RawTypeDecl
deriving instance Data TypePoly
deriving instance Data ClassDef
deriving instance Data RawClassDef
deriving instance Data Pred
deriving instance Data RawPred
deriving instance Data Expr
deriving instance Data RawExpr
deriving instance Data ForComphr
deriving instance Data RawProgramPart
deriving instance Data Type
deriving instance Data TypeVar
deriving instance Data Kind
deriving instance Data Pattern
deriving instance Data Literal

deriving instance (Data a) => Data (RawQual a)
deriving instance (Data a) => Data (Qual a)


rawrdl :: QuasiQuoter
rawrdl = QuasiQuoter { quoteExp = quoteRawrdlExp }


rdl :: QuasiQuoter
rdl = QuasiQuoter { quoteExp = quoteRdlExp }


trdl :: QuasiQuoter
trdl = QuasiQuoter { quoteExp = quoteTypedRdlExp }


parseRawrdl :: Monad m => (String, Int, Int) -> String -> m RawProgram
parseRawrdl (file, line, col) s =
  let parser = rawProgram <* eof
  in case parse parser file s of
    Left e -> fail $ let
      x :: String
      x = concat (fmap parseErrorPretty $ bundleErrors e)
      in fmap (\c -> if c == '\n' then ' ' else c) x
    Right p -> pure p


quoteRawrdlExp :: String -> TH.ExpQ
quoteRawrdlExp s = do
  loc <- TH.location
  let pos = ( TH.loc_filename loc
            , fst (TH.loc_start loc)
            , snd (TH.loc_start loc)
            )
  e <- parseRawrdl pos s
  dataToExpQ (const Nothing) e

{-# NOINLINE parseRdl #-}
parseRdl :: Monad m => (String, Int, Int) -> String -> m Program
parseRdl (file, line, col) s =
  let parser = do
        -- let newpos = SourcePos file (mkPos line) (mkPos col)
        -- updateParserState $ \st ->
        --   st{statePosState = (statePosState st){
        --       pstateSourcePos = newpos
        --       }}
        skipMany controlChar
        rawProgram <* eof
  in case parse parser file s of
    Left e -> fail $ let
      x :: String
      x = concat (fmap parseErrorPretty $ bundleErrors e)
      in fmap (\c -> if c == '\n' then ' ' else c) x
    Right p -> either (fail . show) pure $ buildProgram p


parseTypedRdl :: Monad m => (String, Int, Int) -> String -> m TypedProgram
parseTypedRdl loc s = do
  prg <- parseRdl loc s
  case (unsafePerformIO $ typecheck (TypecheckerConfig True) prg) of
    Left e -> fail $ show e
    Right tprg -> pure tprg


quoteRdlExp :: String -> TH.ExpQ
quoteRdlExp s = do
  loc <- TH.location
  let pos = ( TH.loc_filename loc
            , fst (TH.loc_start loc)
            , snd (TH.loc_start loc)
            )
  e <- parseRdl pos s
  dataToExpQ (const Nothing) e


quoteTypedRdlExp :: String -> TH.ExpQ
quoteTypedRdlExp s = do
  loc <- TH.location
  let pos = ( TH.loc_filename loc
            , fst (TH.loc_start loc)
            , snd (TH.loc_start loc)
            )
  e <- parseTypedRdl pos s
  dataToExpQ (const Nothing) e
