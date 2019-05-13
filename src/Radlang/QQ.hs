-- |QuasiQuotations for Radlang programs
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveDataTypeable #-}
module Radlang.QQ where

import Data.Generics
import qualified Data.Text as T
import Language.Haskell.TH.Syntax hiding (Pred, Type, Kind)
import qualified Language.Haskell.TH as TH
import Language.Haskell.TH.Quote
import Text.Megaparsec hiding (State)
import Text.Megaparsec.Char

import Radlang.Parser
import Radlang.Types hiding (Data)

{-# OPTIONS_GHC -fno-warn-orphans #-}
deriving instance Data RawProgram
deriving instance Data ErrMsg
deriving instance Data TypedExpr
deriving instance Data TypeEnv
deriving instance Data InterfaceEnv
deriving instance Data Interface
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
deriving instance Data InterfaceDef
deriving instance Data RawInterfaceDef
deriving instance Data Pred
deriving instance Data RawPred
deriving instance Data UntypedExpr
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


-- |Qoter of RawProgram
rawrdl :: QuasiQuoter
rawrdl = QuasiQuoter { quoteExp = quoteRawrdlExp }


-- |Parser for QuasiQuoting
parseRawrdl :: Monad m => (String, Int, Int) -> String -> m RawProgram
parseRawrdl (file, line, col) s =
  let parser = skipMany controlChar *> rawProgram <* eof
  in case parse parser file s of
    Left e -> fail $ let
      x :: String
      x = concat (fmap parseErrorPretty $ bundleErrors e)
      in fmap (\c -> if c == '\n' then ' ' else c) x
    Right p -> pure p



liftText :: T.Text -> Q Exp
liftText txt = AppE (VarE 'T.pack) <$> lift (T.unpack txt)


liftDataWithText :: Data a => a -> Q Exp
liftDataWithText = dataToExpQ (\a -> liftText <$> cast a)


-- |RawProgram Exp for QuasiQuoting
quoteRawrdlExp :: String -> TH.ExpQ
quoteRawrdlExp s = do
  loc <- TH.location
  let pos = ( TH.loc_filename loc
            , fst (TH.loc_start loc)
            , snd (TH.loc_start loc)
            )
  e <- parseRawrdl pos s
  liftDataWithText e

