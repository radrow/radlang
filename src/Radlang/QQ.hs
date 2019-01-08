{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE DeriveDataTypeable #-}
module Radlang.QQ where

import Data.Generics
import qualified Language.Haskell.TH as TH
import Language.Haskell.TH.Quote
import Text.Megaparsec
import Data.Data
import Data.Set.Internal as S
import Data.Map.Strict as M

import Radlang.Parser
import Radlang.Types hiding (Data)



deriving instance Data RawProgram
deriving instance Data TypeAlias
deriving instance Data NewType
deriving instance Data ConstructorDef
deriving instance Data ImplDef
deriving instance Data DataDef
deriving instance Data TypeDecl
deriving instance Data TypePoly
deriving instance Data ClassDef
deriving instance Data Pred
deriving instance Data Expr
deriving instance Data RawProgramPart
deriving instance Data Type
deriving instance Data TypeVar
deriving instance Data Kind
deriving instance Data Pattern
deriving instance Data Literal

deriving instance (Data a) => Data (Qual a)


rawrdl :: QuasiQuoter
rawrdl = QuasiQuoter { quoteExp = quoteRawrdlExp }


parseRawrdl :: Monad m => (String, Int, Int) -> String -> m RawProgram
parseRawrdl (file, line, col) s =
  let parser = rawProgram <* eof
  in case parse parser file s of
    Left e -> fail $ show e
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
