module Radlang.TypedQQ where

import Radlang.QQ
import qualified Language.Haskell.TH as TH
import Language.Haskell.TH.Quote

import Radlang.QQ
import Radlang.Typechecker
import Radlang.Parser
import Radlang.Desugar
import Radlang.Types
import System.IO.Unsafe

-- parseTypedRdl :: Monad m => (String, Int, Int) -> String -> m TypedProgram
-- parseTypedRdl loc s = do
--   prg <- parseRdl loc s
--   case (unsafePerformIO $ typecheck (TypecheckerConfig True) prg) of
--     Left e -> fail $ show e
--     Right tprg -> pure tprg

-- quoteTypedRdlExp :: String -> TH.ExpQ
-- quoteTypedRdlExp s = do
--   loc <- TH.location
--   let pos = ( TH.loc_filename loc
--             , fst (TH.loc_start loc)
--             , snd (TH.loc_start loc)
--             )
--   e <- parseTypedRdl pos s
--   dataToExpQ (const Nothing) e

-- trdl :: QuasiQuoter
-- trdl = QuasiQuoter { quoteExp = quoteTypedRdlExp }

