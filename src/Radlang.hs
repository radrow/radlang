-- |Purely functional programming language inspired by Haskell and OCaml

module Radlang
    ( runProgram
    , typecheck
    , parseRDL
    , buildProgram
    ) where

import Data.Map as M

import Radlang.Parser
import Radlang.Evaluator
import Radlang.Intro
import Radlang.Types
import Radlang.Typechecker
import Radlang.Desugar


-- |Perform evaluation of the main value from the program
runProgram :: TypedProgram -> Either ErrMsg StrictData
runProgram tp = let mock = TypedLet (tprgBindings tp) (TypedVal "main")
                    (ns, ds, ts) = primitiveSpace
                in runEvaluator
                   (tprgNamespace tp `M.union` ns)
                   (_dsMap (tprgDataspace tp) `M.union` ds)
                   ts $ eval mock >>= deepForce

