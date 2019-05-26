-- |Purely functional programming language inspired by Haskell and OCaml

module Radlang
    ( runProgram
    , typecheck
    , parseRDL
    , buildProgram
    ) where

import Radlang.Parser
import Radlang.Evaluator
import Radlang.Typechecker
import Radlang.Desugar


