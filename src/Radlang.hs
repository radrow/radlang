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
import Radlang.Typedefs
import Radlang.Typechecker
import Radlang.Desugar


