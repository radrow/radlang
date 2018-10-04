module Test where

import Radlang
import Data.Map.Strict as M

p1 = evalProgram M.empty $ (Case (Data (DataADT "XD" [DataInt 3])) [(Application (Val "XD") (Data $ DataInt 7), Val "Bad"), (Application (Val "XD") (Val "Good"), Val "Good")])
