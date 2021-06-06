module Main

import Data.Bits
import Data.Vect
import Data.Nat
import Data.Colist

import Finite
import CircuitOps
import Compile
import Simulate

testCircuit : Circuit [("a", 4, BitInt 4), ("b", 4, BitInt 4)] [("out", 5, BitInt 5)]
testCircuit =
  MkCircuit $ \d, [a, b] => do
    output <- add d a b
    out <- register d (MkBitInt [True, True, True, True, True]) output
    pure [out]

main : IO ()
main = do
  putStrLn $ compile "test" testCircuit
  let [out] =
        simulate
          testCircuit
          [
            [MkBitInt [True, True, False, False], MkBitInt [False, True, False, False]],
            [MkBitInt [True, True, False, False], MkBitInt [False, True, False, False]]
          ]
  print $ take 2 out
