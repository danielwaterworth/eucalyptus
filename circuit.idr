module Main

import Data.Bits
import Data.Vect
import Data.Nat
import Data.Colist

import Finite
import CircuitOps
import Compile
import Simulate

testCircuit : Circuit (Pair (BitInt 4) (BitInt 4)) (BitInt 5)
testCircuit =
  MkCircuit $ \d => \i => do
    (a, b) <- unpair d i
    output <- add d a b
    register d (MkBitInt [True, True, True, True, True]) output

main : IO ()
main = do
  putStrLn $ compile "test" testCircuit
  print $
    take 2 $
      simulate
        testCircuit
        [
          (MkBitInt [True, True, False, False], MkBitInt [False, True, False, False]),
          (MkBitInt [True, True, False, False], MkBitInt [False, True, False, False])
        ]
