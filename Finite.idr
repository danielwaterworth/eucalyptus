module Finite

import Data.Bits
import Data.Vect
import Data.Nat

unconcat : {m:Nat} -> {n:Nat} -> Vect (m * n) x -> Vect m (Vect n x)
unconcat {m=0} [] = []
unconcat {m=S m} {n} xs =
  let (y, ys) = splitAt n xs
  in y :: unconcat ys

public export
interface Finite x where
  total length : Nat
  encode : x -> Vect length Bool
  decode : Vect length Bool -> x

public export
(n:Nat) => (fx:Finite x) => Finite (Vect n x) where
  length = n * length @{fx}
  encode val = concat $ map encode val
  decode bits = map decode $ unconcat bits

public export
(fx:Finite x) => (fy:Finite y) => Finite (Pair x y) where
  length = length @{fx} + length @{fy}
  encode (MkPair x y) = encode x ++ encode y
  decode bits =
    let MkPair x y = splitAt (length @{fx}) bits
    in MkPair (decode x) (decode y)

public export
[finitePair] (fx:Finite x) => (fy:Finite y) => Finite (Pair x y) where
  length = length @{fx} + length @{fy}
  encode (MkPair x y) = encode x ++ encode y
  decode bits =
    let MkPair x y = splitAt (length @{fx}) bits
    in MkPair (decode x) (decode y)

public export
Finite Bool where
  length = 1

  encode True = [True]
  encode False = [False]

  decode [True] = True
  decode [False] = False

public export
data BitInt : (n:Nat) -> Type where
  MkBitInt : Vect n Bool -> BitInt n

bitToNat : Bool -> Nat
bitToNat False = 0
bitToNat True = 1

add3 : Bool -> Bool -> Bool -> (Bool, Bool)
add3 False False False = (False, False)
add3 False False True  = (False, True)
add3 False True  False = (False, True)
add3 False True  True  = (True, False)
add3 True  False False = (False, True)
add3 True  False True  = (True, False)
add3 True  True  False = (True, False)
add3 True  True  True  = (True, True)

public export
addBitInt : {n:Nat} -> BitInt n -> BitInt n -> BitInt (S n)
addBitInt {n=Z} (MkBitInt []) (MkBitInt []) = MkBitInt [False]
addBitInt (MkBitInt (x::xs)) (MkBitInt (y::ys)) =
  let
    MkBitInt (z::zs) = addBitInt (MkBitInt xs) (MkBitInt ys)
    (a, b) = add3 x y z
  in
    MkBitInt (a :: b :: zs)

public export
(n:Nat) => Show (BitInt n) where
  show (MkBitInt xs) = show xs

public export
(n:Nat) => Finite (BitInt n) where
  length = n
  encode (MkBitInt xs) = xs
  decode xs = MkBitInt xs

div2 : {n:Nat} -> Fin (S n * 2) -> (Fin (S n), Bool)
div2 FZ = (FZ, False)
div2 (FS FZ) = (FZ, True)
div2 {n=S n} (FS (FS x)) =
  let (x', b) = div2 x
  in (FS x', b)

power2Decompose : {n:Nat} -> power 2 (S n) = 2 * power 2 n

power2Decompose' : {n:Nat} -> Fin (power 2 (S n)) = Fin (2 * power 2 n)

foo : (a = b) -> a -> b
foo Refl x = x

invert : a = b -> b = a
invert Refl = Refl

div2' : {n:Nat} -> Fin (2 * S n) -> (Fin (S n), Bool)

div2'' : {n:Nat} -> Fin (power 2 (S n)) -> (Fin (power 2 n), Bool)

finToBitInt : Fin (power 2 n) -> BitInt n

bitIntToFin : {n:Nat} -> BitInt n -> Fin (power 2 n)

