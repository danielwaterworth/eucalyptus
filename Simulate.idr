module Simulate

import Data.Vect
import Data.Colist

import Finite
import CircuitOps

data Domain = D

data Signal : Domain -> Type -> Type where
  MkSignal :
    Colist x ->
    Signal D x

data Desc : Domain -> Type -> Type where
  MkDesc : x -> Desc D x

Functor (Desc D) where
  map f (MkDesc x) = MkDesc (f x)

Applicative (Desc D) where
  pure x = MkDesc x
  MkDesc f <*> MkDesc x = MkDesc (f x)

Monad (Desc D) where
  MkDesc x >>= f = f x

mooreS : (Colist s -> Colist i -> Colist (Pair s o)) -> s -> Colist i -> Colist o
mooreS f initial i = map snd steps
 where mutual
    steps : Colist (Pair s o)
    steps = f (initial :: map fst steps) i

foo : x = y -> x -> y
foo Refl x = x

bar : x = y -> Vect x Bool = Vect y Bool
bar Refl = Refl

CircuitOps Domain Signal Desc where
  add D (MkSignal x) (MkSignal y) = pure (MkSignal (zipWith addBitInt x y))

  reinterpret {fx} {fy} D prf (MkSignal x) =
      MkSignal (map recode x)
    where
      recode : X -> Y
      recode x = decode encoded'
        where
          encoded : Vect (length @{fx}) Bool
          encoded = encode x

          prf' : Vect (length @{fx}) Bool = Vect (length @{fy}) Bool
          prf' = bar prf

          encoded' : Vect (length @{fy}) Bool
          encoded' = foo prf' encoded

  unpair D (MkSignal x) = pure (MkSignal (map fst x), MkSignal (map snd x))

  pair D (MkSignal x) (MkSignal y) = pure (MkSignal (zip x y))

  moore D f initial (MkSignal input) =
    pure $ MkSignal $
      mooreS
        (\states => \inputs =>
          let MkDesc (MkSignal output) = f (MkSignal states) (MkSignal inputs)
          in output)
        initial
        input

  constant D x = pure (MkSignal (repeat x))

  invert D (MkSignal x) = pure $ MkSignal $ map (map not) x

  eq D (MkSignal x) (MkSignal y) =
    pure $ MkSignal $ zipWith (==) (map encode x) (map encode y)

  lt D (MkSignal x) (MkSignal y) =
    pure $ MkSignal $ zipWith (<) (map encode x) (map encode y)

  mux D (MkSignal cond) (MkSignal t) (MkSignal f) =
    pure $ MkSignal $ zipWith3 (\cond' => \t' => \f' => if cond' then t' else f') cond t f

public export
simulate : {I:Type} -> {O:Type} -> Circuit I O -> Colist I -> Colist O
simulate (MkCircuit f) i =
  let MkDesc (MkSignal o) = f D (MkSignal i)
  in o
