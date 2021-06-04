module Simulate

import Data.Vect
import Data.Colist

import Finite
import CircuitOps

data Domain = D

data Signal : Domain -> Nat -> Type -> Type where
  MkSignal : {n:Nat} -> Colist x -> Signal D n x

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
  add D (MkSignal a) (MkSignal b) = pure (MkSignal (zipWith addBitInt a b))

  reinterpret D prf (MkSignal a) =
      MkSignal (map recode a)
    where
      recode : x -> y
      recode v = decode encoded'
        where
          encoded : Vect (length @{fx}) Bool
          encoded = encode v

          prf' : Vect (length @{fx}) Bool = Vect (length @{fy}) Bool
          prf' = bar prf

          encoded' : Vect (length @{fy}) Bool
          encoded' = foo prf' encoded

  unpair D (MkSignal x) = pure (MkSignal (map fst x), MkSignal (map snd x))

  pair D (MkSignal x) (MkSignal y) = pure (MkSignal (zip x y))

  moore D f initial (MkSignal input) =
    pure $ MkSignal $
      mooreS
        (\states, inputs =>
          let MkDesc (MkSignal a, MkSignal b) = f (MkSignal states) (MkSignal inputs)
          in zip a b)
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
data Values : List (String, Nat, Type) -> Type where
  Nil : Values []
  (::) :
    {n:Nat} ->
    Colist t ->
    Values xs ->
    Values ((name, n, t) :: xs)

translate : Values x -> HalfPort Signal D x
translate [] = []
translate (x :: xs) = MkSignal x :: translate xs

inverse : HalfPort Signal D x -> Values x
inverse [] = []
inverse (MkSignal x :: xs) = x :: inverse xs
inverse _ = ?inverse1

public export
simulate : {i, o : List (String, Nat, Type)} -> Circuit i o -> Values i -> Values o
simulate (MkCircuit {fo} f) i =
  let MkDesc o = f D (translate i)
  in inverse o
