module CircuitOps

import Data.Vect

import Finite

public export
interface CircuitOps
  (Domain : Type)
  (Signal : Domain -> Nat -> Type -> Type)
  (Desc : Domain -> Type -> Type) | Domain where
    add :
      {n:Nat} ->
      (d:Domain) ->
      Signal d n (BitInt n) ->
      Signal d n (BitInt n) ->
      Desc d (Signal d (S n) (BitInt (S n)))

    reinterpret :
      {x, y : Type} ->
      (fx:Finite x) =>
      (fy:Finite y) =>
      (d:Domain) ->
      length @{fx} = length @{fy} ->
      Signal d (length @{fx}) x ->
      Signal d (length @{fy}) y

    unpair :
      {X, Y : Type} ->
      (fx:Finite X) =>
      (fy:Finite Y) =>
      (d:Domain) ->
      Signal d (length @{fx} + length @{fy}) (X, Y) ->
      Desc d (Signal d (length @{fx}) X, Signal d (length @{fy}) Y)

    pair :
      {X, Y : Type} ->
      (fx:Finite X) =>
      (fy:Finite Y) =>
      (d:Domain) ->
      Signal d (length @{fx}) X ->
      Signal d (length @{fy}) Y ->
      Desc d (Signal d (length @{fx} + length @{fy}) (X, Y))

    moore :
      {S, I, O : Type} ->
      (fs:Finite S) =>
      (fi:Finite I) =>
      (fo:Finite O) =>
      (d:Domain) ->
      (
        Signal d (length @{fs}) S ->
        Signal d (length @{fi}) I ->
        Desc d (Signal d (length @{fs}) S, Signal d (length @{fo}) O)
      ) ->
      S ->
      Signal d (length @{fi}) I ->
      Desc d (Signal d (length @{fo}) O)

    constant :
      {X:Type} ->
      (fx:Finite X) =>
      (d:Domain) ->
      X ->
      Desc d (Signal d (length @{fx}) X)

    invert :
      {n:Nat} ->
      (d:Domain) ->
      Signal d n (Vect n Bool) ->
      Desc d (Signal d n (Vect n Bool))

    eq :
      {X:Type} ->
      (fx:Finite X) =>
      (d:Domain) ->
      Signal d (length @{fx}) X ->
      Signal d (length @{fx}) X ->
      Desc d (Signal d 1 Bool)

    lt :
      (d:Domain) ->
      {n:Nat} ->
      Signal d n (BitInt n) ->
      Signal d n (BitInt n) ->
      Desc d (Signal d 1 Bool)

    mux :
      {X:Type} ->
      (fx:Finite X) =>
      (d:Domain) ->
      Signal d 1 Bool ->
      Signal d (length @{fx}) X ->
      Signal d (length @{fx}) X ->
      Desc d (Signal d (length @{fx}) X)

public export
register :
  {Domain : Type} ->
  {Signal : Domain -> Nat -> Type -> Type} ->
  {Desc : Domain -> Type -> Type} ->
  {x:Type} ->
  CircuitOps Domain Signal Desc =>
  (fx:Finite x) =>
  (d:Domain) ->
  Monad (Desc d) =>
  x ->
  Signal d (length @{fx}) x ->
  Desc d (Signal d (length @{fx}) x)
register d initial input =
  moore d (\state, input => pure (input, state)) initial input

public export
not :
  {Domain : Type} ->
  {Signal : Domain -> Nat -> Type -> Type} ->
  {Desc : Domain -> Type -> Type} ->
  CircuitOps Domain Signal Desc =>
  (d:Domain) ->
  Monad (Desc d) =>
  Signal d 1 Bool ->
  Desc d (Signal d 1 Bool)
not d x = do
  let x' = the (Signal d 1 (Vect 1 Bool)) $ reinterpret d Refl x
  y <- invert d x'
  pure $ the (Signal d 1 Bool) $ reinterpret d Refl y

public export
gt :
  {Domain : Type} ->
  {Signal : Domain -> Nat -> Type -> Type} ->
  {Desc : Domain -> Type -> Type} ->
  CircuitOps Domain Signal Desc =>
  {n:Nat} ->
  (d:Domain) ->
  Monad (Desc d) =>
  Signal d n (BitInt n) ->
  Signal d n (BitInt n) ->
  Desc d (Signal d 1 Bool)
gt d x y = lt d y x

public export
ge :
  {Domain : Type} ->
  {Signal : Domain -> Nat -> Type -> Type} ->
  {Desc : Domain -> Type -> Type} ->
  CircuitOps Domain Signal Desc =>
  {n:Nat} ->
  (d:Domain) ->
  Monad (Desc d) =>
  Signal d n (BitInt n) ->
  Signal d n (BitInt n) ->
  Desc d (Signal d 1 Bool)
ge d x y = lt d x y >>= not d

public export
le :
  {Domain : Type} ->
  {Signal : Domain -> Nat -> Type -> Type} ->
  {Desc : Domain -> Type -> Type} ->
  CircuitOps Domain Signal Desc =>
  {n:Nat} ->
  (d:Domain) ->
  Monad (Desc d) =>
  Signal d n (BitInt n) ->
  Signal d n (BitInt n) ->
  Desc d (Signal d 1 Bool)
le d x y = gt d x y >>= not d

public export
data HalfPort : {Domain:Type} -> (signal : Domain -> Nat -> Type -> Type) -> Domain -> List (String, Nat, Type) -> Type where
  Nil : HalfPort signal d []
  (::) :
    {Domain : Type} ->
    {signal : Domain -> Nat -> Type -> Type} ->
    {d:Domain} ->
    signal d n t -> HalfPort signal d xs -> HalfPort signal d ((name, n, t)::xs)

public export
data Finites : List (String, Nat, Type) -> Type where
  First : Finites []
  Next :
    (fx:Finite x) ->
    (n:Nat) ->
    length @{fx} = n ->
    Finites xs ->
    Finites ((name, n, x)::xs)

public export
data Circuit : (i, o : List (String, Nat, Type)) -> Type where
  MkCircuit :
    {i, o : List (String, Nat, Type)} ->
    {auto fi: Finites i} ->
    {auto fo: Finites o} ->
    (
      {Domain : Type} ->
      {Signal : Domain -> Nat -> Type -> Type} ->
      {Desc : Domain -> Type -> Type} ->
      CircuitOps Domain Signal Desc =>
      (domain : Domain) ->
      Monad (Desc domain) =>
      HalfPort Signal domain i ->
      Desc domain (HalfPort Signal domain o)
    ) ->
    Circuit i o
