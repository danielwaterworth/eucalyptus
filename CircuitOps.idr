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
      {X:Type} ->
      {Y:Type} ->
      (fx:Finite X) =>
      (fy:Finite Y) =>
      (d:Domain) ->
      length @{fx} = length @{fy} ->
      Signal d (length @{fx}) X ->
      Signal d (length @{fy}) Y

    unpair :
      {X:Type} ->
      {Y:Type} ->
      (fx:Finite X) =>
      (fy:Finite Y) =>
      (d:Domain) ->
      Signal d (length @{fx} + length @{fy}) (X, Y) ->
      Desc d (Signal d (length @{fx}) X, Signal d (length @{fy}) Y)

    pair :
      {X:Type} ->
      {Y:Type} ->
      (fx:Finite X) =>
      (fy:Finite Y) =>
      (d:Domain) ->
      Signal d (length @{fx}) X ->
      Signal d (length @{fy}) Y ->
      Desc d (Signal d (length @{fx} + length @{fy}) (X, Y))

    moore :
      {S:Type} ->
      {I:Type} ->
      {O:Type} ->
      (fs:Finite S) =>
      (fi:Finite I) =>
      (fo:Finite O) =>
      (d:Domain) ->
      (
        Signal d (length @{fs}) S ->
        Signal d (length @{fi}) I ->
        Desc d (Signal d (length @{fs} + length @{fo}) (Pair S O))
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
  moore d (\state => \input => pair d input state) initial input

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
data Circuit : {i:Type} -> {o:Type} -> i -> o -> Type where
  MkCircuit :
    {I:Type} ->
    {O:Type} ->
    (fi:Finite I) =>
    (fo:Finite O) =>
    (
      {Domain : Type} ->
      {Signal : Domain -> Nat -> Type -> Type} ->
      {Desc : Domain -> Type -> Type} ->
      CircuitOps Domain Signal Desc =>
      (domain : Domain) ->
      Monad (Desc domain) =>
      Signal domain (length @{fi}) I ->
      Desc domain (Signal domain (length @{fo}) O)
    ) ->
    Circuit I O
