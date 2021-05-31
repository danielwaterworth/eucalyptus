module CircuitOps

import Data.Vect

import Finite

public export
interface CircuitOps
  (Domain : Type)
  (Signal : Domain -> Type -> Type)
  (Desc : Domain -> Type -> Type) | Domain where
    add :
      {n:Nat} ->
      (d:Domain) ->
      Signal d (BitInt n) ->
      Signal d (BitInt n) ->
      Desc d (Signal d (BitInt (S n)))

    reinterpret :
      {X:Type} ->
      {Y:Type} ->
      (fx:Finite X) =>
      (fy:Finite Y) =>
      (d:Domain) ->
      length @{fx} = length @{fy} ->
      Signal d X ->
      Signal d Y

    unpair :
      {X:Type} ->
      {Y:Type} ->
      (fx:Finite X) =>
      (fy:Finite Y) =>
      (d:Domain) ->
      Signal d (X, Y) ->
      Desc d (Signal d X, Signal d Y)

    pair :
      {X:Type} ->
      {Y:Type} ->
      (fx:Finite X) =>
      (fy:Finite Y) =>
      (d:Domain) ->
      Signal d X ->
      Signal d Y ->
      Desc d (Signal d (X, Y))

    moore :
      {S:Type} ->
      {I:Type} ->
      {O:Type} ->
      (fs:Finite S) =>
      (fo:Finite O) =>
      (d:Domain) ->
      (Signal d S -> Signal d I -> Desc d (Signal d (Pair S O))) ->
      S ->
      Signal d I ->
      Desc d (Signal d O)

    constant :
      {X:Type} ->
      Finite X =>
      (d:Domain) ->
      X ->
      Desc d (Signal d X)

    invert :
      {n:Nat} ->
      (d:Domain) ->
      Signal d (Vect n Bool) ->
      Desc d (Signal d (Vect n Bool))

    eq :
      {X:Type} ->
      Finite X =>
      (d:Domain) ->
      Signal d X ->
      Signal d X ->
      Desc d (Signal d Bool)

    lt :
      {X:Type} ->
      Finite X =>
      (d:Domain) ->
      Signal d X ->
      Signal d X ->
      Desc d (Signal d Bool)

    mux :
      {X:Type} ->
      Finite X =>
      (d:Domain) ->
      Signal d Bool ->
      Signal d X ->
      Signal d X ->
      Desc d (Signal d X)

public export
register :
  {Domain : Type} ->
  {Signal : Domain -> Type -> Type} ->
  {Desc : Domain -> Type -> Type} ->
  {x:Type} ->
  CircuitOps Domain Signal Desc =>
  Finite x =>
  (d:Domain) ->
  Monad (Desc d) =>
  x ->
  Signal d x ->
  Desc d (Signal d x)
register d initial input =
  moore d (\state => \input => pair d input state) initial input

public export
not :
  {Domain : Type} ->
  {Signal : Domain -> Type -> Type} ->
  {Desc : Domain -> Type -> Type} ->
  CircuitOps Domain Signal Desc =>
  (d:Domain) ->
  Monad (Desc d) =>
  Signal d Bool ->
  Desc d (Signal d Bool)
not d x = do
  let x' = the (Signal d (Vect 1 Bool)) $ reinterpret d Refl x
  y <- invert d x'
  pure $ the (Signal d Bool) $ reinterpret d Refl y

public export
gt :
  {Domain : Type} ->
  {Signal : Domain -> Type -> Type} ->
  {Desc : Domain -> Type -> Type} ->
  CircuitOps Domain Signal Desc =>
  {n:Nat} ->
  (d:Domain) ->
  Monad (Desc d) =>
  Signal d (Vect n Bool) ->
  Signal d (Vect n Bool) ->
  Desc d (Signal d Bool)
gt d x y = lt d y x

public export
ge :
  {Domain : Type} ->
  {Signal : Domain -> Type -> Type} ->
  {Desc : Domain -> Type -> Type} ->
  CircuitOps Domain Signal Desc =>
  {n:Nat} ->
  (d:Domain) ->
  Monad (Desc d) =>
  Signal d (Vect n Bool) ->
  Signal d (Vect n Bool) ->
  Desc d (Signal d Bool)
ge d x y = lt d x y >>= not d

public export
le :
  {Domain : Type} ->
  {Signal : Domain -> Type -> Type} ->
  {Desc : Domain -> Type -> Type} ->
  CircuitOps Domain Signal Desc =>
  {n:Nat} ->
  (d:Domain) ->
  Monad (Desc d) =>
  Signal d (Vect n Bool) ->
  Signal d (Vect n Bool) ->
  Desc d (Signal d Bool)
le d x y = gt d x y >>= not d

public export
data Circuit : {i:Type} -> {o:Type} -> i -> o -> Type where
  MkCircuit :
    {I:Type} ->
    {O:Type} ->
    Finite I =>
    Finite O =>
    (
      {Domain : Type} ->
      {Signal : Domain -> Type -> Type} ->
      {Desc : Domain -> Type -> Type} ->
      CircuitOps Domain Signal Desc =>
      (domain : Domain) ->
      Monad (Desc domain) =>
      Signal domain I ->
      Desc domain (Signal domain O)
    ) ->
    Circuit I O
