module Compile

import Data.Vect
import Data.Nat

import Control.Monad.RWS
import Control.Monad.Identity

import Finite
import CircuitOps

data Domain = D

data Output =
  MkOutput
    (List String)
    (List String)

Semigroup Output where
  MkOutput a b <+> MkOutput x y = MkOutput (a ++ x) (b ++ y)

Monoid Output where
  neutral = MkOutput [] []

data Signal : Domain -> Nat -> Type -> Type where
  MkSignal : Nat -> Signal D n x

data Desc : Domain -> Type -> Type where
  MkDesc : RWS () Output Nat x -> Desc D x

Functor (Desc D) where
  map f (MkDesc m) = MkDesc (map f m)

Applicative (Desc D) where
  pure x = MkDesc $ pure x
  MkDesc f <*> MkDesc x = MkDesc (f <*> x)

Monad (Desc D) where
  MkDesc x >>= f = MkDesc (x >>= (\y =>
    let MkDesc z = f y
    in z))

MonadState Nat (Desc D) where
  get = MkDesc get
  put x = MkDesc $ put x

MonadWriter Output (Desc D) where
  tell w = MkDesc $ tell w
  listen (MkDesc m) = MkDesc $ listen m
  pass (MkDesc m) = MkDesc $ pass m

alloc : Desc D Nat
alloc = state (\s => (s + 1, s))

literal : Vect n Bool -> String
literal xs =
    concat ([show (length xs), "'b"] ++ map bitToString xs)
  where
    bitToString : Bool -> String
    bitToString True = "1"
    bitToString False = "0"

CircuitOps Domain Signal Desc where
  add {n} D (MkSignal x) (MkSignal y) = do
    v <- alloc
    tell $
      MkOutput
        [
          "  wire [",
          show n,
          ":0] v",
          show v,
          " = v",
          show x,
          " + v",
          show y,
          ";\n"
        ]
        []
    pure $ MkSignal v

  reinterpret D _ (MkSignal x) = MkSignal x

  unpair {fx} {fy} D (MkSignal x) = do
    a <- alloc
    b <- alloc

    tell $
      MkOutput
        [
          "  wire [",
          show $ pred $ length @{fx},
          ":0] v",
          show a,
          " = v",
          show x,
          "[",
          show $ pred (length @{fx} + length @{fy}),
          ":",
          show (length @{fy}),
          "];\n"
        ]
        []

    tell $
      MkOutput
        [
          "  wire [",
          show $ pred $ length @{fy},
          ":0] v",
          show b,
          " = v",
          show x,
          "[",
          show $ pred $ length @{fy},
          ":0];\n"
        ]
        []

    pure (MkSignal a, MkSignal b)

  pair {fx} {fy} D (MkSignal x) (MkSignal y) = do
    n <- alloc
    tell $
      MkOutput
        [
          "  wire [",
          show $ pred (length @{fx} + length @{fy}),
          ":0] v",
          show n,
          " = {v",
          show x,
          ", v",
          show y,
          "};\n"
        ]
        []
    pure $ MkSignal n

  moore {fs} D f initial input = do
    s <- alloc
    x <- f (MkSignal s) input
    (MkSignal s', o) <- unpair D x

    tell $
      MkOutput
        [
          "  reg [",
          show $ pred $ length @{fs},
          ":0] v",
          show s,
          " = ",
          literal $ encode initial,
          ";\n"
        ]
        [
          "  always @(posedge clk) v",
          show s,
          " <= v",
          show s',
          ";\n"
        ]

    pure o

  constant D x = ?constant

  invert {n} D (MkSignal x) = do
    o <- alloc
    tell $
      MkOutput
        [
          "  wire [",
          show $ pred n,
          ":0] v",
          show o,
          " = ~v",
          show x,
          ";\n"
        ]
        []
    pure $ MkSignal o

  eq D (MkSignal a) (MkSignal b) = do
    n <- alloc
    tell $
      MkOutput
        [
          "  wire [1:0] v",
          show n,
          " = v",
          show a,
          " == v",
          show b,
          ";\n"
        ]
        []
    pure $ MkSignal n

  lt D (MkSignal a) (MkSignal b) = do
    n <- alloc
    tell $
      MkOutput
        [
          "  wire [1:0] v",
          show n,
          " = v",
          show a,
          " < v",
          show b,
          ";\n"
        ]
        []
    pure $ MkSignal n

  mux D (MkSignal cond) (MkSignal t) (MkSignal f) = do
    n <- alloc
    tell $
      MkOutput
        [
          "  wire [1:0] v",
          show n,
          " = v",
          show cond,
          " ? v",
          show t,
          " : v",
          show f,
          ";\n"
        ]
        []
    pure $ MkSignal n

public export
compile : {I:Type} -> {O:Type} -> (fi:Finite I) => String -> Circuit I O -> String
compile moduleName (MkCircuit f) =
  let
    MkDesc m = f D (MkSignal 0)
    (o, _, MkOutput decls updates) = runRWS m MkUnit 1
  in
    concat $ concat (the (List (List String)) [
      [
        "module ",
        moduleName,
        "(\n",
        "  input clk,\n",
        "  input [", show $ pred $ length @{fi}, ":0] in\n",
        ")\n"
      ],
      decls,
      ["\n"],
      updates,
      ["endmodule\n"]
    ])
