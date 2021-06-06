module Compile

import Data.List
import Data.Nat
import Data.Vect

import Syntax.WithProof

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
  ESignal : (fx:Finite x) => length @{fx} = Z -> Signal D Z x
  PSignal : (fx:Finite x) => (n:Nat) -> length @{fx} = S n -> String -> Signal D (S n) x

esignal : (fx:Finite x) => length @{fx} = Z -> Signal D (length @{fx}) x
esignal prf = rewrite prf in ESignal prf

psignal : (fx:Finite x) => (n:Nat) -> length @{fx} = S n -> String -> Signal D (length @{fx}) x
psignal n prf m = rewrite prf in PSignal n prf m

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

alloc : Desc D String
alloc = state (\s => (s + 1, "v" ++ show s))

literal : Vect n Bool -> String
literal xs =
    concat ([show (length xs), "'b"] ++ map bitToString xs)
  where
    bitToString : Bool -> String
    bitToString True = "1"
    bitToString False = "0"

zeroes : (a, b : Nat) -> a + b = 0 -> (a = 0, b = 0)
zeroes 0 0 Refl = (Refl, Refl)
zeroes (S k) b _ impossible

pairCoerce : {x, y, a, b : Nat} -> x = S a -> y = S b -> Signal D (x + y) t -> Signal D (S (a + S b)) t
pairCoerce Refl Refl x = x

absurbAdd : {a, b, x : Nat} -> x = S a -> x + b = Z -> t
absurbAdd Refl Refl impossible

CircuitOps Domain Signal Desc where
  add D (ESignal _) (ESignal _) = constant D (MkBitInt [False])
  add D (PSignal n _ x) (PSignal _ _ y) = do
    v <- alloc
    tell $
      MkOutput
        [
          "  wire [",
          show n,
          ":0] ",
          v,
          " = ",
          x,
          " + ",
          y,
          ";\n"
        ]
        []
    pure $ PSignal (S n) Refl v

  reinterpret D prf input =
    case @@(length @{fx}) of
      (Z ** prf') =>
        let
          prf'' = trans (sym prf') prf
        in
          esignal (sym prf'')
      (S n ** prf') =>
        let
          prf'' = trans (sym prf') prf
          PSignal _ _ v =
            replace
              {p=(\n => Signal D n x)}
              prf'
              input
        in
          psignal n (sym prf'') v

  unpair D x with (length @{fx} + length @{fy}) proof eq
    unpair D (ESignal _) | Z =
      let
        (a, b) = zeroes (length @{fx}) (length @{fy}) eq
      in
        pure (esignal a, esignal b)

    unpair D (PSignal _ _ v) | S n with (length @{fx}) proof ax
      unpair D (PSignal _ _ v) | S n | Z with (length @{fy}) proof by
        unpair D (PSignal _ _ v) | S n | Z | Z impossible
        unpair D (PSignal _ _ v) | S n | Z | S b =
          pure (ESignal ax, PSignal b by v)
      unpair D (PSignal _ _ v) | S n | S a with (length @{fy}) proof by
        unpair D (PSignal _ _ v) | S n | S a | Z =
          pure (PSignal a ax v, ESignal by)
        unpair D (PSignal _ _ v) | S n | S a | S b = do
          x <- alloc
          y <- alloc

          tell $
            MkOutput
              [
                "  wire [",
                show $ a,
                ":0] ",
                x,
                " = ",
                v,
                "[",
                show n,
                ":",
                show (b + 1),
                "];\n"
              ]
              []

          tell $
            MkOutput
              [
                "  wire [",
                show b,
                ":0] ",
                y,
                " = ",
                v,
                "[",
                show b,
                ":0];\n"
              ]
              []

          pure (PSignal a ax x, PSignal b by y)

  pair D x y with (length @{fx}) proof ax
    pair D x y | Z with (length @{fy}) proof by
      pair D (ESignal _) (ESignal _) | Z | Z = ?pair1
      pair D (ESignal _) (PSignal _ _ x) | Z | S b = ?pair2
    pair D x y | S a with (length @{fy}) proof by
      pair D (PSignal _ _ x) (ESignal _) | S a | Z = ?pair3
      pair D (PSignal _ _ x) (PSignal _ _ y) | S a | S b with (length @{fx} + length @{fy}) proof prf
        pair D (PSignal _ _ x) (PSignal _ _ y) | S a | S b | Z = absurbAdd ax prf
        pair D (PSignal _ _ x) (PSignal _ _ y) | S a | S b | S n = do
          o <- alloc
          tell $
            MkOutput
              [
                "  wire [",
                show n,
                ":0] ",
                o,
                " = {",
                x,
                ", ",
                y,
                "};\n"
              ]
              []
          pure $ pairCoerce ax by $ psignal @{finitePair @{fx} @{fy}} n prf o

  moore D f initial input with (length @{fo})
    moore D f initial input | Z = ?moore1
    moore D f initial input | S n with (length @{fs}) proof prf
      moore D f initial input | S n | Z = ?moore2
      moore D f initial input | S n | S m = do
        s <- alloc
        (PSignal _ _ s', o) <- f (PSignal m prf s) input

        tell $
          MkOutput
            [
              "  reg [",
              show m,
              ":0] ",
              s,
              " = ",
              literal $ encode @{fs} initial,
              ";\n"
            ]
            [
              "  always @(posedge clk) ",
              s,
              " <= ",
              s',
              ";\n"
            ]

        pure o

  constant D x =
    case @@(length @{fx}) of
      (Z ** prf) =>
        pure (esignal prf)
      (S n ** prf) => do
        v <- alloc
        tell $
          MkOutput
            [
              "  wire [",
              show n,
              ":0] ",
              v,
              " = ",
              literal $ encode x,
              ";\n"
            ]
            []
        pure (psignal n prf v)

  invert D (ESignal prf) = pure $ ESignal prf
  invert D (PSignal n prf x) = do
    o <- alloc
    tell $
      MkOutput
        [
          "  wire [",
          show n,
          ":0] ",
          o,
          " = ~",
          x,
          ";\n"
        ]
        []
    pure $ PSignal n prf o

  eq D a b with (length @{fx})
    eq D (PSignal _ _ a) (PSignal _ _ b) | S n = do
      n <- alloc
      tell $
        MkOutput
          [
            "  wire [1:0] v",
            show n,
            " = ",
            a,
            " == ",
            b,
            ";\n"
          ]
          []
      pure $ PSignal Z Refl n
    eq D (ESignal _) (ESignal _) | Z = constant D True

  lt {n=S n} D (PSignal _ _ a) (PSignal _ _ b) = do
    n <- alloc
    tell $
      MkOutput
        [
          "  wire [1:0] v",
          show n,
          " = ",
          a,
          " < ",
          b,
          ";\n"
        ]
        []
    pure $ PSignal Z Refl n
  lt {n=Z} D (ESignal _) (ESignal _) = constant D True

  mux D (PSignal 0 _ cond) t f with (length @{fx})
    mux D (PSignal 0 _ cond) (PSignal _ _ t) (PSignal _ _ f) | S n = do
      o <- alloc
      tell $
        MkOutput
          [
            "  wire [",
            show n,
            ":0] ",
            o,
            " = ",
            cond,
            " ? ",
            t,
            " : ",
            f,
            ";\n"
          ]
          []
      pure $ PSignal @{fx} n (believe_me (the (1 = 1) Refl)) o
    mux D (PSignal 0 _ cond) (ESignal _) (ESignal _) | Z =
      pure $ ESignal @{fx} (believe_me (the (1 = 1) Refl))

inputSignal : {i : List (String, Nat, Type)} -> Finites i -> HalfPort Signal D i
inputSignal First = []
inputSignal (Next fx Z prf fs) =
  ESignal prf :: inputSignal fs
inputSignal (Next fx (S n) prf fs) {i=(name, _, _)::_} =
  PSignal n prf name :: inputSignal fs

mkOutput : (String, Nat, String) -> (List String, List String)
mkOutput (name, n, x) =
  (
    ["  output [", show n, ":0] ", name],
    ["  assign ", name, " = ", x, ";\n"]
  )

outputs : {o : List (String, Nat, Type)} -> HalfPort Signal D o -> List (String, Nat, String)
outputs (ESignal _::xs) = outputs xs
outputs {o=(name, _, _) :: _} (PSignal n _ v::xs) = (name, (S n), v) :: outputs xs
outputs _ = []

public export
compile : String -> Circuit i o -> String
compile moduleName (MkCircuit {i} {o} {fi} {fo} f) =
  let
    input = inputSignal fi
    MkDesc m = f D input
    (o, _, MkOutput decls updates) = runRWS m MkUnit 0

    clock = [["  input clk"]]

    inputs = map (\(name, n, t) => ["  input [", show n, ":0] ", name]) i

    (outputs, outputUpdate) = unzip $ map mkOutput $ outputs o
    ports = concat $ intersperse [",\n"] (clock ++ inputs ++ outputs)
  in
    concat $ concat (the (List (List String)) [
      [
        "module ",
        moduleName,
        "(\n"
      ],
      ports,
      ["\n)\n"],
      decls,
      ["\n"],
      updates,
      ["\n"],
      concat outputUpdate,
      ["endmodule\n"]
    ])
