import Base
import ../source/impl.bend as Source
import ../source/proof.bend as SP
import ../machine/impl.bend as Machine
import ../shared/impl.bend as Shared
import ../fun/impl.bend as Fun
import ../fun/proof.bend as FP
import ../wasm/impl.bend as Wasm
import ../compile_wasm/spec.bend as Contract
import ./spec.bend as Spec
import ./impl.bend as FM
import ./code.bend as Code

# Proofs of the machine in F
# ==========================
#
# Generated. For each function g of the program, L.g states that its code,
# on the encodings of its arguments, returns the encoding of what the Bend def
# that it mirrors computes, in some number of steps.

# Eliminators
# ============

def Elim.Bool(+x: Bool, -P: Bool -> Type, c0: P(False{}), c1: P(True{})) -> P(x):
  match x:
    case False{}:
      c0
    case True{}:
      c1

def Elim.Def(+x: Source.Def, -P: Source.Def -> Type, c0: @k: List<&2, Nat> -> @t: Source.Term -> @v: Source.Term -> @o: Bool -> P(Source.Def{k, t, v, o})) -> P(x):
  match x:
    case Source.Def{k, t, v, o}:
      c0(k, t, v, o)

def Elim.Form(+x: Machine.Form, -P: Machine.Form -> Type, c0: @r: Source.Quan -> @a: Machine.Val -> @b: Machine.Val -> P(Machine.Form.tup{r, a, b}), c1: @k: List<&2, Nat> -> P(Machine.Form.lab{k}), c2: P(Machine.Form.other{})) -> P(x):
  match x:
    case Machine.Form.tup{r, a, b}:
      c0(r, a, b)
    case Machine.Form.lab{k}:
      c1(k)
    case Machine.Form.other{}:
      c2

def Elim.Look(+x: Machine.Look, -P: Machine.Look -> Type, c0: @v: Machine.Val -> P(Machine.Look.val{v}), c1: @j: Nat -> P(Machine.Look.free{j})) -> P(x):
  match x:
    case Machine.Look.val{v}:
      c0(v)
    case Machine.Look.free{j}:
      c1(j)

def Elim.MDef(+x: Maybe<&2, Source.Def>, -P: Maybe<&2, Source.Def> -> Type, c0: P(None{}), c1: @d: Source.Def -> P(Some{d})) -> P(x):
  match x:
    case None{}:
      c0
    case Some{d}:
      c1(d)

def Elim.MName(+x: Maybe<&2, List<&2, Nat>>, -P: Maybe<&2, List<&2, Nat>> -> Type, c0: P(None{}), c1: @k: List<&2, Nat> -> P(Some{k})) -> P(x):
  match x:
    case None{}:
      c0
    case Some{k}:
      c1(k)

def Elim.MNat(+x: Maybe<&2, Nat>, -P: Maybe<&2, Nat> -> Type, c0: P(None{}), c1: @n: Nat -> P(Some{n})) -> P(x):
  match x:
    case None{}:
      c0
    case Some{n}:
      c1(n)

def Elim.MObs(+x: Maybe<&2, Source.Obs>, -P: Maybe<&2, Source.Obs> -> Type, c0: P(None{}), c1: @o: Source.Obs -> P(Some{o})) -> P(x):
  match x:
    case None{}:
      c0
    case Some{o}:
      c1(o)

def Elim.MStart(+x: Maybe<&2, FM.Start>, -P: Maybe<&2, FM.Start> -> Type, c0: P(None{}), c1: @x: FM.Start -> P(Some{x})) -> P(x):
  match x:
    case None{}:
      c0
    case Some{x}:
      c1(x)

def Elim.Move(+x: Machine.Move, -P: Machine.Move -> Type, c0: @s: Machine.St -> P(Machine.Move.go{s}), c1: @v: Machine.Val -> P(Machine.Move.done{v}), c2: P(Machine.Move.stuck{})) -> P(x):
  match x:
    case Machine.Move.go{s}:
      c0(s)
    case Machine.Move.done{v}:
      c1(v)
    case Machine.Move.stuck{}:
      c2

def Elim.Nat(+n: Nat, -P: Nat -> Type, z: P(0n), s: @p: Nat -> P(1n+p)) -> P(n):
  match n:
    case 0n:
      z
    case 1n+p:
      s(p)

def Elim.Quan(+x: Source.Quan, -P: Source.Quan -> Type, c0: P(Source.Q0{}), c1: P(Source.Q1{}), c2: P(Source.Q2{})) -> P(x):
  match x:
    case Source.Q0{}:
      c0
    case Source.Q1{}:
      c1
    case Source.Q2{}:
      c2

def Elim.Start(+x: FM.Start, -P: FM.Start -> Type, c0: @s: Machine.St -> @bk: List<&2, Source.Def> -> P(FM.Start{s, bk})) -> P(x):
  match x:
    case FM.Start{s, bk}:
      c0(s, bk)

# Lemmas
# ======

# Wasm.Nat.at_most(n, k) is Nat.is_le(n, k), for each k to 255. To be replaced
# by one lemma on U32.from_nat.
def AtMost.k0(+n: Nat) -> {Wasm.Nat.at_most(n, 0) == Nat.is_le(n, 0n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def AtMost.k1(+n: Nat) -> {Wasm.Nat.at_most(n, 1) == Nat.is_le(n, 1n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k0(p)

def AtMost.k2(+n: Nat) -> {Wasm.Nat.at_most(n, 2) == Nat.is_le(n, 2n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k1(p)

def AtMost.k3(+n: Nat) -> {Wasm.Nat.at_most(n, 3) == Nat.is_le(n, 3n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k2(p)

def AtMost.k4(+n: Nat) -> {Wasm.Nat.at_most(n, 4) == Nat.is_le(n, 4n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k3(p)

def AtMost.k5(+n: Nat) -> {Wasm.Nat.at_most(n, 5) == Nat.is_le(n, 5n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k4(p)

def AtMost.k6(+n: Nat) -> {Wasm.Nat.at_most(n, 6) == Nat.is_le(n, 6n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k5(p)

def AtMost.k7(+n: Nat) -> {Wasm.Nat.at_most(n, 7) == Nat.is_le(n, 7n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k6(p)

def AtMost.k8(+n: Nat) -> {Wasm.Nat.at_most(n, 8) == Nat.is_le(n, 8n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k7(p)

def AtMost.k9(+n: Nat) -> {Wasm.Nat.at_most(n, 9) == Nat.is_le(n, 9n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k8(p)

def AtMost.k10(+n: Nat) -> {Wasm.Nat.at_most(n, 10) == Nat.is_le(n, 10n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k9(p)

def AtMost.k11(+n: Nat) -> {Wasm.Nat.at_most(n, 11) == Nat.is_le(n, 11n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k10(p)

def AtMost.k12(+n: Nat) -> {Wasm.Nat.at_most(n, 12) == Nat.is_le(n, 12n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k11(p)

def AtMost.k13(+n: Nat) -> {Wasm.Nat.at_most(n, 13) == Nat.is_le(n, 13n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k12(p)

def AtMost.k14(+n: Nat) -> {Wasm.Nat.at_most(n, 14) == Nat.is_le(n, 14n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k13(p)

def AtMost.k15(+n: Nat) -> {Wasm.Nat.at_most(n, 15) == Nat.is_le(n, 15n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k14(p)

def AtMost.k16(+n: Nat) -> {Wasm.Nat.at_most(n, 16) == Nat.is_le(n, 16n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k15(p)

def AtMost.k17(+n: Nat) -> {Wasm.Nat.at_most(n, 17) == Nat.is_le(n, 17n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k16(p)

def AtMost.k18(+n: Nat) -> {Wasm.Nat.at_most(n, 18) == Nat.is_le(n, 18n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k17(p)

def AtMost.k19(+n: Nat) -> {Wasm.Nat.at_most(n, 19) == Nat.is_le(n, 19n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k18(p)

def AtMost.k20(+n: Nat) -> {Wasm.Nat.at_most(n, 20) == Nat.is_le(n, 20n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k19(p)

def AtMost.k21(+n: Nat) -> {Wasm.Nat.at_most(n, 21) == Nat.is_le(n, 21n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k20(p)

def AtMost.k22(+n: Nat) -> {Wasm.Nat.at_most(n, 22) == Nat.is_le(n, 22n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k21(p)

def AtMost.k23(+n: Nat) -> {Wasm.Nat.at_most(n, 23) == Nat.is_le(n, 23n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k22(p)

def AtMost.k24(+n: Nat) -> {Wasm.Nat.at_most(n, 24) == Nat.is_le(n, 24n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k23(p)

def AtMost.k25(+n: Nat) -> {Wasm.Nat.at_most(n, 25) == Nat.is_le(n, 25n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k24(p)

def AtMost.k26(+n: Nat) -> {Wasm.Nat.at_most(n, 26) == Nat.is_le(n, 26n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k25(p)

def AtMost.k27(+n: Nat) -> {Wasm.Nat.at_most(n, 27) == Nat.is_le(n, 27n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k26(p)

def AtMost.k28(+n: Nat) -> {Wasm.Nat.at_most(n, 28) == Nat.is_le(n, 28n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k27(p)

def AtMost.k29(+n: Nat) -> {Wasm.Nat.at_most(n, 29) == Nat.is_le(n, 29n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k28(p)

def AtMost.k30(+n: Nat) -> {Wasm.Nat.at_most(n, 30) == Nat.is_le(n, 30n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k29(p)

def AtMost.k31(+n: Nat) -> {Wasm.Nat.at_most(n, 31) == Nat.is_le(n, 31n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k30(p)

def AtMost.k32(+n: Nat) -> {Wasm.Nat.at_most(n, 32) == Nat.is_le(n, 32n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k31(p)

def AtMost.k33(+n: Nat) -> {Wasm.Nat.at_most(n, 33) == Nat.is_le(n, 33n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k32(p)

def AtMost.k34(+n: Nat) -> {Wasm.Nat.at_most(n, 34) == Nat.is_le(n, 34n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k33(p)

def AtMost.k35(+n: Nat) -> {Wasm.Nat.at_most(n, 35) == Nat.is_le(n, 35n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k34(p)

def AtMost.k36(+n: Nat) -> {Wasm.Nat.at_most(n, 36) == Nat.is_le(n, 36n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k35(p)

def AtMost.k37(+n: Nat) -> {Wasm.Nat.at_most(n, 37) == Nat.is_le(n, 37n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k36(p)

def AtMost.k38(+n: Nat) -> {Wasm.Nat.at_most(n, 38) == Nat.is_le(n, 38n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k37(p)

def AtMost.k39(+n: Nat) -> {Wasm.Nat.at_most(n, 39) == Nat.is_le(n, 39n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k38(p)

def AtMost.k40(+n: Nat) -> {Wasm.Nat.at_most(n, 40) == Nat.is_le(n, 40n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k39(p)

def AtMost.k41(+n: Nat) -> {Wasm.Nat.at_most(n, 41) == Nat.is_le(n, 41n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k40(p)

def AtMost.k42(+n: Nat) -> {Wasm.Nat.at_most(n, 42) == Nat.is_le(n, 42n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k41(p)

def AtMost.k43(+n: Nat) -> {Wasm.Nat.at_most(n, 43) == Nat.is_le(n, 43n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k42(p)

def AtMost.k44(+n: Nat) -> {Wasm.Nat.at_most(n, 44) == Nat.is_le(n, 44n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k43(p)

def AtMost.k45(+n: Nat) -> {Wasm.Nat.at_most(n, 45) == Nat.is_le(n, 45n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k44(p)

def AtMost.k46(+n: Nat) -> {Wasm.Nat.at_most(n, 46) == Nat.is_le(n, 46n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k45(p)

def AtMost.k47(+n: Nat) -> {Wasm.Nat.at_most(n, 47) == Nat.is_le(n, 47n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k46(p)

def AtMost.k48(+n: Nat) -> {Wasm.Nat.at_most(n, 48) == Nat.is_le(n, 48n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k47(p)

def AtMost.k49(+n: Nat) -> {Wasm.Nat.at_most(n, 49) == Nat.is_le(n, 49n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k48(p)

def AtMost.k50(+n: Nat) -> {Wasm.Nat.at_most(n, 50) == Nat.is_le(n, 50n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k49(p)

def AtMost.k51(+n: Nat) -> {Wasm.Nat.at_most(n, 51) == Nat.is_le(n, 51n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k50(p)

def AtMost.k52(+n: Nat) -> {Wasm.Nat.at_most(n, 52) == Nat.is_le(n, 52n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k51(p)

def AtMost.k53(+n: Nat) -> {Wasm.Nat.at_most(n, 53) == Nat.is_le(n, 53n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k52(p)

def AtMost.k54(+n: Nat) -> {Wasm.Nat.at_most(n, 54) == Nat.is_le(n, 54n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k53(p)

def AtMost.k55(+n: Nat) -> {Wasm.Nat.at_most(n, 55) == Nat.is_le(n, 55n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k54(p)

def AtMost.k56(+n: Nat) -> {Wasm.Nat.at_most(n, 56) == Nat.is_le(n, 56n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k55(p)

def AtMost.k57(+n: Nat) -> {Wasm.Nat.at_most(n, 57) == Nat.is_le(n, 57n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k56(p)

def AtMost.k58(+n: Nat) -> {Wasm.Nat.at_most(n, 58) == Nat.is_le(n, 58n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k57(p)

def AtMost.k59(+n: Nat) -> {Wasm.Nat.at_most(n, 59) == Nat.is_le(n, 59n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k58(p)

def AtMost.k60(+n: Nat) -> {Wasm.Nat.at_most(n, 60) == Nat.is_le(n, 60n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k59(p)

def AtMost.k61(+n: Nat) -> {Wasm.Nat.at_most(n, 61) == Nat.is_le(n, 61n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k60(p)

def AtMost.k62(+n: Nat) -> {Wasm.Nat.at_most(n, 62) == Nat.is_le(n, 62n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k61(p)

def AtMost.k63(+n: Nat) -> {Wasm.Nat.at_most(n, 63) == Nat.is_le(n, 63n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k62(p)

def AtMost.k64(+n: Nat) -> {Wasm.Nat.at_most(n, 64) == Nat.is_le(n, 64n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k63(p)

def AtMost.k65(+n: Nat) -> {Wasm.Nat.at_most(n, 65) == Nat.is_le(n, 65n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k64(p)

def AtMost.k66(+n: Nat) -> {Wasm.Nat.at_most(n, 66) == Nat.is_le(n, 66n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k65(p)

def AtMost.k67(+n: Nat) -> {Wasm.Nat.at_most(n, 67) == Nat.is_le(n, 67n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k66(p)

def AtMost.k68(+n: Nat) -> {Wasm.Nat.at_most(n, 68) == Nat.is_le(n, 68n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k67(p)

def AtMost.k69(+n: Nat) -> {Wasm.Nat.at_most(n, 69) == Nat.is_le(n, 69n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k68(p)

def AtMost.k70(+n: Nat) -> {Wasm.Nat.at_most(n, 70) == Nat.is_le(n, 70n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k69(p)

def AtMost.k71(+n: Nat) -> {Wasm.Nat.at_most(n, 71) == Nat.is_le(n, 71n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k70(p)

def AtMost.k72(+n: Nat) -> {Wasm.Nat.at_most(n, 72) == Nat.is_le(n, 72n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k71(p)

def AtMost.k73(+n: Nat) -> {Wasm.Nat.at_most(n, 73) == Nat.is_le(n, 73n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k72(p)

def AtMost.k74(+n: Nat) -> {Wasm.Nat.at_most(n, 74) == Nat.is_le(n, 74n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k73(p)

def AtMost.k75(+n: Nat) -> {Wasm.Nat.at_most(n, 75) == Nat.is_le(n, 75n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k74(p)

def AtMost.k76(+n: Nat) -> {Wasm.Nat.at_most(n, 76) == Nat.is_le(n, 76n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k75(p)

def AtMost.k77(+n: Nat) -> {Wasm.Nat.at_most(n, 77) == Nat.is_le(n, 77n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k76(p)

def AtMost.k78(+n: Nat) -> {Wasm.Nat.at_most(n, 78) == Nat.is_le(n, 78n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k77(p)

def AtMost.k79(+n: Nat) -> {Wasm.Nat.at_most(n, 79) == Nat.is_le(n, 79n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k78(p)

def AtMost.k80(+n: Nat) -> {Wasm.Nat.at_most(n, 80) == Nat.is_le(n, 80n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k79(p)

def AtMost.k81(+n: Nat) -> {Wasm.Nat.at_most(n, 81) == Nat.is_le(n, 81n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k80(p)

def AtMost.k82(+n: Nat) -> {Wasm.Nat.at_most(n, 82) == Nat.is_le(n, 82n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k81(p)

def AtMost.k83(+n: Nat) -> {Wasm.Nat.at_most(n, 83) == Nat.is_le(n, 83n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k82(p)

def AtMost.k84(+n: Nat) -> {Wasm.Nat.at_most(n, 84) == Nat.is_le(n, 84n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k83(p)

def AtMost.k85(+n: Nat) -> {Wasm.Nat.at_most(n, 85) == Nat.is_le(n, 85n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k84(p)

def AtMost.k86(+n: Nat) -> {Wasm.Nat.at_most(n, 86) == Nat.is_le(n, 86n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k85(p)

def AtMost.k87(+n: Nat) -> {Wasm.Nat.at_most(n, 87) == Nat.is_le(n, 87n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k86(p)

def AtMost.k88(+n: Nat) -> {Wasm.Nat.at_most(n, 88) == Nat.is_le(n, 88n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k87(p)

def AtMost.k89(+n: Nat) -> {Wasm.Nat.at_most(n, 89) == Nat.is_le(n, 89n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k88(p)

def AtMost.k90(+n: Nat) -> {Wasm.Nat.at_most(n, 90) == Nat.is_le(n, 90n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k89(p)

def AtMost.k91(+n: Nat) -> {Wasm.Nat.at_most(n, 91) == Nat.is_le(n, 91n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k90(p)

def AtMost.k92(+n: Nat) -> {Wasm.Nat.at_most(n, 92) == Nat.is_le(n, 92n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k91(p)

def AtMost.k93(+n: Nat) -> {Wasm.Nat.at_most(n, 93) == Nat.is_le(n, 93n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k92(p)

def AtMost.k94(+n: Nat) -> {Wasm.Nat.at_most(n, 94) == Nat.is_le(n, 94n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k93(p)

def AtMost.k95(+n: Nat) -> {Wasm.Nat.at_most(n, 95) == Nat.is_le(n, 95n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k94(p)

def AtMost.k96(+n: Nat) -> {Wasm.Nat.at_most(n, 96) == Nat.is_le(n, 96n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k95(p)

def AtMost.k97(+n: Nat) -> {Wasm.Nat.at_most(n, 97) == Nat.is_le(n, 97n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k96(p)

def AtMost.k98(+n: Nat) -> {Wasm.Nat.at_most(n, 98) == Nat.is_le(n, 98n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k97(p)

def AtMost.k99(+n: Nat) -> {Wasm.Nat.at_most(n, 99) == Nat.is_le(n, 99n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k98(p)

def AtMost.k100(+n: Nat) -> {Wasm.Nat.at_most(n, 100) == Nat.is_le(n, 100n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k99(p)

def AtMost.k101(+n: Nat) -> {Wasm.Nat.at_most(n, 101) == Nat.is_le(n, 101n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k100(p)

def AtMost.k102(+n: Nat) -> {Wasm.Nat.at_most(n, 102) == Nat.is_le(n, 102n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k101(p)

def AtMost.k103(+n: Nat) -> {Wasm.Nat.at_most(n, 103) == Nat.is_le(n, 103n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k102(p)

def AtMost.k104(+n: Nat) -> {Wasm.Nat.at_most(n, 104) == Nat.is_le(n, 104n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k103(p)

def AtMost.k105(+n: Nat) -> {Wasm.Nat.at_most(n, 105) == Nat.is_le(n, 105n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k104(p)

def AtMost.k106(+n: Nat) -> {Wasm.Nat.at_most(n, 106) == Nat.is_le(n, 106n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k105(p)

def AtMost.k107(+n: Nat) -> {Wasm.Nat.at_most(n, 107) == Nat.is_le(n, 107n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k106(p)

def AtMost.k108(+n: Nat) -> {Wasm.Nat.at_most(n, 108) == Nat.is_le(n, 108n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k107(p)

def AtMost.k109(+n: Nat) -> {Wasm.Nat.at_most(n, 109) == Nat.is_le(n, 109n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k108(p)

def AtMost.k110(+n: Nat) -> {Wasm.Nat.at_most(n, 110) == Nat.is_le(n, 110n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k109(p)

def AtMost.k111(+n: Nat) -> {Wasm.Nat.at_most(n, 111) == Nat.is_le(n, 111n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k110(p)

def AtMost.k112(+n: Nat) -> {Wasm.Nat.at_most(n, 112) == Nat.is_le(n, 112n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k111(p)

def AtMost.k113(+n: Nat) -> {Wasm.Nat.at_most(n, 113) == Nat.is_le(n, 113n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k112(p)

def AtMost.k114(+n: Nat) -> {Wasm.Nat.at_most(n, 114) == Nat.is_le(n, 114n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k113(p)

def AtMost.k115(+n: Nat) -> {Wasm.Nat.at_most(n, 115) == Nat.is_le(n, 115n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k114(p)

def AtMost.k116(+n: Nat) -> {Wasm.Nat.at_most(n, 116) == Nat.is_le(n, 116n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k115(p)

def AtMost.k117(+n: Nat) -> {Wasm.Nat.at_most(n, 117) == Nat.is_le(n, 117n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k116(p)

def AtMost.k118(+n: Nat) -> {Wasm.Nat.at_most(n, 118) == Nat.is_le(n, 118n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k117(p)

def AtMost.k119(+n: Nat) -> {Wasm.Nat.at_most(n, 119) == Nat.is_le(n, 119n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k118(p)

def AtMost.k120(+n: Nat) -> {Wasm.Nat.at_most(n, 120) == Nat.is_le(n, 120n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k119(p)

def AtMost.k121(+n: Nat) -> {Wasm.Nat.at_most(n, 121) == Nat.is_le(n, 121n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k120(p)

def AtMost.k122(+n: Nat) -> {Wasm.Nat.at_most(n, 122) == Nat.is_le(n, 122n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k121(p)

def AtMost.k123(+n: Nat) -> {Wasm.Nat.at_most(n, 123) == Nat.is_le(n, 123n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k122(p)

def AtMost.k124(+n: Nat) -> {Wasm.Nat.at_most(n, 124) == Nat.is_le(n, 124n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k123(p)

def AtMost.k125(+n: Nat) -> {Wasm.Nat.at_most(n, 125) == Nat.is_le(n, 125n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k124(p)

def AtMost.k126(+n: Nat) -> {Wasm.Nat.at_most(n, 126) == Nat.is_le(n, 126n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k125(p)

def AtMost.k127(+n: Nat) -> {Wasm.Nat.at_most(n, 127) == Nat.is_le(n, 127n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k126(p)

def AtMost.k128(+n: Nat) -> {Wasm.Nat.at_most(n, 128) == Nat.is_le(n, 128n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k127(p)

def AtMost.k129(+n: Nat) -> {Wasm.Nat.at_most(n, 129) == Nat.is_le(n, 129n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k128(p)

def AtMost.k130(+n: Nat) -> {Wasm.Nat.at_most(n, 130) == Nat.is_le(n, 130n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k129(p)

def AtMost.k131(+n: Nat) -> {Wasm.Nat.at_most(n, 131) == Nat.is_le(n, 131n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k130(p)

def AtMost.k132(+n: Nat) -> {Wasm.Nat.at_most(n, 132) == Nat.is_le(n, 132n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k131(p)

def AtMost.k133(+n: Nat) -> {Wasm.Nat.at_most(n, 133) == Nat.is_le(n, 133n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k132(p)

def AtMost.k134(+n: Nat) -> {Wasm.Nat.at_most(n, 134) == Nat.is_le(n, 134n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k133(p)

def AtMost.k135(+n: Nat) -> {Wasm.Nat.at_most(n, 135) == Nat.is_le(n, 135n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k134(p)

def AtMost.k136(+n: Nat) -> {Wasm.Nat.at_most(n, 136) == Nat.is_le(n, 136n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k135(p)

def AtMost.k137(+n: Nat) -> {Wasm.Nat.at_most(n, 137) == Nat.is_le(n, 137n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k136(p)

def AtMost.k138(+n: Nat) -> {Wasm.Nat.at_most(n, 138) == Nat.is_le(n, 138n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k137(p)

def AtMost.k139(+n: Nat) -> {Wasm.Nat.at_most(n, 139) == Nat.is_le(n, 139n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k138(p)

def AtMost.k140(+n: Nat) -> {Wasm.Nat.at_most(n, 140) == Nat.is_le(n, 140n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k139(p)

def AtMost.k141(+n: Nat) -> {Wasm.Nat.at_most(n, 141) == Nat.is_le(n, 141n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k140(p)

def AtMost.k142(+n: Nat) -> {Wasm.Nat.at_most(n, 142) == Nat.is_le(n, 142n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k141(p)

def AtMost.k143(+n: Nat) -> {Wasm.Nat.at_most(n, 143) == Nat.is_le(n, 143n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k142(p)

def AtMost.k144(+n: Nat) -> {Wasm.Nat.at_most(n, 144) == Nat.is_le(n, 144n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k143(p)

def AtMost.k145(+n: Nat) -> {Wasm.Nat.at_most(n, 145) == Nat.is_le(n, 145n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k144(p)

def AtMost.k146(+n: Nat) -> {Wasm.Nat.at_most(n, 146) == Nat.is_le(n, 146n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k145(p)

def AtMost.k147(+n: Nat) -> {Wasm.Nat.at_most(n, 147) == Nat.is_le(n, 147n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k146(p)

def AtMost.k148(+n: Nat) -> {Wasm.Nat.at_most(n, 148) == Nat.is_le(n, 148n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k147(p)

def AtMost.k149(+n: Nat) -> {Wasm.Nat.at_most(n, 149) == Nat.is_le(n, 149n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k148(p)

def AtMost.k150(+n: Nat) -> {Wasm.Nat.at_most(n, 150) == Nat.is_le(n, 150n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k149(p)

def AtMost.k151(+n: Nat) -> {Wasm.Nat.at_most(n, 151) == Nat.is_le(n, 151n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k150(p)

def AtMost.k152(+n: Nat) -> {Wasm.Nat.at_most(n, 152) == Nat.is_le(n, 152n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k151(p)

def AtMost.k153(+n: Nat) -> {Wasm.Nat.at_most(n, 153) == Nat.is_le(n, 153n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k152(p)

def AtMost.k154(+n: Nat) -> {Wasm.Nat.at_most(n, 154) == Nat.is_le(n, 154n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k153(p)

def AtMost.k155(+n: Nat) -> {Wasm.Nat.at_most(n, 155) == Nat.is_le(n, 155n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k154(p)

def AtMost.k156(+n: Nat) -> {Wasm.Nat.at_most(n, 156) == Nat.is_le(n, 156n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k155(p)

def AtMost.k157(+n: Nat) -> {Wasm.Nat.at_most(n, 157) == Nat.is_le(n, 157n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k156(p)

def AtMost.k158(+n: Nat) -> {Wasm.Nat.at_most(n, 158) == Nat.is_le(n, 158n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k157(p)

def AtMost.k159(+n: Nat) -> {Wasm.Nat.at_most(n, 159) == Nat.is_le(n, 159n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k158(p)

def AtMost.k160(+n: Nat) -> {Wasm.Nat.at_most(n, 160) == Nat.is_le(n, 160n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k159(p)

def AtMost.k161(+n: Nat) -> {Wasm.Nat.at_most(n, 161) == Nat.is_le(n, 161n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k160(p)

def AtMost.k162(+n: Nat) -> {Wasm.Nat.at_most(n, 162) == Nat.is_le(n, 162n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k161(p)

def AtMost.k163(+n: Nat) -> {Wasm.Nat.at_most(n, 163) == Nat.is_le(n, 163n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k162(p)

def AtMost.k164(+n: Nat) -> {Wasm.Nat.at_most(n, 164) == Nat.is_le(n, 164n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k163(p)

def AtMost.k165(+n: Nat) -> {Wasm.Nat.at_most(n, 165) == Nat.is_le(n, 165n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k164(p)

def AtMost.k166(+n: Nat) -> {Wasm.Nat.at_most(n, 166) == Nat.is_le(n, 166n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k165(p)

def AtMost.k167(+n: Nat) -> {Wasm.Nat.at_most(n, 167) == Nat.is_le(n, 167n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k166(p)

def AtMost.k168(+n: Nat) -> {Wasm.Nat.at_most(n, 168) == Nat.is_le(n, 168n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k167(p)

def AtMost.k169(+n: Nat) -> {Wasm.Nat.at_most(n, 169) == Nat.is_le(n, 169n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k168(p)

def AtMost.k170(+n: Nat) -> {Wasm.Nat.at_most(n, 170) == Nat.is_le(n, 170n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k169(p)

def AtMost.k171(+n: Nat) -> {Wasm.Nat.at_most(n, 171) == Nat.is_le(n, 171n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k170(p)

def AtMost.k172(+n: Nat) -> {Wasm.Nat.at_most(n, 172) == Nat.is_le(n, 172n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k171(p)

def AtMost.k173(+n: Nat) -> {Wasm.Nat.at_most(n, 173) == Nat.is_le(n, 173n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k172(p)

def AtMost.k174(+n: Nat) -> {Wasm.Nat.at_most(n, 174) == Nat.is_le(n, 174n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k173(p)

def AtMost.k175(+n: Nat) -> {Wasm.Nat.at_most(n, 175) == Nat.is_le(n, 175n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k174(p)

def AtMost.k176(+n: Nat) -> {Wasm.Nat.at_most(n, 176) == Nat.is_le(n, 176n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k175(p)

def AtMost.k177(+n: Nat) -> {Wasm.Nat.at_most(n, 177) == Nat.is_le(n, 177n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k176(p)

def AtMost.k178(+n: Nat) -> {Wasm.Nat.at_most(n, 178) == Nat.is_le(n, 178n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k177(p)

def AtMost.k179(+n: Nat) -> {Wasm.Nat.at_most(n, 179) == Nat.is_le(n, 179n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k178(p)

def AtMost.k180(+n: Nat) -> {Wasm.Nat.at_most(n, 180) == Nat.is_le(n, 180n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k179(p)

def AtMost.k181(+n: Nat) -> {Wasm.Nat.at_most(n, 181) == Nat.is_le(n, 181n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k180(p)

def AtMost.k182(+n: Nat) -> {Wasm.Nat.at_most(n, 182) == Nat.is_le(n, 182n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k181(p)

def AtMost.k183(+n: Nat) -> {Wasm.Nat.at_most(n, 183) == Nat.is_le(n, 183n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k182(p)

def AtMost.k184(+n: Nat) -> {Wasm.Nat.at_most(n, 184) == Nat.is_le(n, 184n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k183(p)

def AtMost.k185(+n: Nat) -> {Wasm.Nat.at_most(n, 185) == Nat.is_le(n, 185n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k184(p)

def AtMost.k186(+n: Nat) -> {Wasm.Nat.at_most(n, 186) == Nat.is_le(n, 186n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k185(p)

def AtMost.k187(+n: Nat) -> {Wasm.Nat.at_most(n, 187) == Nat.is_le(n, 187n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k186(p)

def AtMost.k188(+n: Nat) -> {Wasm.Nat.at_most(n, 188) == Nat.is_le(n, 188n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k187(p)

def AtMost.k189(+n: Nat) -> {Wasm.Nat.at_most(n, 189) == Nat.is_le(n, 189n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k188(p)

def AtMost.k190(+n: Nat) -> {Wasm.Nat.at_most(n, 190) == Nat.is_le(n, 190n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k189(p)

def AtMost.k191(+n: Nat) -> {Wasm.Nat.at_most(n, 191) == Nat.is_le(n, 191n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k190(p)

def AtMost.k192(+n: Nat) -> {Wasm.Nat.at_most(n, 192) == Nat.is_le(n, 192n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k191(p)

def AtMost.k193(+n: Nat) -> {Wasm.Nat.at_most(n, 193) == Nat.is_le(n, 193n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k192(p)

def AtMost.k194(+n: Nat) -> {Wasm.Nat.at_most(n, 194) == Nat.is_le(n, 194n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k193(p)

def AtMost.k195(+n: Nat) -> {Wasm.Nat.at_most(n, 195) == Nat.is_le(n, 195n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k194(p)

def AtMost.k196(+n: Nat) -> {Wasm.Nat.at_most(n, 196) == Nat.is_le(n, 196n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k195(p)

def AtMost.k197(+n: Nat) -> {Wasm.Nat.at_most(n, 197) == Nat.is_le(n, 197n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k196(p)

def AtMost.k198(+n: Nat) -> {Wasm.Nat.at_most(n, 198) == Nat.is_le(n, 198n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k197(p)

def AtMost.k199(+n: Nat) -> {Wasm.Nat.at_most(n, 199) == Nat.is_le(n, 199n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k198(p)

def AtMost.k200(+n: Nat) -> {Wasm.Nat.at_most(n, 200) == Nat.is_le(n, 200n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k199(p)

def AtMost.k201(+n: Nat) -> {Wasm.Nat.at_most(n, 201) == Nat.is_le(n, 201n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k200(p)

def AtMost.k202(+n: Nat) -> {Wasm.Nat.at_most(n, 202) == Nat.is_le(n, 202n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k201(p)

def AtMost.k203(+n: Nat) -> {Wasm.Nat.at_most(n, 203) == Nat.is_le(n, 203n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k202(p)

def AtMost.k204(+n: Nat) -> {Wasm.Nat.at_most(n, 204) == Nat.is_le(n, 204n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k203(p)

def AtMost.k205(+n: Nat) -> {Wasm.Nat.at_most(n, 205) == Nat.is_le(n, 205n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k204(p)

def AtMost.k206(+n: Nat) -> {Wasm.Nat.at_most(n, 206) == Nat.is_le(n, 206n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k205(p)

def AtMost.k207(+n: Nat) -> {Wasm.Nat.at_most(n, 207) == Nat.is_le(n, 207n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k206(p)

def AtMost.k208(+n: Nat) -> {Wasm.Nat.at_most(n, 208) == Nat.is_le(n, 208n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k207(p)

def AtMost.k209(+n: Nat) -> {Wasm.Nat.at_most(n, 209) == Nat.is_le(n, 209n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k208(p)

def AtMost.k210(+n: Nat) -> {Wasm.Nat.at_most(n, 210) == Nat.is_le(n, 210n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k209(p)

def AtMost.k211(+n: Nat) -> {Wasm.Nat.at_most(n, 211) == Nat.is_le(n, 211n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k210(p)

def AtMost.k212(+n: Nat) -> {Wasm.Nat.at_most(n, 212) == Nat.is_le(n, 212n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k211(p)

def AtMost.k213(+n: Nat) -> {Wasm.Nat.at_most(n, 213) == Nat.is_le(n, 213n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k212(p)

def AtMost.k214(+n: Nat) -> {Wasm.Nat.at_most(n, 214) == Nat.is_le(n, 214n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k213(p)

def AtMost.k215(+n: Nat) -> {Wasm.Nat.at_most(n, 215) == Nat.is_le(n, 215n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k214(p)

def AtMost.k216(+n: Nat) -> {Wasm.Nat.at_most(n, 216) == Nat.is_le(n, 216n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k215(p)

def AtMost.k217(+n: Nat) -> {Wasm.Nat.at_most(n, 217) == Nat.is_le(n, 217n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k216(p)

def AtMost.k218(+n: Nat) -> {Wasm.Nat.at_most(n, 218) == Nat.is_le(n, 218n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k217(p)

def AtMost.k219(+n: Nat) -> {Wasm.Nat.at_most(n, 219) == Nat.is_le(n, 219n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k218(p)

def AtMost.k220(+n: Nat) -> {Wasm.Nat.at_most(n, 220) == Nat.is_le(n, 220n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k219(p)

def AtMost.k221(+n: Nat) -> {Wasm.Nat.at_most(n, 221) == Nat.is_le(n, 221n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k220(p)

def AtMost.k222(+n: Nat) -> {Wasm.Nat.at_most(n, 222) == Nat.is_le(n, 222n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k221(p)

def AtMost.k223(+n: Nat) -> {Wasm.Nat.at_most(n, 223) == Nat.is_le(n, 223n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k222(p)

def AtMost.k224(+n: Nat) -> {Wasm.Nat.at_most(n, 224) == Nat.is_le(n, 224n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k223(p)

def AtMost.k225(+n: Nat) -> {Wasm.Nat.at_most(n, 225) == Nat.is_le(n, 225n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k224(p)

def AtMost.k226(+n: Nat) -> {Wasm.Nat.at_most(n, 226) == Nat.is_le(n, 226n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k225(p)

def AtMost.k227(+n: Nat) -> {Wasm.Nat.at_most(n, 227) == Nat.is_le(n, 227n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k226(p)

def AtMost.k228(+n: Nat) -> {Wasm.Nat.at_most(n, 228) == Nat.is_le(n, 228n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k227(p)

def AtMost.k229(+n: Nat) -> {Wasm.Nat.at_most(n, 229) == Nat.is_le(n, 229n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k228(p)

def AtMost.k230(+n: Nat) -> {Wasm.Nat.at_most(n, 230) == Nat.is_le(n, 230n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k229(p)

def AtMost.k231(+n: Nat) -> {Wasm.Nat.at_most(n, 231) == Nat.is_le(n, 231n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k230(p)

def AtMost.k232(+n: Nat) -> {Wasm.Nat.at_most(n, 232) == Nat.is_le(n, 232n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k231(p)

def AtMost.k233(+n: Nat) -> {Wasm.Nat.at_most(n, 233) == Nat.is_le(n, 233n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k232(p)

def AtMost.k234(+n: Nat) -> {Wasm.Nat.at_most(n, 234) == Nat.is_le(n, 234n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k233(p)

def AtMost.k235(+n: Nat) -> {Wasm.Nat.at_most(n, 235) == Nat.is_le(n, 235n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k234(p)

def AtMost.k236(+n: Nat) -> {Wasm.Nat.at_most(n, 236) == Nat.is_le(n, 236n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k235(p)

def AtMost.k237(+n: Nat) -> {Wasm.Nat.at_most(n, 237) == Nat.is_le(n, 237n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k236(p)

def AtMost.k238(+n: Nat) -> {Wasm.Nat.at_most(n, 238) == Nat.is_le(n, 238n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k237(p)

def AtMost.k239(+n: Nat) -> {Wasm.Nat.at_most(n, 239) == Nat.is_le(n, 239n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k238(p)

def AtMost.k240(+n: Nat) -> {Wasm.Nat.at_most(n, 240) == Nat.is_le(n, 240n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k239(p)

def AtMost.k241(+n: Nat) -> {Wasm.Nat.at_most(n, 241) == Nat.is_le(n, 241n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k240(p)

def AtMost.k242(+n: Nat) -> {Wasm.Nat.at_most(n, 242) == Nat.is_le(n, 242n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k241(p)

def AtMost.k243(+n: Nat) -> {Wasm.Nat.at_most(n, 243) == Nat.is_le(n, 243n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k242(p)

def AtMost.k244(+n: Nat) -> {Wasm.Nat.at_most(n, 244) == Nat.is_le(n, 244n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k243(p)

def AtMost.k245(+n: Nat) -> {Wasm.Nat.at_most(n, 245) == Nat.is_le(n, 245n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k244(p)

def AtMost.k246(+n: Nat) -> {Wasm.Nat.at_most(n, 246) == Nat.is_le(n, 246n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k245(p)

def AtMost.k247(+n: Nat) -> {Wasm.Nat.at_most(n, 247) == Nat.is_le(n, 247n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k246(p)

def AtMost.k248(+n: Nat) -> {Wasm.Nat.at_most(n, 248) == Nat.is_le(n, 248n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k247(p)

def AtMost.k249(+n: Nat) -> {Wasm.Nat.at_most(n, 249) == Nat.is_le(n, 249n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k248(p)

def AtMost.k250(+n: Nat) -> {Wasm.Nat.at_most(n, 250) == Nat.is_le(n, 250n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k249(p)

def AtMost.k251(+n: Nat) -> {Wasm.Nat.at_most(n, 251) == Nat.is_le(n, 251n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k250(p)

def AtMost.k252(+n: Nat) -> {Wasm.Nat.at_most(n, 252) == Nat.is_le(n, 252n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k251(p)

def AtMost.k253(+n: Nat) -> {Wasm.Nat.at_most(n, 253) == Nat.is_le(n, 253n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k252(p)

def AtMost.k254(+n: Nat) -> {Wasm.Nat.at_most(n, 254) == Nat.is_le(n, 254n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k253(p)

def AtMost.k255(+n: Nat) -> {Wasm.Nat.at_most(n, 255) == Nat.is_le(n, 255n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      AtMost.k254(p)

def L.Name.is_eq(+a_1: List<&2, Nat>, +b_2: List<&2, Nat>, +ks: List<&2, Fun.Fr>) ->
  Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Name.is_eq(), [FM.Enc.name(a_1), FM.Enc.name(b_2)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(a_1, b_2)), ks}}):
  match a_1:
    case Nil{}:
      match b_2:
        case Nil{}:
          (3n, {==})
        case Con{+y_3, +ys_4}:
          (3n, {==})
    case Con{+x_5, +xs_6}:
      match b_2:
        case Nil{}:
          (3n, {==})
        case Con{+y_7, +ys_8}:
          FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Name.is_eq(), [FM.Enc.name(Con{x_5, xs_6}), FM.Enc.name(Con{y_7, ys_8})], ks}}, Fun.F.iter(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Name.is_eq(), [FM.Enc.name(Con{x_5, xs_6}), FM.Enc.name(Con{y_7, ys_8})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(Con{x_5, xs_6}, Con{y_7, ys_8})), ks}},
            FP.Reach.steps(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Name.is_eq(), [FM.Enc.name(Con{x_5, xs_6}), FM.Enc.name(Con{y_7, ys_8})], ks}}),
            Shared.Bool.elim(Nat.is_eq(x_5, y_7), bq => Fun.Reach(Code.prog(), Bool.pick(Fun.Step, bq, Fun.Step.go{Fun.S.run{Code.F.Name.is_eq.k1(), [FM.Enc.name(ys_8), FM.Enc.nat(y_7), FM.Enc.name(xs_6), FM.Enc.nat(x_5), FM.Enc.name(Con{x_5, xs_6}), FM.Enc.name(Con{y_7, ys_8})], ks}}, Fun.Step.go{Fun.S.run{Code.F.Name.is_eq.k2(), [FM.Enc.name(ys_8), FM.Enc.nat(y_7), FM.Enc.name(xs_6), FM.Enc.nat(x_5), FM.Enc.name(Con{x_5, xs_6}), FM.Enc.name(Con{y_7, ys_8})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Bool.and(bq, Source.Name.is_eq(xs_6, ys_8))), ks}}),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Name.is_eq.k1(), [FM.Enc.name(ys_8), FM.Enc.nat(y_7), FM.Enc.name(xs_6), FM.Enc.nat(x_5), FM.Enc.name(Con{x_5, xs_6}), FM.Enc.name(Con{y_7, ys_8})], ks}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Name.is_eq.k1(), [FM.Enc.name(ys_8), FM.Enc.nat(y_7), FM.Enc.name(xs_6), FM.Enc.nat(x_5), FM.Enc.name(Con{x_5, xs_6}), FM.Enc.name(Con{y_7, ys_8})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Bool.and(True{}, Source.Name.is_eq(xs_6, ys_8))), ks}},
            FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Name.is_eq.k1(), [FM.Enc.name(ys_8), FM.Enc.nat(y_7), FM.Enc.name(xs_6), FM.Enc.nat(x_5), FM.Enc.name(Con{x_5, xs_6}), FM.Enc.name(Con{y_7, ys_8})], ks}}),
            L.Name.is_eq(xs_6, ys_8, ks)),
            (1n, {==})))

def L.Book.get(+bk_9: List<&2, Source.Def>, +k_10: List<&2, Nat>, +ks: List<&2, Fun.Fr>) ->
  Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Book.get(), [FM.Enc.book(bk_9), FM.Enc.name(k_10)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.mdef(Source.Book.get(bk_9, k_10)), ks}}):
  match bk_9:
    case Nil{}:
      (2n, {==})
    case Con{+d_11, +rest_12}:
      match d_11:
        case Source.Def{+n_13, +t_14, +v_15, +o_16}:
          FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Book.get(), [FM.Enc.book(Con{Source.Def{n_13, t_14, v_15, o_16}, rest_12}), FM.Enc.name(k_10)], ks}}, Fun.F.iter(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Book.get(), [FM.Enc.book(Con{Source.Def{n_13, t_14, v_15, o_16}, rest_12}), FM.Enc.name(k_10)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.mdef(Source.Book.get(Con{Source.Def{n_13, t_14, v_15, o_16}, rest_12}, k_10)), ks}},
            FP.Reach.steps(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Book.get(), [FM.Enc.book(Con{Source.Def{n_13, t_14, v_15, o_16}, rest_12}), FM.Enc.name(k_10)], ks}}),
            FP.Reach.trans(Code.prog(), Fun.F.iter(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Book.get(), [FM.Enc.book(Con{Source.Def{n_13, t_14, v_15, o_16}, rest_12}), FM.Enc.name(k_10)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(n_13, k_10)), Con{Fun.Fr{Code.F.Book.get.k1(), [FM.Enc.term(v_15), FM.Enc.name(n_13), FM.Enc.book(rest_12), FM.Enc.def(Source.Def{n_13, t_14, v_15, o_16}), FM.Enc.book(Con{Source.Def{n_13, t_14, v_15, o_16}, rest_12}), FM.Enc.name(k_10)]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.mdef(Source.Book.get(Con{Source.Def{n_13, t_14, v_15, o_16}, rest_12}, k_10)), ks}},
            L.Name.is_eq(n_13, k_10, Con{Fun.Fr{Code.F.Book.get.k1(), [FM.Enc.term(v_15), FM.Enc.name(n_13), FM.Enc.book(rest_12), FM.Enc.def(Source.Def{n_13, t_14, v_15, o_16}), FM.Enc.book(Con{Source.Def{n_13, t_14, v_15, o_16}, rest_12}), FM.Enc.name(k_10)]}, ks}),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(n_13, k_10)), Con{Fun.Fr{Code.F.Book.get.k1(), [FM.Enc.term(v_15), FM.Enc.name(n_13), FM.Enc.book(rest_12), FM.Enc.def(Source.Def{n_13, t_14, v_15, o_16}), FM.Enc.book(Con{Source.Def{n_13, t_14, v_15, o_16}, rest_12}), FM.Enc.name(k_10)]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(n_13, k_10)), Con{Fun.Fr{Code.F.Book.get.k1(), [FM.Enc.term(v_15), FM.Enc.name(n_13), FM.Enc.book(rest_12), FM.Enc.def(Source.Def{n_13, t_14, v_15, o_16}), FM.Enc.book(Con{Source.Def{n_13, t_14, v_15, o_16}, rest_12}), FM.Enc.name(k_10)]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.mdef(Source.Book.get(Con{Source.Def{n_13, t_14, v_15, o_16}, rest_12}, k_10)), ks}},
            FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(n_13, k_10)), Con{Fun.Fr{Code.F.Book.get.k1(), [FM.Enc.term(v_15), FM.Enc.name(n_13), FM.Enc.book(rest_12), FM.Enc.def(Source.Def{n_13, t_14, v_15, o_16}), FM.Enc.book(Con{Source.Def{n_13, t_14, v_15, o_16}, rest_12}), FM.Enc.name(k_10)]}, ks}}}),
            Elim.Bool(Source.Name.is_eq(n_13, k_10), m1 => Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Book.get.k1(), [FM.Enc.bool(m1), FM.Enc.term(v_15), FM.Enc.name(n_13), FM.Enc.book(rest_12), FM.Enc.def(Source.Def{n_13, t_14, v_15, o_16}), FM.Enc.book(Con{Source.Def{n_13, t_14, v_15, o_16}, rest_12}), FM.Enc.name(k_10)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.mdef(Source.Bool.lazy(Maybe<&2, Source.Def>, m1, u => Some{Source.Def{n_13, t_14, v_15, o_16}}, u => Source.Book.get(rest_12, k_10))), ks}}),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Book.get.k1(), [FM.Enc.bool(False{}), FM.Enc.term(v_15), FM.Enc.name(n_13), FM.Enc.book(rest_12), FM.Enc.def(Source.Def{n_13, t_14, v_15, o_16}), FM.Enc.book(Con{Source.Def{n_13, t_14, v_15, o_16}, rest_12}), FM.Enc.name(k_10)], ks}}, Fun.F.iter(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Book.get.k1(), [FM.Enc.bool(False{}), FM.Enc.term(v_15), FM.Enc.name(n_13), FM.Enc.book(rest_12), FM.Enc.def(Source.Def{n_13, t_14, v_15, o_16}), FM.Enc.book(Con{Source.Def{n_13, t_14, v_15, o_16}, rest_12}), FM.Enc.name(k_10)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.mdef(Source.Bool.lazy(Maybe<&2, Source.Def>, False{}, u => Some{Source.Def{n_13, t_14, v_15, o_16}}, u => Source.Book.get(rest_12, k_10))), ks}},
            FP.Reach.steps(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Book.get.k1(), [FM.Enc.bool(False{}), FM.Enc.term(v_15), FM.Enc.name(n_13), FM.Enc.book(rest_12), FM.Enc.def(Source.Def{n_13, t_14, v_15, o_16}), FM.Enc.book(Con{Source.Def{n_13, t_14, v_15, o_16}, rest_12}), FM.Enc.name(k_10)], ks}}),
            L.Book.get(rest_12, k_10, ks)),
            (3n, {==})))))

def L.Env.get(+e_18: Machine.Val, +i_19: Nat, +ks: List<&2, Fun.Fr>) ->
  Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.get(), [FM.Enc.val(e_18), FM.Enc.nat(i_19)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.val(Machine.Env.get(e_18, i_19)), ks}}):
  match e_18:
    case Machine.Val.nil{}:
      (4n, {==})
    case Machine.Val.env{+x_20, +rest_21}:
      match i_19:
        case 0n:
          (3n, {==})
        case 1n+j_22:
          FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.get(), [FM.Enc.val(Machine.Val.env{x_20, rest_21}), FM.Enc.nat(1n+j_22)], ks}}, Fun.F.iter(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.get(), [FM.Enc.val(Machine.Val.env{x_20, rest_21}), FM.Enc.nat(1n+j_22)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.val(Machine.Env.get(Machine.Val.env{x_20, rest_21}, 1n+j_22)), ks}},
            FP.Reach.steps(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.get(), [FM.Enc.val(Machine.Val.env{x_20, rest_21}), FM.Enc.nat(1n+j_22)], ks}}),
            L.Env.get(rest_21, j_22, ks))
    case Machine.Val.arg{+_q_23, +_x_24, +_rest_25}:
      (4n, {==})
    case Machine.Val.clo{+_t_26, +_e_27}:
      (4n, {==})
    case Machine.Val.lab{+_k_28}:
      (4n, {==})
    case Machine.Val.rfl{}:
      (4n, {==})
    case Machine.Val.tup{+_q_29, +_a_30, +_b_31}:
      (4n, {==})
    case Machine.Val.call{+_k_32, +_xs_33}:
      (4n, {==})

def L.Env.find(+e_34: Machine.Val, +i_35: Nat, +ks: List<&2, Fun.Fr>) ->
  Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(e_34), FM.Enc.nat(i_35)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.look(Machine.Env.find(e_34, i_35)), ks}}):
  match e_34:
    case Machine.Val.nil{}:
      (3n, {==})
    case Machine.Val.env{+x_36, +rest_37}:
      match x_36:
        case Machine.Val.nil{}:
          match i_35:
            case 0n:
              (5n, {==})
            case 1n+j_38:
              FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.nil{}, rest_37}), FM.Enc.nat(1n+j_38)], ks}}, Fun.F.iter(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.nil{}, rest_37}), FM.Enc.nat(1n+j_38)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.look(Machine.Env.find(Machine.Val.env{Machine.Val.nil{}, rest_37}, 1n+j_38)), ks}},
                FP.Reach.steps(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.nil{}, rest_37}), FM.Enc.nat(1n+j_38)], ks}}),
                L.Env.find(rest_37, j_38, ks))
        case Machine.Val.env{+_x_39, +_rest_40}:
          match i_35:
            case 0n:
              (5n, {==})
            case 1n+j_41:
              FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.env{_x_39, _rest_40}, rest_37}), FM.Enc.nat(1n+j_41)], ks}}, Fun.F.iter(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.env{_x_39, _rest_40}, rest_37}), FM.Enc.nat(1n+j_41)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.look(Machine.Env.find(Machine.Val.env{Machine.Val.env{_x_39, _rest_40}, rest_37}, 1n+j_41)), ks}},
                FP.Reach.steps(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.env{_x_39, _rest_40}, rest_37}), FM.Enc.nat(1n+j_41)], ks}}),
                L.Env.find(rest_37, j_41, ks))
        case Machine.Val.arg{+_q_42, +_x_43, +_rest_44}:
          match i_35:
            case 0n:
              (5n, {==})
            case 1n+j_45:
              FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.arg{_q_42, _x_43, _rest_44}, rest_37}), FM.Enc.nat(1n+j_45)], ks}}, Fun.F.iter(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.arg{_q_42, _x_43, _rest_44}, rest_37}), FM.Enc.nat(1n+j_45)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.look(Machine.Env.find(Machine.Val.env{Machine.Val.arg{_q_42, _x_43, _rest_44}, rest_37}, 1n+j_45)), ks}},
                FP.Reach.steps(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.arg{_q_42, _x_43, _rest_44}, rest_37}), FM.Enc.nat(1n+j_45)], ks}}),
                L.Env.find(rest_37, j_45, ks))
        case Machine.Val.clo{+t_46, +e2_47}:
          match t_46:
            case Source.Term.Var{+j0_48}:
              match i_35:
                case 0n:
                  FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.Var{j0_48}, e2_47}, rest_37}), FM.Enc.nat(0n)], ks}}, Fun.F.iter(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.Var{j0_48}, e2_47}, rest_37}), FM.Enc.nat(0n)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.look(Machine.Env.find(Machine.Val.env{Machine.Val.clo{Source.Term.Var{j0_48}, e2_47}, rest_37}, 0n)), ks}},
                    FP.Reach.steps(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.Var{j0_48}, e2_47}, rest_37}), FM.Enc.nat(0n)], ks}}),
                    L.Env.find(e2_47, j0_48, ks))
                case 1n+j_49:
                  FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.Var{j0_48}, e2_47}, rest_37}), FM.Enc.nat(1n+j_49)], ks}}, Fun.F.iter(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.Var{j0_48}, e2_47}, rest_37}), FM.Enc.nat(1n+j_49)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.look(Machine.Env.find(Machine.Val.env{Machine.Val.clo{Source.Term.Var{j0_48}, e2_47}, rest_37}, 1n+j_49)), ks}},
                    FP.Reach.steps(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.Var{j0_48}, e2_47}, rest_37}), FM.Enc.nat(1n+j_49)], ks}}),
                    L.Env.find(rest_37, j_49, ks))
            case Source.Term.Ref{+_k_50}:
              match i_35:
                case 0n:
                  (6n, {==})
                case 1n+j_51:
                  FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.Ref{_k_50}, e2_47}, rest_37}), FM.Enc.nat(1n+j_51)], ks}}, Fun.F.iter(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.Ref{_k_50}, e2_47}, rest_37}), FM.Enc.nat(1n+j_51)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.look(Machine.Env.find(Machine.Val.env{Machine.Val.clo{Source.Term.Ref{_k_50}, e2_47}, rest_37}, 1n+j_51)), ks}},
                    FP.Reach.steps(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.Ref{_k_50}, e2_47}, rest_37}), FM.Enc.nat(1n+j_51)], ks}}),
                    L.Env.find(rest_37, j_51, ks))
            case Source.Term.Ann{+_x_52, +_t_53}:
              match i_35:
                case 0n:
                  (6n, {==})
                case 1n+j_54:
                  FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.Ann{_x_52, _t_53}, e2_47}, rest_37}), FM.Enc.nat(1n+j_54)], ks}}, Fun.F.iter(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.Ann{_x_52, _t_53}, e2_47}, rest_37}), FM.Enc.nat(1n+j_54)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.look(Machine.Env.find(Machine.Val.env{Machine.Val.clo{Source.Term.Ann{_x_52, _t_53}, e2_47}, rest_37}, 1n+j_54)), ks}},
                    FP.Reach.steps(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.Ann{_x_52, _t_53}, e2_47}, rest_37}), FM.Enc.nat(1n+j_54)], ks}}),
                    L.Env.find(rest_37, j_54, ks))
            case Source.Term.Let{+_q_55, +_v_56, +_f_57}:
              match i_35:
                case 0n:
                  (6n, {==})
                case 1n+j_58:
                  FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.Let{_q_55, _v_56, _f_57}, e2_47}, rest_37}), FM.Enc.nat(1n+j_58)], ks}}, Fun.F.iter(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.Let{_q_55, _v_56, _f_57}, e2_47}, rest_37}), FM.Enc.nat(1n+j_58)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.look(Machine.Env.find(Machine.Val.env{Machine.Val.clo{Source.Term.Let{_q_55, _v_56, _f_57}, e2_47}, rest_37}, 1n+j_58)), ks}},
                    FP.Reach.steps(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.Let{_q_55, _v_56, _f_57}, e2_47}, rest_37}), FM.Enc.nat(1n+j_58)], ks}}),
                    L.Env.find(rest_37, j_58, ks))
            case Source.Term.Typ{+_q_59}:
              match i_35:
                case 0n:
                  (6n, {==})
                case 1n+j_60:
                  FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.Typ{_q_59}, e2_47}, rest_37}), FM.Enc.nat(1n+j_60)], ks}}, Fun.F.iter(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.Typ{_q_59}, e2_47}, rest_37}), FM.Enc.nat(1n+j_60)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.look(Machine.Env.find(Machine.Val.env{Machine.Val.clo{Source.Term.Typ{_q_59}, e2_47}, rest_37}, 1n+j_60)), ks}},
                    FP.Reach.steps(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.Typ{_q_59}, e2_47}, rest_37}), FM.Enc.nat(1n+j_60)], ks}}),
                    L.Env.find(rest_37, j_60, ks))
            case Source.Term.Min{+_a_61, +_b_62}:
              match i_35:
                case 0n:
                  (6n, {==})
                case 1n+j_63:
                  FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.Min{_a_61, _b_62}, e2_47}, rest_37}), FM.Enc.nat(1n+j_63)], ks}}, Fun.F.iter(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.Min{_a_61, _b_62}, e2_47}, rest_37}), FM.Enc.nat(1n+j_63)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.look(Machine.Env.find(Machine.Val.env{Machine.Val.clo{Source.Term.Min{_a_61, _b_62}, e2_47}, rest_37}, 1n+j_63)), ks}},
                    FP.Reach.steps(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.Min{_a_61, _b_62}, e2_47}, rest_37}), FM.Enc.nat(1n+j_63)], ks}}),
                    L.Env.find(rest_37, j_63, ks))
            case Source.Term.All{+_q_64, +_a_65, +_b_66}:
              match i_35:
                case 0n:
                  (6n, {==})
                case 1n+j_67:
                  FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.All{_q_64, _a_65, _b_66}, e2_47}, rest_37}), FM.Enc.nat(1n+j_67)], ks}}, Fun.F.iter(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.All{_q_64, _a_65, _b_66}, e2_47}, rest_37}), FM.Enc.nat(1n+j_67)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.look(Machine.Env.find(Machine.Val.env{Machine.Val.clo{Source.Term.All{_q_64, _a_65, _b_66}, e2_47}, rest_37}, 1n+j_67)), ks}},
                    FP.Reach.steps(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.All{_q_64, _a_65, _b_66}, e2_47}, rest_37}), FM.Enc.nat(1n+j_67)], ks}}),
                    L.Env.find(rest_37, j_67, ks))
            case Source.Term.Lam{+_q_68, +_f_69}:
              match i_35:
                case 0n:
                  (6n, {==})
                case 1n+j_70:
                  FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.Lam{_q_68, _f_69}, e2_47}, rest_37}), FM.Enc.nat(1n+j_70)], ks}}, Fun.F.iter(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.Lam{_q_68, _f_69}, e2_47}, rest_37}), FM.Enc.nat(1n+j_70)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.look(Machine.Env.find(Machine.Val.env{Machine.Val.clo{Source.Term.Lam{_q_68, _f_69}, e2_47}, rest_37}, 1n+j_70)), ks}},
                    FP.Reach.steps(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.Lam{_q_68, _f_69}, e2_47}, rest_37}), FM.Enc.nat(1n+j_70)], ks}}),
                    L.Env.find(rest_37, j_70, ks))
            case Source.Term.App{+_q_71, +_f_72, +_x_73}:
              match i_35:
                case 0n:
                  (6n, {==})
                case 1n+j_74:
                  FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.App{_q_71, _f_72, _x_73}, e2_47}, rest_37}), FM.Enc.nat(1n+j_74)], ks}}, Fun.F.iter(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.App{_q_71, _f_72, _x_73}, e2_47}, rest_37}), FM.Enc.nat(1n+j_74)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.look(Machine.Env.find(Machine.Val.env{Machine.Val.clo{Source.Term.App{_q_71, _f_72, _x_73}, e2_47}, rest_37}, 1n+j_74)), ks}},
                    FP.Reach.steps(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.App{_q_71, _f_72, _x_73}, e2_47}, rest_37}), FM.Enc.nat(1n+j_74)], ks}}),
                    L.Env.find(rest_37, j_74, ks))
            case Source.Term.Sig{+_q_75, +_a_76, +_b_77}:
              match i_35:
                case 0n:
                  (6n, {==})
                case 1n+j_78:
                  FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.Sig{_q_75, _a_76, _b_77}, e2_47}, rest_37}), FM.Enc.nat(1n+j_78)], ks}}, Fun.F.iter(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.Sig{_q_75, _a_76, _b_77}, e2_47}, rest_37}), FM.Enc.nat(1n+j_78)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.look(Machine.Env.find(Machine.Val.env{Machine.Val.clo{Source.Term.Sig{_q_75, _a_76, _b_77}, e2_47}, rest_37}, 1n+j_78)), ks}},
                    FP.Reach.steps(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.Sig{_q_75, _a_76, _b_77}, e2_47}, rest_37}), FM.Enc.nat(1n+j_78)], ks}}),
                    L.Env.find(rest_37, j_78, ks))
            case Source.Term.Tup{+_q_79, +_a_80, +_b_81}:
              match i_35:
                case 0n:
                  (6n, {==})
                case 1n+j_82:
                  FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.Tup{_q_79, _a_80, _b_81}, e2_47}, rest_37}), FM.Enc.nat(1n+j_82)], ks}}, Fun.F.iter(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.Tup{_q_79, _a_80, _b_81}, e2_47}, rest_37}), FM.Enc.nat(1n+j_82)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.look(Machine.Env.find(Machine.Val.env{Machine.Val.clo{Source.Term.Tup{_q_79, _a_80, _b_81}, e2_47}, rest_37}, 1n+j_82)), ks}},
                    FP.Reach.steps(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.Tup{_q_79, _a_80, _b_81}, e2_47}, rest_37}), FM.Enc.nat(1n+j_82)], ks}}),
                    L.Env.find(rest_37, j_82, ks))
            case Source.Term.Prj{+_h_83}:
              match i_35:
                case 0n:
                  (6n, {==})
                case 1n+j_84:
                  FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.Prj{_h_83}, e2_47}, rest_37}), FM.Enc.nat(1n+j_84)], ks}}, Fun.F.iter(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.Prj{_h_83}, e2_47}, rest_37}), FM.Enc.nat(1n+j_84)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.look(Machine.Env.find(Machine.Val.env{Machine.Val.clo{Source.Term.Prj{_h_83}, e2_47}, rest_37}, 1n+j_84)), ks}},
                    FP.Reach.steps(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.Prj{_h_83}, e2_47}, rest_37}), FM.Enc.nat(1n+j_84)], ks}}),
                    L.Env.find(rest_37, j_84, ks))
            case Source.Term.Enu{+_ks_85}:
              match i_35:
                case 0n:
                  (6n, {==})
                case 1n+j_86:
                  FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.Enu{_ks_85}, e2_47}, rest_37}), FM.Enc.nat(1n+j_86)], ks}}, Fun.F.iter(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.Enu{_ks_85}, e2_47}, rest_37}), FM.Enc.nat(1n+j_86)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.look(Machine.Env.find(Machine.Val.env{Machine.Val.clo{Source.Term.Enu{_ks_85}, e2_47}, rest_37}, 1n+j_86)), ks}},
                    FP.Reach.steps(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.Enu{_ks_85}, e2_47}, rest_37}), FM.Enc.nat(1n+j_86)], ks}}),
                    L.Env.find(rest_37, j_86, ks))
            case Source.Term.Lab{+_k_87}:
              match i_35:
                case 0n:
                  (6n, {==})
                case 1n+j_88:
                  FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.Lab{_k_87}, e2_47}, rest_37}), FM.Enc.nat(1n+j_88)], ks}}, Fun.F.iter(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.Lab{_k_87}, e2_47}, rest_37}), FM.Enc.nat(1n+j_88)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.look(Machine.Env.find(Machine.Val.env{Machine.Val.clo{Source.Term.Lab{_k_87}, e2_47}, rest_37}, 1n+j_88)), ks}},
                    FP.Reach.steps(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.Lab{_k_87}, e2_47}, rest_37}), FM.Enc.nat(1n+j_88)], ks}}),
                    L.Env.find(rest_37, j_88, ks))
            case Source.Term.Mat{+_k_89, +_h_90, +_m_91}:
              match i_35:
                case 0n:
                  (6n, {==})
                case 1n+j_92:
                  FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.Mat{_k_89, _h_90, _m_91}, e2_47}, rest_37}), FM.Enc.nat(1n+j_92)], ks}}, Fun.F.iter(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.Mat{_k_89, _h_90, _m_91}, e2_47}, rest_37}), FM.Enc.nat(1n+j_92)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.look(Machine.Env.find(Machine.Val.env{Machine.Val.clo{Source.Term.Mat{_k_89, _h_90, _m_91}, e2_47}, rest_37}, 1n+j_92)), ks}},
                    FP.Reach.steps(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.Mat{_k_89, _h_90, _m_91}, e2_47}, rest_37}), FM.Enc.nat(1n+j_92)], ks}}),
                    L.Env.find(rest_37, j_92, ks))
            case Source.Term.Efq{}:
              match i_35:
                case 0n:
                  (6n, {==})
                case 1n+j_93:
                  FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.Efq{}, e2_47}, rest_37}), FM.Enc.nat(1n+j_93)], ks}}, Fun.F.iter(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.Efq{}, e2_47}, rest_37}), FM.Enc.nat(1n+j_93)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.look(Machine.Env.find(Machine.Val.env{Machine.Val.clo{Source.Term.Efq{}, e2_47}, rest_37}, 1n+j_93)), ks}},
                    FP.Reach.steps(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.Efq{}, e2_47}, rest_37}), FM.Enc.nat(1n+j_93)], ks}}),
                    L.Env.find(rest_37, j_93, ks))
            case Source.Term.Eql{+_a_94, +_b_95, +_t_96}:
              match i_35:
                case 0n:
                  (6n, {==})
                case 1n+j_97:
                  FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.Eql{_a_94, _b_95, _t_96}, e2_47}, rest_37}), FM.Enc.nat(1n+j_97)], ks}}, Fun.F.iter(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.Eql{_a_94, _b_95, _t_96}, e2_47}, rest_37}), FM.Enc.nat(1n+j_97)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.look(Machine.Env.find(Machine.Val.env{Machine.Val.clo{Source.Term.Eql{_a_94, _b_95, _t_96}, e2_47}, rest_37}, 1n+j_97)), ks}},
                    FP.Reach.steps(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.Eql{_a_94, _b_95, _t_96}, e2_47}, rest_37}), FM.Enc.nat(1n+j_97)], ks}}),
                    L.Env.find(rest_37, j_97, ks))
            case Source.Term.Rfl{}:
              match i_35:
                case 0n:
                  (6n, {==})
                case 1n+j_98:
                  FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.Rfl{}, e2_47}, rest_37}), FM.Enc.nat(1n+j_98)], ks}}, Fun.F.iter(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.Rfl{}, e2_47}, rest_37}), FM.Enc.nat(1n+j_98)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.look(Machine.Env.find(Machine.Val.env{Machine.Val.clo{Source.Term.Rfl{}, e2_47}, rest_37}, 1n+j_98)), ks}},
                    FP.Reach.steps(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.Rfl{}, e2_47}, rest_37}), FM.Enc.nat(1n+j_98)], ks}}),
                    L.Env.find(rest_37, j_98, ks))
            case Source.Term.Rwt{+_e_99, +_p_100, +_f_101}:
              match i_35:
                case 0n:
                  (6n, {==})
                case 1n+j_102:
                  FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.Rwt{_e_99, _p_100, _f_101}, e2_47}, rest_37}), FM.Enc.nat(1n+j_102)], ks}}, Fun.F.iter(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.Rwt{_e_99, _p_100, _f_101}, e2_47}, rest_37}), FM.Enc.nat(1n+j_102)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.look(Machine.Env.find(Machine.Val.env{Machine.Val.clo{Source.Term.Rwt{_e_99, _p_100, _f_101}, e2_47}, rest_37}, 1n+j_102)), ks}},
                    FP.Reach.steps(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.clo{Source.Term.Rwt{_e_99, _p_100, _f_101}, e2_47}, rest_37}), FM.Enc.nat(1n+j_102)], ks}}),
                    L.Env.find(rest_37, j_102, ks))
        case Machine.Val.lab{+_k_103}:
          match i_35:
            case 0n:
              (5n, {==})
            case 1n+j_104:
              FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.lab{_k_103}, rest_37}), FM.Enc.nat(1n+j_104)], ks}}, Fun.F.iter(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.lab{_k_103}, rest_37}), FM.Enc.nat(1n+j_104)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.look(Machine.Env.find(Machine.Val.env{Machine.Val.lab{_k_103}, rest_37}, 1n+j_104)), ks}},
                FP.Reach.steps(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.lab{_k_103}, rest_37}), FM.Enc.nat(1n+j_104)], ks}}),
                L.Env.find(rest_37, j_104, ks))
        case Machine.Val.rfl{}:
          match i_35:
            case 0n:
              (5n, {==})
            case 1n+j_105:
              FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.rfl{}, rest_37}), FM.Enc.nat(1n+j_105)], ks}}, Fun.F.iter(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.rfl{}, rest_37}), FM.Enc.nat(1n+j_105)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.look(Machine.Env.find(Machine.Val.env{Machine.Val.rfl{}, rest_37}, 1n+j_105)), ks}},
                FP.Reach.steps(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.rfl{}, rest_37}), FM.Enc.nat(1n+j_105)], ks}}),
                L.Env.find(rest_37, j_105, ks))
        case Machine.Val.tup{+_q_106, +_a_107, +_b_108}:
          match i_35:
            case 0n:
              (5n, {==})
            case 1n+j_109:
              FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.tup{_q_106, _a_107, _b_108}, rest_37}), FM.Enc.nat(1n+j_109)], ks}}, Fun.F.iter(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.tup{_q_106, _a_107, _b_108}, rest_37}), FM.Enc.nat(1n+j_109)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.look(Machine.Env.find(Machine.Val.env{Machine.Val.tup{_q_106, _a_107, _b_108}, rest_37}, 1n+j_109)), ks}},
                FP.Reach.steps(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.tup{_q_106, _a_107, _b_108}, rest_37}), FM.Enc.nat(1n+j_109)], ks}}),
                L.Env.find(rest_37, j_109, ks))
        case Machine.Val.call{+_k_110, +_xs_111}:
          match i_35:
            case 0n:
              (5n, {==})
            case 1n+j_112:
              FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.call{_k_110, _xs_111}, rest_37}), FM.Enc.nat(1n+j_112)], ks}}, Fun.F.iter(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.call{_k_110, _xs_111}, rest_37}), FM.Enc.nat(1n+j_112)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.look(Machine.Env.find(Machine.Val.env{Machine.Val.call{_k_110, _xs_111}, rest_37}, 1n+j_112)), ks}},
                FP.Reach.steps(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(Machine.Val.env{Machine.Val.call{_k_110, _xs_111}, rest_37}), FM.Enc.nat(1n+j_112)], ks}}),
                L.Env.find(rest_37, j_112, ks))
    case Machine.Val.arg{+_q_113, +_x_114, +_rest_115}:
      (3n, {==})
    case Machine.Val.clo{+_t_116, +_e_117}:
      (3n, {==})
    case Machine.Val.lab{+_k_118}:
      (3n, {==})
    case Machine.Val.rfl{}:
      (3n, {==})
    case Machine.Val.tup{+_q_119, +_a_120, +_b_121}:
      (3n, {==})
    case Machine.Val.call{+_k_122, +_xs_123}:
      (3n, {==})

def L.Val.form.of(+l_124: Machine.Look, +ks: List<&2, Fun.Fr>) ->
  Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.form.of(), [FM.Enc.look(l_124)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.form(Machine.Val.form.of(l_124)), ks}}):
  match l_124:
    case Machine.Look.val{+v_125}:
      match v_125:
        case Machine.Val.nil{}:
          (5n, {==})
        case Machine.Val.env{+_x_126, +_rest_127}:
          (5n, {==})
        case Machine.Val.arg{+_q_128, +_x_129, +_rest_130}:
          (5n, {==})
        case Machine.Val.clo{+t_131, +e_132}:
          match t_131:
            case Source.Term.Var{+_i_133}:
              (5n, {==})
            case Source.Term.Ref{+_k_134}:
              (5n, {==})
            case Source.Term.Ann{+_x_135, +_t_136}:
              (5n, {==})
            case Source.Term.Let{+_q_137, +_v_138, +_f_139}:
              (5n, {==})
            case Source.Term.Typ{+_q_140}:
              (5n, {==})
            case Source.Term.Min{+_a_141, +_b_142}:
              (5n, {==})
            case Source.Term.All{+_q_143, +_a_144, +_b_145}:
              (5n, {==})
            case Source.Term.Lam{+_q_146, +_f_147}:
              (5n, {==})
            case Source.Term.App{+_q_148, +_f_149, +_x_150}:
              (5n, {==})
            case Source.Term.Sig{+_q_151, +_a_152, +_b_153}:
              (5n, {==})
            case Source.Term.Tup{+r_154, +a_155, +b_156}:
              (9n, {==})
            case Source.Term.Prj{+_h_157}:
              (5n, {==})
            case Source.Term.Enu{+_ks_158}:
              (5n, {==})
            case Source.Term.Lab{+k_159}:
              (6n, {==})
            case Source.Term.Mat{+_k_160, +_h_161, +_m_162}:
              (5n, {==})
            case Source.Term.Efq{}:
              (5n, {==})
            case Source.Term.Eql{+_a_163, +_b_164, +_t_165}:
              (5n, {==})
            case Source.Term.Rfl{}:
              (5n, {==})
            case Source.Term.Rwt{+_e_166, +_p_167, +_f_168}:
              (5n, {==})
        case Machine.Val.lab{+k_169}:
          (6n, {==})
        case Machine.Val.rfl{}:
          (5n, {==})
        case Machine.Val.tup{+r_170, +a_171, +b_172}:
          (7n, {==})
        case Machine.Val.call{+_k_173, +_xs_174}:
          (5n, {==})
    case Machine.Look.free{+_j_175}:
      (2n, {==})

def L.Val.form(+x_176: Machine.Val, +ks: List<&2, Fun.Fr>) ->
  Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.form(), [FM.Enc.val(x_176)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.form(Machine.Val.form(x_176)), ks}}):
  FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.form(), [FM.Enc.val(x_176)], ks}}, Fun.F.iter(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.form(), [FM.Enc.val(x_176)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.form(Machine.Val.form(x_176)), ks}},
    FP.Reach.steps(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.form(), [FM.Enc.val(x_176)], ks}}),
    FP.Reach.trans(Code.prog(), Fun.F.iter(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.form(), [FM.Enc.val(x_176)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.look(Machine.Env.find(Machine.Val.env{x_176, Machine.Val.nil{}}, 0n)), Con{Fun.Fr{Code.F.Val.form.k1(), [FM.Enc.val(Machine.Val.env{x_176, Machine.Val.nil{}}), FM.Enc.val(x_176)]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.form(Machine.Val.form(x_176)), ks}},
    L.Env.find(Machine.Val.env{x_176, Machine.Val.nil{}}, 0n, Con{Fun.Fr{Code.F.Val.form.k1(), [FM.Enc.val(Machine.Val.env{x_176, Machine.Val.nil{}}), FM.Enc.val(x_176)]}, ks}),
    FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.look(Machine.Env.find(Machine.Val.env{x_176, Machine.Val.nil{}}, 0n)), Con{Fun.Fr{Code.F.Val.form.k1(), [FM.Enc.val(Machine.Val.env{x_176, Machine.Val.nil{}}), FM.Enc.val(x_176)]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.look(Machine.Env.find(Machine.Val.env{x_176, Machine.Val.nil{}}, 0n)), Con{Fun.Fr{Code.F.Val.form.k1(), [FM.Enc.val(Machine.Val.env{x_176, Machine.Val.nil{}}), FM.Enc.val(x_176)]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.form(Machine.Val.form(x_176)), ks}},
    FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.look(Machine.Env.find(Machine.Val.env{x_176, Machine.Val.nil{}}, 0n)), Con{Fun.Fr{Code.F.Val.form.k1(), [FM.Enc.val(Machine.Val.env{x_176, Machine.Val.nil{}}), FM.Enc.val(x_176)]}, ks}}}),
    FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.form.k1(), [FM.Enc.look(Machine.Env.find(Machine.Val.env{x_176, Machine.Val.nil{}}, 0n)), FM.Enc.val(Machine.Val.env{x_176, Machine.Val.nil{}}), FM.Enc.val(x_176)], ks}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.form.k1(), [FM.Enc.look(Machine.Env.find(Machine.Val.env{x_176, Machine.Val.nil{}}, 0n)), FM.Enc.val(Machine.Val.env{x_176, Machine.Val.nil{}}), FM.Enc.val(x_176)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.form(Machine.Val.form.of(Machine.Env.find(Machine.Val.env{x_176, Machine.Val.nil{}}, 0n))), ks}},
    FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.form.k1(), [FM.Enc.look(Machine.Env.find(Machine.Val.env{x_176, Machine.Val.nil{}}, 0n)), FM.Enc.val(Machine.Val.env{x_176, Machine.Val.nil{}}), FM.Enc.val(x_176)], ks}}),
    L.Val.form.of(Machine.Env.find(Machine.Val.env{x_176, Machine.Val.nil{}}, 0n), ks)))))

def L.Val.data.go(+e_178: Machine.Val, +c_180: Bool, +t_179: Source.Term, +ks: List<&2, Fun.Fr>) ->
  Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go(), [FM.Enc.val(e_178), FM.Enc.term(t_179), FM.Enc.bool(c_180)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(e_178, t_179, c_180)), ks}}):
  match e_178:
    case Machine.Val.nil{}:
      match c_180:
        case False{}:
          match t_179:
            case Source.Term.Var{+_i_181}:
              (3n, {==})
            case Source.Term.Ref{+_k_182}:
              (3n, {==})
            case Source.Term.Ann{+_x_183, +_t_184}:
              (3n, {==})
            case Source.Term.Let{+_q_185, +_v_186, +_f_187}:
              (3n, {==})
            case Source.Term.Typ{+_q_188}:
              (3n, {==})
            case Source.Term.Min{+_a_189, +_b_190}:
              (3n, {==})
            case Source.Term.All{+_q_191, +_a_192, +_b_193}:
              (3n, {==})
            case Source.Term.Lam{+_q_194, +_f_195}:
              (3n, {==})
            case Source.Term.App{+_q_196, +_f_197, +_x_198}:
              (3n, {==})
            case Source.Term.Sig{+_q_199, +_a_200, +_b_201}:
              (3n, {==})
            case Source.Term.Tup{+_q_202, +_a_203, +_b_204}:
              (3n, {==})
            case Source.Term.Prj{+_h_205}:
              (3n, {==})
            case Source.Term.Enu{+_ks_206}:
              (3n, {==})
            case Source.Term.Lab{+_k_207}:
              (3n, {==})
            case Source.Term.Mat{+_k_208, +_h_209, +_m_210}:
              (3n, {==})
            case Source.Term.Efq{}:
              (3n, {==})
            case Source.Term.Eql{+_a_211, +_b_212, +_t_213}:
              (3n, {==})
            case Source.Term.Rfl{}:
              (3n, {==})
            case Source.Term.Rwt{+_e_214, +_p_215, +_f_216}:
              (3n, {==})
        case True{}:
          match t_179:
            case Source.Term.Var{+i_217}:
              (4n, {==})
            case Source.Term.Ref{+_k_218}:
              (7n, {==})
            case Source.Term.Ann{+_x_219, +_t_220}:
              (7n, {==})
            case Source.Term.Let{+_q_221, +_v_222, +_f_223}:
              (7n, {==})
            case Source.Term.Typ{+_q_224}:
              (7n, {==})
            case Source.Term.Min{+_a_225, +_b_226}:
              (7n, {==})
            case Source.Term.All{+_q_227, +_a_228, +_b_229}:
              (7n, {==})
            case Source.Term.Lam{+_q_230, +_f_231}:
              (7n, {==})
            case Source.Term.App{+_q_232, +_f_233, +_x_234}:
              (7n, {==})
            case Source.Term.Sig{+_q_235, +_a_236, +_b_237}:
              (7n, {==})
            case Source.Term.Tup{+q_238, +a_239, +b_240}:
              match q_238:
                case Source.Q0{}:
                  FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go(), [FM.Enc.val(Machine.Val.nil{}), FM.Enc.term(Source.Term.Tup{Source.Q0{}, a_239, b_240}), FM.Enc.bool(True{})], ks}}, Fun.F.iter(7n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go(), [FM.Enc.val(Machine.Val.nil{}), FM.Enc.term(Source.Term.Tup{Source.Q0{}, a_239, b_240}), FM.Enc.bool(True{})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(Machine.Val.nil{}, Source.Term.Tup{Source.Q0{}, a_239, b_240}, True{})), ks}},
                    FP.Reach.steps(7n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go(), [FM.Enc.val(Machine.Val.nil{}), FM.Enc.term(Source.Term.Tup{Source.Q0{}, a_239, b_240}), FM.Enc.bool(True{})], ks}}),
                    L.Val.data.go(Machine.Val.nil{}, True{}, b_240, ks))
                case Source.Q1{}:
                  FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go(), [FM.Enc.val(Machine.Val.nil{}), FM.Enc.term(Source.Term.Tup{Source.Q1{}, a_239, b_240}), FM.Enc.bool(True{})], ks}}, Fun.F.iter(7n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go(), [FM.Enc.val(Machine.Val.nil{}), FM.Enc.term(Source.Term.Tup{Source.Q1{}, a_239, b_240}), FM.Enc.bool(True{})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(Machine.Val.nil{}, Source.Term.Tup{Source.Q1{}, a_239, b_240}, True{})), ks}},
                    FP.Reach.steps(7n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go(), [FM.Enc.val(Machine.Val.nil{}), FM.Enc.term(Source.Term.Tup{Source.Q1{}, a_239, b_240}), FM.Enc.bool(True{})], ks}}),
                    FP.Reach.trans(Code.prog(), Fun.F.iter(7n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go(), [FM.Enc.val(Machine.Val.nil{}), FM.Enc.term(Source.Term.Tup{Source.Q1{}, a_239, b_240}), FM.Enc.bool(True{})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(Machine.Val.nil{}, a_239, True{})), Con{Fun.Fr{Code.F.Val.data.go.k1(), [FM.Enc.term(b_240), FM.Enc.term(a_239), FM.Enc.p(FM.Enc.term(a_239), FM.Enc.term(b_240)), FM.Enc.quan(Source.Q1{}), Fun.V.z{}, Fun.V.z{}, Fun.V.z{}, Fun.V.z{}, FM.Enc.val(Machine.Val.nil{}), FM.Enc.term(Source.Term.Tup{Source.Q1{}, a_239, b_240}), FM.Enc.bool(True{})]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(Machine.Val.nil{}, Source.Term.Tup{Source.Q1{}, a_239, b_240}, True{})), ks}},
                    L.Val.data.go(Machine.Val.nil{}, True{}, a_239, Con{Fun.Fr{Code.F.Val.data.go.k1(), [FM.Enc.term(b_240), FM.Enc.term(a_239), FM.Enc.p(FM.Enc.term(a_239), FM.Enc.term(b_240)), FM.Enc.quan(Source.Q1{}), Fun.V.z{}, Fun.V.z{}, Fun.V.z{}, Fun.V.z{}, FM.Enc.val(Machine.Val.nil{}), FM.Enc.term(Source.Term.Tup{Source.Q1{}, a_239, b_240}), FM.Enc.bool(True{})]}, ks}),
                    FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(Machine.Val.nil{}, a_239, True{})), Con{Fun.Fr{Code.F.Val.data.go.k1(), [FM.Enc.term(b_240), FM.Enc.term(a_239), FM.Enc.p(FM.Enc.term(a_239), FM.Enc.term(b_240)), FM.Enc.quan(Source.Q1{}), Fun.V.z{}, Fun.V.z{}, Fun.V.z{}, Fun.V.z{}, FM.Enc.val(Machine.Val.nil{}), FM.Enc.term(Source.Term.Tup{Source.Q1{}, a_239, b_240}), FM.Enc.bool(True{})]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(Machine.Val.nil{}, a_239, True{})), Con{Fun.Fr{Code.F.Val.data.go.k1(), [FM.Enc.term(b_240), FM.Enc.term(a_239), FM.Enc.p(FM.Enc.term(a_239), FM.Enc.term(b_240)), FM.Enc.quan(Source.Q1{}), Fun.V.z{}, Fun.V.z{}, Fun.V.z{}, Fun.V.z{}, FM.Enc.val(Machine.Val.nil{}), FM.Enc.term(Source.Term.Tup{Source.Q1{}, a_239, b_240}), FM.Enc.bool(True{})]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(Machine.Val.nil{}, Source.Term.Tup{Source.Q1{}, a_239, b_240}, True{})), ks}},
                    FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(Machine.Val.nil{}, a_239, True{})), Con{Fun.Fr{Code.F.Val.data.go.k1(), [FM.Enc.term(b_240), FM.Enc.term(a_239), FM.Enc.p(FM.Enc.term(a_239), FM.Enc.term(b_240)), FM.Enc.quan(Source.Q1{}), Fun.V.z{}, Fun.V.z{}, Fun.V.z{}, Fun.V.z{}, FM.Enc.val(Machine.Val.nil{}), FM.Enc.term(Source.Term.Tup{Source.Q1{}, a_239, b_240}), FM.Enc.bool(True{})]}, ks}}}),
                    Elim.Bool(Machine.Val.data.go(Machine.Val.nil{}, a_239, True{}), m2 => Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go.k1(), [FM.Enc.bool(m2), FM.Enc.term(b_240), FM.Enc.term(a_239), FM.Enc.p(FM.Enc.term(a_239), FM.Enc.term(b_240)), FM.Enc.quan(Source.Q1{}), Fun.V.z{}, Fun.V.z{}, Fun.V.z{}, Fun.V.z{}, FM.Enc.val(Machine.Val.nil{}), FM.Enc.term(Source.Term.Tup{Source.Q1{}, a_239, b_240}), FM.Enc.bool(True{})], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(Bool.and(m2, Machine.Val.data.go(Machine.Val.nil{}, b_240, True{}))), ks}}),
                    (2n, {==}),
                    FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go.k1(), [FM.Enc.bool(True{}), FM.Enc.term(b_240), FM.Enc.term(a_239), FM.Enc.p(FM.Enc.term(a_239), FM.Enc.term(b_240)), FM.Enc.quan(Source.Q1{}), Fun.V.z{}, Fun.V.z{}, Fun.V.z{}, Fun.V.z{}, FM.Enc.val(Machine.Val.nil{}), FM.Enc.term(Source.Term.Tup{Source.Q1{}, a_239, b_240}), FM.Enc.bool(True{})], ks}}, Fun.F.iter(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go.k1(), [FM.Enc.bool(True{}), FM.Enc.term(b_240), FM.Enc.term(a_239), FM.Enc.p(FM.Enc.term(a_239), FM.Enc.term(b_240)), FM.Enc.quan(Source.Q1{}), Fun.V.z{}, Fun.V.z{}, Fun.V.z{}, Fun.V.z{}, FM.Enc.val(Machine.Val.nil{}), FM.Enc.term(Source.Term.Tup{Source.Q1{}, a_239, b_240}), FM.Enc.bool(True{})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Bool.and(True{}, Machine.Val.data.go(Machine.Val.nil{}, b_240, True{}))), ks}},
                    FP.Reach.steps(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go.k1(), [FM.Enc.bool(True{}), FM.Enc.term(b_240), FM.Enc.term(a_239), FM.Enc.p(FM.Enc.term(a_239), FM.Enc.term(b_240)), FM.Enc.quan(Source.Q1{}), Fun.V.z{}, Fun.V.z{}, Fun.V.z{}, Fun.V.z{}, FM.Enc.val(Machine.Val.nil{}), FM.Enc.term(Source.Term.Tup{Source.Q1{}, a_239, b_240}), FM.Enc.bool(True{})], ks}}),
                    L.Val.data.go(Machine.Val.nil{}, True{}, b_240, ks))))))
                case Source.Q2{}:
                  FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go(), [FM.Enc.val(Machine.Val.nil{}), FM.Enc.term(Source.Term.Tup{Source.Q2{}, a_239, b_240}), FM.Enc.bool(True{})], ks}}, Fun.F.iter(7n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go(), [FM.Enc.val(Machine.Val.nil{}), FM.Enc.term(Source.Term.Tup{Source.Q2{}, a_239, b_240}), FM.Enc.bool(True{})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(Machine.Val.nil{}, Source.Term.Tup{Source.Q2{}, a_239, b_240}, True{})), ks}},
                    FP.Reach.steps(7n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go(), [FM.Enc.val(Machine.Val.nil{}), FM.Enc.term(Source.Term.Tup{Source.Q2{}, a_239, b_240}), FM.Enc.bool(True{})], ks}}),
                    FP.Reach.trans(Code.prog(), Fun.F.iter(7n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go(), [FM.Enc.val(Machine.Val.nil{}), FM.Enc.term(Source.Term.Tup{Source.Q2{}, a_239, b_240}), FM.Enc.bool(True{})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(Machine.Val.nil{}, a_239, True{})), Con{Fun.Fr{Code.F.Val.data.go.k1(), [FM.Enc.term(b_240), FM.Enc.term(a_239), FM.Enc.p(FM.Enc.term(a_239), FM.Enc.term(b_240)), FM.Enc.quan(Source.Q2{}), Fun.V.z{}, Fun.V.z{}, Fun.V.z{}, Fun.V.z{}, FM.Enc.val(Machine.Val.nil{}), FM.Enc.term(Source.Term.Tup{Source.Q2{}, a_239, b_240}), FM.Enc.bool(True{})]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(Machine.Val.nil{}, Source.Term.Tup{Source.Q2{}, a_239, b_240}, True{})), ks}},
                    L.Val.data.go(Machine.Val.nil{}, True{}, a_239, Con{Fun.Fr{Code.F.Val.data.go.k1(), [FM.Enc.term(b_240), FM.Enc.term(a_239), FM.Enc.p(FM.Enc.term(a_239), FM.Enc.term(b_240)), FM.Enc.quan(Source.Q2{}), Fun.V.z{}, Fun.V.z{}, Fun.V.z{}, Fun.V.z{}, FM.Enc.val(Machine.Val.nil{}), FM.Enc.term(Source.Term.Tup{Source.Q2{}, a_239, b_240}), FM.Enc.bool(True{})]}, ks}),
                    FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(Machine.Val.nil{}, a_239, True{})), Con{Fun.Fr{Code.F.Val.data.go.k1(), [FM.Enc.term(b_240), FM.Enc.term(a_239), FM.Enc.p(FM.Enc.term(a_239), FM.Enc.term(b_240)), FM.Enc.quan(Source.Q2{}), Fun.V.z{}, Fun.V.z{}, Fun.V.z{}, Fun.V.z{}, FM.Enc.val(Machine.Val.nil{}), FM.Enc.term(Source.Term.Tup{Source.Q2{}, a_239, b_240}), FM.Enc.bool(True{})]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(Machine.Val.nil{}, a_239, True{})), Con{Fun.Fr{Code.F.Val.data.go.k1(), [FM.Enc.term(b_240), FM.Enc.term(a_239), FM.Enc.p(FM.Enc.term(a_239), FM.Enc.term(b_240)), FM.Enc.quan(Source.Q2{}), Fun.V.z{}, Fun.V.z{}, Fun.V.z{}, Fun.V.z{}, FM.Enc.val(Machine.Val.nil{}), FM.Enc.term(Source.Term.Tup{Source.Q2{}, a_239, b_240}), FM.Enc.bool(True{})]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(Machine.Val.nil{}, Source.Term.Tup{Source.Q2{}, a_239, b_240}, True{})), ks}},
                    FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(Machine.Val.nil{}, a_239, True{})), Con{Fun.Fr{Code.F.Val.data.go.k1(), [FM.Enc.term(b_240), FM.Enc.term(a_239), FM.Enc.p(FM.Enc.term(a_239), FM.Enc.term(b_240)), FM.Enc.quan(Source.Q2{}), Fun.V.z{}, Fun.V.z{}, Fun.V.z{}, Fun.V.z{}, FM.Enc.val(Machine.Val.nil{}), FM.Enc.term(Source.Term.Tup{Source.Q2{}, a_239, b_240}), FM.Enc.bool(True{})]}, ks}}}),
                    Elim.Bool(Machine.Val.data.go(Machine.Val.nil{}, a_239, True{}), m3 => Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go.k1(), [FM.Enc.bool(m3), FM.Enc.term(b_240), FM.Enc.term(a_239), FM.Enc.p(FM.Enc.term(a_239), FM.Enc.term(b_240)), FM.Enc.quan(Source.Q2{}), Fun.V.z{}, Fun.V.z{}, Fun.V.z{}, Fun.V.z{}, FM.Enc.val(Machine.Val.nil{}), FM.Enc.term(Source.Term.Tup{Source.Q2{}, a_239, b_240}), FM.Enc.bool(True{})], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(Bool.and(m3, Machine.Val.data.go(Machine.Val.nil{}, b_240, True{}))), ks}}),
                    (2n, {==}),
                    FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go.k1(), [FM.Enc.bool(True{}), FM.Enc.term(b_240), FM.Enc.term(a_239), FM.Enc.p(FM.Enc.term(a_239), FM.Enc.term(b_240)), FM.Enc.quan(Source.Q2{}), Fun.V.z{}, Fun.V.z{}, Fun.V.z{}, Fun.V.z{}, FM.Enc.val(Machine.Val.nil{}), FM.Enc.term(Source.Term.Tup{Source.Q2{}, a_239, b_240}), FM.Enc.bool(True{})], ks}}, Fun.F.iter(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go.k1(), [FM.Enc.bool(True{}), FM.Enc.term(b_240), FM.Enc.term(a_239), FM.Enc.p(FM.Enc.term(a_239), FM.Enc.term(b_240)), FM.Enc.quan(Source.Q2{}), Fun.V.z{}, Fun.V.z{}, Fun.V.z{}, Fun.V.z{}, FM.Enc.val(Machine.Val.nil{}), FM.Enc.term(Source.Term.Tup{Source.Q2{}, a_239, b_240}), FM.Enc.bool(True{})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Bool.and(True{}, Machine.Val.data.go(Machine.Val.nil{}, b_240, True{}))), ks}},
                    FP.Reach.steps(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go.k1(), [FM.Enc.bool(True{}), FM.Enc.term(b_240), FM.Enc.term(a_239), FM.Enc.p(FM.Enc.term(a_239), FM.Enc.term(b_240)), FM.Enc.quan(Source.Q2{}), Fun.V.z{}, Fun.V.z{}, Fun.V.z{}, Fun.V.z{}, FM.Enc.val(Machine.Val.nil{}), FM.Enc.term(Source.Term.Tup{Source.Q2{}, a_239, b_240}), FM.Enc.bool(True{})], ks}}),
                    L.Val.data.go(Machine.Val.nil{}, True{}, b_240, ks))))))
            case Source.Term.Prj{+_h_243}:
              (7n, {==})
            case Source.Term.Enu{+_ks_244}:
              (7n, {==})
            case Source.Term.Lab{+k_245}:
              (6n, {==})
            case Source.Term.Mat{+_k_246, +_h_247, +_m_248}:
              (7n, {==})
            case Source.Term.Efq{}:
              (7n, {==})
            case Source.Term.Eql{+_a_249, +_b_250, +_t_251}:
              (7n, {==})
            case Source.Term.Rfl{}:
              (7n, {==})
            case Source.Term.Rwt{+_e_252, +_p_253, +_f_254}:
              (7n, {==})
    case Machine.Val.env{+x_255, +rest_256}:
      match c_180:
        case False{}:
          match t_179:
            case Source.Term.Var{+_i_257}:
              match _i_257:
                case 0n:
                  (4n, {==})
                case 1n+_p_258:
                  (4n, {==})
            case Source.Term.Ref{+_k_259}:
              (4n, {==})
            case Source.Term.Ann{+_x_260, +_t_261}:
              (4n, {==})
            case Source.Term.Let{+_q_262, +_v_263, +_f_264}:
              (4n, {==})
            case Source.Term.Typ{+_q_265}:
              (4n, {==})
            case Source.Term.Min{+_a_266, +_b_267}:
              (4n, {==})
            case Source.Term.All{+_q_268, +_a_269, +_b_270}:
              (4n, {==})
            case Source.Term.Lam{+_q_271, +_f_272}:
              (4n, {==})
            case Source.Term.App{+_q_273, +_f_274, +_x_275}:
              (4n, {==})
            case Source.Term.Sig{+_q_276, +_a_277, +_b_278}:
              (4n, {==})
            case Source.Term.Tup{+_q_279, +_a_280, +_b_281}:
              (4n, {==})
            case Source.Term.Prj{+_h_282}:
              (4n, {==})
            case Source.Term.Enu{+_ks_283}:
              (4n, {==})
            case Source.Term.Lab{+_k_284}:
              (4n, {==})
            case Source.Term.Mat{+_k_285, +_h_286, +_m_287}:
              (4n, {==})
            case Source.Term.Efq{}:
              (4n, {==})
            case Source.Term.Eql{+_a_288, +_b_289, +_t_290}:
              (4n, {==})
            case Source.Term.Rfl{}:
              (4n, {==})
            case Source.Term.Rwt{+_e_291, +_p_292, +_f_293}:
              (4n, {==})
        case True{}:
          match t_179:
            case Source.Term.Var{+i_294}:
              match i_294:
                case 0n:
                  FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go(), [FM.Enc.val(Machine.Val.env{x_255, rest_256}), FM.Enc.term(Source.Term.Var{0n}), FM.Enc.bool(True{})], ks}}, Fun.F.iter(6n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go(), [FM.Enc.val(Machine.Val.env{x_255, rest_256}), FM.Enc.term(Source.Term.Var{0n}), FM.Enc.bool(True{})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(Machine.Val.env{x_255, rest_256}, Source.Term.Var{0n}, True{})), ks}},
                    FP.Reach.steps(6n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go(), [FM.Enc.val(Machine.Val.env{x_255, rest_256}), FM.Enc.term(Source.Term.Var{0n}), FM.Enc.bool(True{})], ks}}),
                    L.Val.data.go(x_255, False{}, Source.Term.Efq{}, ks))
                case 1n+j_295:
                  FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go(), [FM.Enc.val(Machine.Val.env{x_255, rest_256}), FM.Enc.term(Source.Term.Var{1n+j_295}), FM.Enc.bool(True{})], ks}}, Fun.F.iter(7n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go(), [FM.Enc.val(Machine.Val.env{x_255, rest_256}), FM.Enc.term(Source.Term.Var{1n+j_295}), FM.Enc.bool(True{})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(Machine.Val.env{x_255, rest_256}, Source.Term.Var{1n+j_295}, True{})), ks}},
                    FP.Reach.steps(7n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go(), [FM.Enc.val(Machine.Val.env{x_255, rest_256}), FM.Enc.term(Source.Term.Var{1n+j_295}), FM.Enc.bool(True{})], ks}}),
                    L.Val.data.go(rest_256, True{}, Source.Term.Var{j_295}, ks))
            case Source.Term.Ref{+_k_296}:
              (8n, {==})
            case Source.Term.Ann{+_x_297, +_t_298}:
              (8n, {==})
            case Source.Term.Let{+_q_299, +_v_300, +_f_301}:
              (8n, {==})
            case Source.Term.Typ{+_q_302}:
              (8n, {==})
            case Source.Term.Min{+_a_303, +_b_304}:
              (8n, {==})
            case Source.Term.All{+_q_305, +_a_306, +_b_307}:
              (8n, {==})
            case Source.Term.Lam{+_q_308, +_f_309}:
              (8n, {==})
            case Source.Term.App{+_q_310, +_f_311, +_x_312}:
              (8n, {==})
            case Source.Term.Sig{+_q_313, +_a_314, +_b_315}:
              (8n, {==})
            case Source.Term.Tup{+q_316, +a_317, +b_318}:
              match q_316:
                case Source.Q0{}:
                  FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go(), [FM.Enc.val(Machine.Val.env{x_255, rest_256}), FM.Enc.term(Source.Term.Tup{Source.Q0{}, a_317, b_318}), FM.Enc.bool(True{})], ks}}, Fun.F.iter(8n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go(), [FM.Enc.val(Machine.Val.env{x_255, rest_256}), FM.Enc.term(Source.Term.Tup{Source.Q0{}, a_317, b_318}), FM.Enc.bool(True{})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(Machine.Val.env{x_255, rest_256}, Source.Term.Tup{Source.Q0{}, a_317, b_318}, True{})), ks}},
                    FP.Reach.steps(8n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go(), [FM.Enc.val(Machine.Val.env{x_255, rest_256}), FM.Enc.term(Source.Term.Tup{Source.Q0{}, a_317, b_318}), FM.Enc.bool(True{})], ks}}),
                    L.Val.data.go(Machine.Val.env{x_255, rest_256}, True{}, b_318, ks))
                case Source.Q1{}:
                  FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go(), [FM.Enc.val(Machine.Val.env{x_255, rest_256}), FM.Enc.term(Source.Term.Tup{Source.Q1{}, a_317, b_318}), FM.Enc.bool(True{})], ks}}, Fun.F.iter(8n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go(), [FM.Enc.val(Machine.Val.env{x_255, rest_256}), FM.Enc.term(Source.Term.Tup{Source.Q1{}, a_317, b_318}), FM.Enc.bool(True{})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(Machine.Val.env{x_255, rest_256}, Source.Term.Tup{Source.Q1{}, a_317, b_318}, True{})), ks}},
                    FP.Reach.steps(8n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go(), [FM.Enc.val(Machine.Val.env{x_255, rest_256}), FM.Enc.term(Source.Term.Tup{Source.Q1{}, a_317, b_318}), FM.Enc.bool(True{})], ks}}),
                    FP.Reach.trans(Code.prog(), Fun.F.iter(8n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go(), [FM.Enc.val(Machine.Val.env{x_255, rest_256}), FM.Enc.term(Source.Term.Tup{Source.Q1{}, a_317, b_318}), FM.Enc.bool(True{})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(Machine.Val.env{x_255, rest_256}, a_317, True{})), Con{Fun.Fr{Code.F.Val.data.go.k2(), [FM.Enc.term(b_318), FM.Enc.term(a_317), FM.Enc.p(FM.Enc.term(a_317), FM.Enc.term(b_318)), FM.Enc.quan(Source.Q1{}), Fun.V.z{}, Fun.V.z{}, FM.Enc.val(rest_256), FM.Enc.val(x_255), FM.Enc.val(Machine.Val.env{x_255, rest_256}), FM.Enc.term(Source.Term.Tup{Source.Q1{}, a_317, b_318}), FM.Enc.bool(True{})]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(Machine.Val.env{x_255, rest_256}, Source.Term.Tup{Source.Q1{}, a_317, b_318}, True{})), ks}},
                    L.Val.data.go(Machine.Val.env{x_255, rest_256}, True{}, a_317, Con{Fun.Fr{Code.F.Val.data.go.k2(), [FM.Enc.term(b_318), FM.Enc.term(a_317), FM.Enc.p(FM.Enc.term(a_317), FM.Enc.term(b_318)), FM.Enc.quan(Source.Q1{}), Fun.V.z{}, Fun.V.z{}, FM.Enc.val(rest_256), FM.Enc.val(x_255), FM.Enc.val(Machine.Val.env{x_255, rest_256}), FM.Enc.term(Source.Term.Tup{Source.Q1{}, a_317, b_318}), FM.Enc.bool(True{})]}, ks}),
                    FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(Machine.Val.env{x_255, rest_256}, a_317, True{})), Con{Fun.Fr{Code.F.Val.data.go.k2(), [FM.Enc.term(b_318), FM.Enc.term(a_317), FM.Enc.p(FM.Enc.term(a_317), FM.Enc.term(b_318)), FM.Enc.quan(Source.Q1{}), Fun.V.z{}, Fun.V.z{}, FM.Enc.val(rest_256), FM.Enc.val(x_255), FM.Enc.val(Machine.Val.env{x_255, rest_256}), FM.Enc.term(Source.Term.Tup{Source.Q1{}, a_317, b_318}), FM.Enc.bool(True{})]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(Machine.Val.env{x_255, rest_256}, a_317, True{})), Con{Fun.Fr{Code.F.Val.data.go.k2(), [FM.Enc.term(b_318), FM.Enc.term(a_317), FM.Enc.p(FM.Enc.term(a_317), FM.Enc.term(b_318)), FM.Enc.quan(Source.Q1{}), Fun.V.z{}, Fun.V.z{}, FM.Enc.val(rest_256), FM.Enc.val(x_255), FM.Enc.val(Machine.Val.env{x_255, rest_256}), FM.Enc.term(Source.Term.Tup{Source.Q1{}, a_317, b_318}), FM.Enc.bool(True{})]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(Machine.Val.env{x_255, rest_256}, Source.Term.Tup{Source.Q1{}, a_317, b_318}, True{})), ks}},
                    FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(Machine.Val.env{x_255, rest_256}, a_317, True{})), Con{Fun.Fr{Code.F.Val.data.go.k2(), [FM.Enc.term(b_318), FM.Enc.term(a_317), FM.Enc.p(FM.Enc.term(a_317), FM.Enc.term(b_318)), FM.Enc.quan(Source.Q1{}), Fun.V.z{}, Fun.V.z{}, FM.Enc.val(rest_256), FM.Enc.val(x_255), FM.Enc.val(Machine.Val.env{x_255, rest_256}), FM.Enc.term(Source.Term.Tup{Source.Q1{}, a_317, b_318}), FM.Enc.bool(True{})]}, ks}}}),
                    Elim.Bool(Machine.Val.data.go(Machine.Val.env{x_255, rest_256}, a_317, True{}), m4 => Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go.k2(), [FM.Enc.bool(m4), FM.Enc.term(b_318), FM.Enc.term(a_317), FM.Enc.p(FM.Enc.term(a_317), FM.Enc.term(b_318)), FM.Enc.quan(Source.Q1{}), Fun.V.z{}, Fun.V.z{}, FM.Enc.val(rest_256), FM.Enc.val(x_255), FM.Enc.val(Machine.Val.env{x_255, rest_256}), FM.Enc.term(Source.Term.Tup{Source.Q1{}, a_317, b_318}), FM.Enc.bool(True{})], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(Bool.and(m4, Machine.Val.data.go(Machine.Val.env{x_255, rest_256}, b_318, True{}))), ks}}),
                    (2n, {==}),
                    FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go.k2(), [FM.Enc.bool(True{}), FM.Enc.term(b_318), FM.Enc.term(a_317), FM.Enc.p(FM.Enc.term(a_317), FM.Enc.term(b_318)), FM.Enc.quan(Source.Q1{}), Fun.V.z{}, Fun.V.z{}, FM.Enc.val(rest_256), FM.Enc.val(x_255), FM.Enc.val(Machine.Val.env{x_255, rest_256}), FM.Enc.term(Source.Term.Tup{Source.Q1{}, a_317, b_318}), FM.Enc.bool(True{})], ks}}, Fun.F.iter(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go.k2(), [FM.Enc.bool(True{}), FM.Enc.term(b_318), FM.Enc.term(a_317), FM.Enc.p(FM.Enc.term(a_317), FM.Enc.term(b_318)), FM.Enc.quan(Source.Q1{}), Fun.V.z{}, Fun.V.z{}, FM.Enc.val(rest_256), FM.Enc.val(x_255), FM.Enc.val(Machine.Val.env{x_255, rest_256}), FM.Enc.term(Source.Term.Tup{Source.Q1{}, a_317, b_318}), FM.Enc.bool(True{})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Bool.and(True{}, Machine.Val.data.go(Machine.Val.env{x_255, rest_256}, b_318, True{}))), ks}},
                    FP.Reach.steps(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go.k2(), [FM.Enc.bool(True{}), FM.Enc.term(b_318), FM.Enc.term(a_317), FM.Enc.p(FM.Enc.term(a_317), FM.Enc.term(b_318)), FM.Enc.quan(Source.Q1{}), Fun.V.z{}, Fun.V.z{}, FM.Enc.val(rest_256), FM.Enc.val(x_255), FM.Enc.val(Machine.Val.env{x_255, rest_256}), FM.Enc.term(Source.Term.Tup{Source.Q1{}, a_317, b_318}), FM.Enc.bool(True{})], ks}}),
                    L.Val.data.go(Machine.Val.env{x_255, rest_256}, True{}, b_318, ks))))))
                case Source.Q2{}:
                  FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go(), [FM.Enc.val(Machine.Val.env{x_255, rest_256}), FM.Enc.term(Source.Term.Tup{Source.Q2{}, a_317, b_318}), FM.Enc.bool(True{})], ks}}, Fun.F.iter(8n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go(), [FM.Enc.val(Machine.Val.env{x_255, rest_256}), FM.Enc.term(Source.Term.Tup{Source.Q2{}, a_317, b_318}), FM.Enc.bool(True{})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(Machine.Val.env{x_255, rest_256}, Source.Term.Tup{Source.Q2{}, a_317, b_318}, True{})), ks}},
                    FP.Reach.steps(8n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go(), [FM.Enc.val(Machine.Val.env{x_255, rest_256}), FM.Enc.term(Source.Term.Tup{Source.Q2{}, a_317, b_318}), FM.Enc.bool(True{})], ks}}),
                    FP.Reach.trans(Code.prog(), Fun.F.iter(8n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go(), [FM.Enc.val(Machine.Val.env{x_255, rest_256}), FM.Enc.term(Source.Term.Tup{Source.Q2{}, a_317, b_318}), FM.Enc.bool(True{})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(Machine.Val.env{x_255, rest_256}, a_317, True{})), Con{Fun.Fr{Code.F.Val.data.go.k2(), [FM.Enc.term(b_318), FM.Enc.term(a_317), FM.Enc.p(FM.Enc.term(a_317), FM.Enc.term(b_318)), FM.Enc.quan(Source.Q2{}), Fun.V.z{}, Fun.V.z{}, FM.Enc.val(rest_256), FM.Enc.val(x_255), FM.Enc.val(Machine.Val.env{x_255, rest_256}), FM.Enc.term(Source.Term.Tup{Source.Q2{}, a_317, b_318}), FM.Enc.bool(True{})]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(Machine.Val.env{x_255, rest_256}, Source.Term.Tup{Source.Q2{}, a_317, b_318}, True{})), ks}},
                    L.Val.data.go(Machine.Val.env{x_255, rest_256}, True{}, a_317, Con{Fun.Fr{Code.F.Val.data.go.k2(), [FM.Enc.term(b_318), FM.Enc.term(a_317), FM.Enc.p(FM.Enc.term(a_317), FM.Enc.term(b_318)), FM.Enc.quan(Source.Q2{}), Fun.V.z{}, Fun.V.z{}, FM.Enc.val(rest_256), FM.Enc.val(x_255), FM.Enc.val(Machine.Val.env{x_255, rest_256}), FM.Enc.term(Source.Term.Tup{Source.Q2{}, a_317, b_318}), FM.Enc.bool(True{})]}, ks}),
                    FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(Machine.Val.env{x_255, rest_256}, a_317, True{})), Con{Fun.Fr{Code.F.Val.data.go.k2(), [FM.Enc.term(b_318), FM.Enc.term(a_317), FM.Enc.p(FM.Enc.term(a_317), FM.Enc.term(b_318)), FM.Enc.quan(Source.Q2{}), Fun.V.z{}, Fun.V.z{}, FM.Enc.val(rest_256), FM.Enc.val(x_255), FM.Enc.val(Machine.Val.env{x_255, rest_256}), FM.Enc.term(Source.Term.Tup{Source.Q2{}, a_317, b_318}), FM.Enc.bool(True{})]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(Machine.Val.env{x_255, rest_256}, a_317, True{})), Con{Fun.Fr{Code.F.Val.data.go.k2(), [FM.Enc.term(b_318), FM.Enc.term(a_317), FM.Enc.p(FM.Enc.term(a_317), FM.Enc.term(b_318)), FM.Enc.quan(Source.Q2{}), Fun.V.z{}, Fun.V.z{}, FM.Enc.val(rest_256), FM.Enc.val(x_255), FM.Enc.val(Machine.Val.env{x_255, rest_256}), FM.Enc.term(Source.Term.Tup{Source.Q2{}, a_317, b_318}), FM.Enc.bool(True{})]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(Machine.Val.env{x_255, rest_256}, Source.Term.Tup{Source.Q2{}, a_317, b_318}, True{})), ks}},
                    FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(Machine.Val.env{x_255, rest_256}, a_317, True{})), Con{Fun.Fr{Code.F.Val.data.go.k2(), [FM.Enc.term(b_318), FM.Enc.term(a_317), FM.Enc.p(FM.Enc.term(a_317), FM.Enc.term(b_318)), FM.Enc.quan(Source.Q2{}), Fun.V.z{}, Fun.V.z{}, FM.Enc.val(rest_256), FM.Enc.val(x_255), FM.Enc.val(Machine.Val.env{x_255, rest_256}), FM.Enc.term(Source.Term.Tup{Source.Q2{}, a_317, b_318}), FM.Enc.bool(True{})]}, ks}}}),
                    Elim.Bool(Machine.Val.data.go(Machine.Val.env{x_255, rest_256}, a_317, True{}), m5 => Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go.k2(), [FM.Enc.bool(m5), FM.Enc.term(b_318), FM.Enc.term(a_317), FM.Enc.p(FM.Enc.term(a_317), FM.Enc.term(b_318)), FM.Enc.quan(Source.Q2{}), Fun.V.z{}, Fun.V.z{}, FM.Enc.val(rest_256), FM.Enc.val(x_255), FM.Enc.val(Machine.Val.env{x_255, rest_256}), FM.Enc.term(Source.Term.Tup{Source.Q2{}, a_317, b_318}), FM.Enc.bool(True{})], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(Bool.and(m5, Machine.Val.data.go(Machine.Val.env{x_255, rest_256}, b_318, True{}))), ks}}),
                    (2n, {==}),
                    FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go.k2(), [FM.Enc.bool(True{}), FM.Enc.term(b_318), FM.Enc.term(a_317), FM.Enc.p(FM.Enc.term(a_317), FM.Enc.term(b_318)), FM.Enc.quan(Source.Q2{}), Fun.V.z{}, Fun.V.z{}, FM.Enc.val(rest_256), FM.Enc.val(x_255), FM.Enc.val(Machine.Val.env{x_255, rest_256}), FM.Enc.term(Source.Term.Tup{Source.Q2{}, a_317, b_318}), FM.Enc.bool(True{})], ks}}, Fun.F.iter(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go.k2(), [FM.Enc.bool(True{}), FM.Enc.term(b_318), FM.Enc.term(a_317), FM.Enc.p(FM.Enc.term(a_317), FM.Enc.term(b_318)), FM.Enc.quan(Source.Q2{}), Fun.V.z{}, Fun.V.z{}, FM.Enc.val(rest_256), FM.Enc.val(x_255), FM.Enc.val(Machine.Val.env{x_255, rest_256}), FM.Enc.term(Source.Term.Tup{Source.Q2{}, a_317, b_318}), FM.Enc.bool(True{})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Bool.and(True{}, Machine.Val.data.go(Machine.Val.env{x_255, rest_256}, b_318, True{}))), ks}},
                    FP.Reach.steps(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go.k2(), [FM.Enc.bool(True{}), FM.Enc.term(b_318), FM.Enc.term(a_317), FM.Enc.p(FM.Enc.term(a_317), FM.Enc.term(b_318)), FM.Enc.quan(Source.Q2{}), Fun.V.z{}, Fun.V.z{}, FM.Enc.val(rest_256), FM.Enc.val(x_255), FM.Enc.val(Machine.Val.env{x_255, rest_256}), FM.Enc.term(Source.Term.Tup{Source.Q2{}, a_317, b_318}), FM.Enc.bool(True{})], ks}}),
                    L.Val.data.go(Machine.Val.env{x_255, rest_256}, True{}, b_318, ks))))))
            case Source.Term.Prj{+_h_321}:
              (8n, {==})
            case Source.Term.Enu{+_ks_322}:
              (8n, {==})
            case Source.Term.Lab{+k_323}:
              (7n, {==})
            case Source.Term.Mat{+_k_324, +_h_325, +_m_326}:
              (8n, {==})
            case Source.Term.Efq{}:
              (8n, {==})
            case Source.Term.Eql{+_a_327, +_b_328, +_t_329}:
              (8n, {==})
            case Source.Term.Rfl{}:
              (8n, {==})
            case Source.Term.Rwt{+_e_330, +_p_331, +_f_332}:
              (8n, {==})
    case Machine.Val.arg{+_q_333, +_x_334, +_rest_335}:
      (7n, {==})
    case Machine.Val.clo{+t2_336, +e2_337}:
      match c_180:
        case False{}:
          FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go(), [FM.Enc.val(Machine.Val.clo{t2_336, e2_337}), FM.Enc.term(t_179), FM.Enc.bool(False{})], ks}}, Fun.F.iter(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go(), [FM.Enc.val(Machine.Val.clo{t2_336, e2_337}), FM.Enc.term(t_179), FM.Enc.bool(False{})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(Machine.Val.clo{t2_336, e2_337}, t_179, False{})), ks}},
            FP.Reach.steps(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go(), [FM.Enc.val(Machine.Val.clo{t2_336, e2_337}), FM.Enc.term(t_179), FM.Enc.bool(False{})], ks}}),
            L.Val.data.go(e2_337, True{}, t2_336, ks))
        case True{}:
          (5n, {==})
    case Machine.Val.lab{+k_338}:
      match c_180:
        case False{}:
          (7n, {==})
        case True{}:
          (7n, {==})
    case Machine.Val.rfl{}:
      match c_180:
        case False{}:
          (8n, {==})
        case True{}:
          (8n, {==})
    case Machine.Val.tup{+q_339, +a_340, +b_341}:
      match c_180:
        case False{}:
          Elim.Quan(q_339, m6 => Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go(), [FM.Enc.val(Machine.Val.tup{m6, a_340, b_341}), FM.Enc.term(t_179), FM.Enc.bool(False{})], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(Machine.Val.tup{m6, a_340, b_341}, t_179, False{})), ks}}),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go(), [FM.Enc.val(Machine.Val.tup{Source.Q0{}, a_340, b_341}), FM.Enc.term(t_179), FM.Enc.bool(False{})], ks}}, Fun.F.iter(8n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go(), [FM.Enc.val(Machine.Val.tup{Source.Q0{}, a_340, b_341}), FM.Enc.term(t_179), FM.Enc.bool(False{})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(Machine.Val.tup{Source.Q0{}, a_340, b_341}, t_179, False{})), ks}},
            FP.Reach.steps(8n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go(), [FM.Enc.val(Machine.Val.tup{Source.Q0{}, a_340, b_341}), FM.Enc.term(t_179), FM.Enc.bool(False{})], ks}}),
            L.Val.data.go(b_341, False{}, t_179, ks)),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go(), [FM.Enc.val(Machine.Val.tup{Source.Q1{}, a_340, b_341}), FM.Enc.term(t_179), FM.Enc.bool(False{})], ks}}, Fun.F.iter(8n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go(), [FM.Enc.val(Machine.Val.tup{Source.Q1{}, a_340, b_341}), FM.Enc.term(t_179), FM.Enc.bool(False{})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(Machine.Val.tup{Source.Q1{}, a_340, b_341}, t_179, False{})), ks}},
            FP.Reach.steps(8n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go(), [FM.Enc.val(Machine.Val.tup{Source.Q1{}, a_340, b_341}), FM.Enc.term(t_179), FM.Enc.bool(False{})], ks}}),
            FP.Reach.trans(Code.prog(), Fun.F.iter(8n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go(), [FM.Enc.val(Machine.Val.tup{Source.Q1{}, a_340, b_341}), FM.Enc.term(t_179), FM.Enc.bool(False{})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(a_340, t_179, False{})), Con{Fun.Fr{Code.F.Val.data.go.k3(), [Fun.V.z{}, Fun.V.z{}, FM.Enc.val(b_341), FM.Enc.val(a_340), FM.Enc.p(FM.Enc.val(a_340), FM.Enc.val(b_341)), FM.Enc.quan(Source.Q1{}), FM.Enc.val(Machine.Val.tup{Source.Q1{}, a_340, b_341}), FM.Enc.term(t_179), FM.Enc.bool(False{})]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(Machine.Val.tup{Source.Q1{}, a_340, b_341}, t_179, False{})), ks}},
            L.Val.data.go(a_340, False{}, t_179, Con{Fun.Fr{Code.F.Val.data.go.k3(), [Fun.V.z{}, Fun.V.z{}, FM.Enc.val(b_341), FM.Enc.val(a_340), FM.Enc.p(FM.Enc.val(a_340), FM.Enc.val(b_341)), FM.Enc.quan(Source.Q1{}), FM.Enc.val(Machine.Val.tup{Source.Q1{}, a_340, b_341}), FM.Enc.term(t_179), FM.Enc.bool(False{})]}, ks}),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(a_340, t_179, False{})), Con{Fun.Fr{Code.F.Val.data.go.k3(), [Fun.V.z{}, Fun.V.z{}, FM.Enc.val(b_341), FM.Enc.val(a_340), FM.Enc.p(FM.Enc.val(a_340), FM.Enc.val(b_341)), FM.Enc.quan(Source.Q1{}), FM.Enc.val(Machine.Val.tup{Source.Q1{}, a_340, b_341}), FM.Enc.term(t_179), FM.Enc.bool(False{})]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(a_340, t_179, False{})), Con{Fun.Fr{Code.F.Val.data.go.k3(), [Fun.V.z{}, Fun.V.z{}, FM.Enc.val(b_341), FM.Enc.val(a_340), FM.Enc.p(FM.Enc.val(a_340), FM.Enc.val(b_341)), FM.Enc.quan(Source.Q1{}), FM.Enc.val(Machine.Val.tup{Source.Q1{}, a_340, b_341}), FM.Enc.term(t_179), FM.Enc.bool(False{})]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(Machine.Val.tup{Source.Q1{}, a_340, b_341}, t_179, False{})), ks}},
            FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(a_340, t_179, False{})), Con{Fun.Fr{Code.F.Val.data.go.k3(), [Fun.V.z{}, Fun.V.z{}, FM.Enc.val(b_341), FM.Enc.val(a_340), FM.Enc.p(FM.Enc.val(a_340), FM.Enc.val(b_341)), FM.Enc.quan(Source.Q1{}), FM.Enc.val(Machine.Val.tup{Source.Q1{}, a_340, b_341}), FM.Enc.term(t_179), FM.Enc.bool(False{})]}, ks}}}),
            Elim.Bool(Machine.Val.data.go(a_340, t_179, False{}), m7 => Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go.k3(), [FM.Enc.bool(m7), Fun.V.z{}, Fun.V.z{}, FM.Enc.val(b_341), FM.Enc.val(a_340), FM.Enc.p(FM.Enc.val(a_340), FM.Enc.val(b_341)), FM.Enc.quan(Source.Q1{}), FM.Enc.val(Machine.Val.tup{Source.Q1{}, a_340, b_341}), FM.Enc.term(t_179), FM.Enc.bool(False{})], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(Bool.and(m7, Machine.Val.data.go(b_341, t_179, False{}))), ks}}),
            (2n, {==}),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go.k3(), [FM.Enc.bool(True{}), Fun.V.z{}, Fun.V.z{}, FM.Enc.val(b_341), FM.Enc.val(a_340), FM.Enc.p(FM.Enc.val(a_340), FM.Enc.val(b_341)), FM.Enc.quan(Source.Q1{}), FM.Enc.val(Machine.Val.tup{Source.Q1{}, a_340, b_341}), FM.Enc.term(t_179), FM.Enc.bool(False{})], ks}}, Fun.F.iter(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go.k3(), [FM.Enc.bool(True{}), Fun.V.z{}, Fun.V.z{}, FM.Enc.val(b_341), FM.Enc.val(a_340), FM.Enc.p(FM.Enc.val(a_340), FM.Enc.val(b_341)), FM.Enc.quan(Source.Q1{}), FM.Enc.val(Machine.Val.tup{Source.Q1{}, a_340, b_341}), FM.Enc.term(t_179), FM.Enc.bool(False{})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Bool.and(True{}, Machine.Val.data.go(b_341, t_179, False{}))), ks}},
            FP.Reach.steps(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go.k3(), [FM.Enc.bool(True{}), Fun.V.z{}, Fun.V.z{}, FM.Enc.val(b_341), FM.Enc.val(a_340), FM.Enc.p(FM.Enc.val(a_340), FM.Enc.val(b_341)), FM.Enc.quan(Source.Q1{}), FM.Enc.val(Machine.Val.tup{Source.Q1{}, a_340, b_341}), FM.Enc.term(t_179), FM.Enc.bool(False{})], ks}}),
            L.Val.data.go(b_341, False{}, t_179, ks)))))),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go(), [FM.Enc.val(Machine.Val.tup{Source.Q2{}, a_340, b_341}), FM.Enc.term(t_179), FM.Enc.bool(False{})], ks}}, Fun.F.iter(8n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go(), [FM.Enc.val(Machine.Val.tup{Source.Q2{}, a_340, b_341}), FM.Enc.term(t_179), FM.Enc.bool(False{})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(Machine.Val.tup{Source.Q2{}, a_340, b_341}, t_179, False{})), ks}},
            FP.Reach.steps(8n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go(), [FM.Enc.val(Machine.Val.tup{Source.Q2{}, a_340, b_341}), FM.Enc.term(t_179), FM.Enc.bool(False{})], ks}}),
            FP.Reach.trans(Code.prog(), Fun.F.iter(8n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go(), [FM.Enc.val(Machine.Val.tup{Source.Q2{}, a_340, b_341}), FM.Enc.term(t_179), FM.Enc.bool(False{})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(a_340, t_179, False{})), Con{Fun.Fr{Code.F.Val.data.go.k3(), [Fun.V.z{}, Fun.V.z{}, FM.Enc.val(b_341), FM.Enc.val(a_340), FM.Enc.p(FM.Enc.val(a_340), FM.Enc.val(b_341)), FM.Enc.quan(Source.Q2{}), FM.Enc.val(Machine.Val.tup{Source.Q2{}, a_340, b_341}), FM.Enc.term(t_179), FM.Enc.bool(False{})]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(Machine.Val.tup{Source.Q2{}, a_340, b_341}, t_179, False{})), ks}},
            L.Val.data.go(a_340, False{}, t_179, Con{Fun.Fr{Code.F.Val.data.go.k3(), [Fun.V.z{}, Fun.V.z{}, FM.Enc.val(b_341), FM.Enc.val(a_340), FM.Enc.p(FM.Enc.val(a_340), FM.Enc.val(b_341)), FM.Enc.quan(Source.Q2{}), FM.Enc.val(Machine.Val.tup{Source.Q2{}, a_340, b_341}), FM.Enc.term(t_179), FM.Enc.bool(False{})]}, ks}),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(a_340, t_179, False{})), Con{Fun.Fr{Code.F.Val.data.go.k3(), [Fun.V.z{}, Fun.V.z{}, FM.Enc.val(b_341), FM.Enc.val(a_340), FM.Enc.p(FM.Enc.val(a_340), FM.Enc.val(b_341)), FM.Enc.quan(Source.Q2{}), FM.Enc.val(Machine.Val.tup{Source.Q2{}, a_340, b_341}), FM.Enc.term(t_179), FM.Enc.bool(False{})]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(a_340, t_179, False{})), Con{Fun.Fr{Code.F.Val.data.go.k3(), [Fun.V.z{}, Fun.V.z{}, FM.Enc.val(b_341), FM.Enc.val(a_340), FM.Enc.p(FM.Enc.val(a_340), FM.Enc.val(b_341)), FM.Enc.quan(Source.Q2{}), FM.Enc.val(Machine.Val.tup{Source.Q2{}, a_340, b_341}), FM.Enc.term(t_179), FM.Enc.bool(False{})]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(Machine.Val.tup{Source.Q2{}, a_340, b_341}, t_179, False{})), ks}},
            FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(a_340, t_179, False{})), Con{Fun.Fr{Code.F.Val.data.go.k3(), [Fun.V.z{}, Fun.V.z{}, FM.Enc.val(b_341), FM.Enc.val(a_340), FM.Enc.p(FM.Enc.val(a_340), FM.Enc.val(b_341)), FM.Enc.quan(Source.Q2{}), FM.Enc.val(Machine.Val.tup{Source.Q2{}, a_340, b_341}), FM.Enc.term(t_179), FM.Enc.bool(False{})]}, ks}}}),
            Elim.Bool(Machine.Val.data.go(a_340, t_179, False{}), m8 => Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go.k3(), [FM.Enc.bool(m8), Fun.V.z{}, Fun.V.z{}, FM.Enc.val(b_341), FM.Enc.val(a_340), FM.Enc.p(FM.Enc.val(a_340), FM.Enc.val(b_341)), FM.Enc.quan(Source.Q2{}), FM.Enc.val(Machine.Val.tup{Source.Q2{}, a_340, b_341}), FM.Enc.term(t_179), FM.Enc.bool(False{})], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(Bool.and(m8, Machine.Val.data.go(b_341, t_179, False{}))), ks}}),
            (2n, {==}),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go.k3(), [FM.Enc.bool(True{}), Fun.V.z{}, Fun.V.z{}, FM.Enc.val(b_341), FM.Enc.val(a_340), FM.Enc.p(FM.Enc.val(a_340), FM.Enc.val(b_341)), FM.Enc.quan(Source.Q2{}), FM.Enc.val(Machine.Val.tup{Source.Q2{}, a_340, b_341}), FM.Enc.term(t_179), FM.Enc.bool(False{})], ks}}, Fun.F.iter(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go.k3(), [FM.Enc.bool(True{}), Fun.V.z{}, Fun.V.z{}, FM.Enc.val(b_341), FM.Enc.val(a_340), FM.Enc.p(FM.Enc.val(a_340), FM.Enc.val(b_341)), FM.Enc.quan(Source.Q2{}), FM.Enc.val(Machine.Val.tup{Source.Q2{}, a_340, b_341}), FM.Enc.term(t_179), FM.Enc.bool(False{})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Bool.and(True{}, Machine.Val.data.go(b_341, t_179, False{}))), ks}},
            FP.Reach.steps(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go.k3(), [FM.Enc.bool(True{}), Fun.V.z{}, Fun.V.z{}, FM.Enc.val(b_341), FM.Enc.val(a_340), FM.Enc.p(FM.Enc.val(a_340), FM.Enc.val(b_341)), FM.Enc.quan(Source.Q2{}), FM.Enc.val(Machine.Val.tup{Source.Q2{}, a_340, b_341}), FM.Enc.term(t_179), FM.Enc.bool(False{})], ks}}),
            L.Val.data.go(b_341, False{}, t_179, ks)))))))
        case True{}:
          (7n, {==})
    case Machine.Val.call{+_k_344, +_xs_345}:
      (7n, {==})

def L.Val.is_data(+x_346: Machine.Val, +ks: List<&2, Fun.Fr>) ->
  Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.is_data(), [FM.Enc.val(x_346)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.is_data(x_346)), ks}}):
  FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.is_data(), [FM.Enc.val(x_346)], ks}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.is_data(), [FM.Enc.val(x_346)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.is_data(x_346)), ks}},
    FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.is_data(), [FM.Enc.val(x_346)], ks}}),
    L.Val.data.go(x_346, False{}, Source.Term.Efq{}, ks))

def L.Val.observe(+v_347: Machine.Val, +ks: List<&2, Fun.Fr>) ->
  Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.observe(), [FM.Enc.val(v_347)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.mobs(Machine.Val.observe(v_347)), ks}}):
  match v_347:
    case Machine.Val.nil{}:
      (4n, {==})
    case Machine.Val.env{+_x_348, +_rest_349}:
      (4n, {==})
    case Machine.Val.arg{+_q_350, +_x_351, +_rest_352}:
      (4n, {==})
    case Machine.Val.clo{+_t_353, +_e_354}:
      (4n, {==})
    case Machine.Val.lab{+k_355}:
      (4n, {==})
    case Machine.Val.rfl{}:
      (4n, {==})
    case Machine.Val.tup{+q_356, +a_357, +b_358}:
      FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.observe(), [FM.Enc.val(Machine.Val.tup{q_356, a_357, b_358})], ks}}, Fun.F.iter(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.observe(), [FM.Enc.val(Machine.Val.tup{q_356, a_357, b_358})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.mobs(Machine.Val.observe(Machine.Val.tup{q_356, a_357, b_358})), ks}},
        FP.Reach.steps(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.observe(), [FM.Enc.val(Machine.Val.tup{q_356, a_357, b_358})], ks}}),
        FP.Reach.trans(Code.prog(), Fun.F.iter(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.observe(), [FM.Enc.val(Machine.Val.tup{q_356, a_357, b_358})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.mobs(Machine.Val.observe(b_358)), Con{Fun.Fr{Code.F.Val.observe.k1(), [FM.Enc.val(b_358), FM.Enc.val(a_357), FM.Enc.p(FM.Enc.val(a_357), FM.Enc.val(b_358)), FM.Enc.quan(q_356), FM.Enc.val(Machine.Val.tup{q_356, a_357, b_358})]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.mobs(Machine.Val.observe(Machine.Val.tup{q_356, a_357, b_358})), ks}},
        L.Val.observe(b_358, Con{Fun.Fr{Code.F.Val.observe.k1(), [FM.Enc.val(b_358), FM.Enc.val(a_357), FM.Enc.p(FM.Enc.val(a_357), FM.Enc.val(b_358)), FM.Enc.quan(q_356), FM.Enc.val(Machine.Val.tup{q_356, a_357, b_358})]}, ks}),
        FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.mobs(Machine.Val.observe(b_358)), Con{Fun.Fr{Code.F.Val.observe.k1(), [FM.Enc.val(b_358), FM.Enc.val(a_357), FM.Enc.p(FM.Enc.val(a_357), FM.Enc.val(b_358)), FM.Enc.quan(q_356), FM.Enc.val(Machine.Val.tup{q_356, a_357, b_358})]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.mobs(Machine.Val.observe(b_358)), Con{Fun.Fr{Code.F.Val.observe.k1(), [FM.Enc.val(b_358), FM.Enc.val(a_357), FM.Enc.p(FM.Enc.val(a_357), FM.Enc.val(b_358)), FM.Enc.quan(q_356), FM.Enc.val(Machine.Val.tup{q_356, a_357, b_358})]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.mobs(Machine.Val.observe(Machine.Val.tup{q_356, a_357, b_358})), ks}},
        FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.mobs(Machine.Val.observe(b_358)), Con{Fun.Fr{Code.F.Val.observe.k1(), [FM.Enc.val(b_358), FM.Enc.val(a_357), FM.Enc.p(FM.Enc.val(a_357), FM.Enc.val(b_358)), FM.Enc.quan(q_356), FM.Enc.val(Machine.Val.tup{q_356, a_357, b_358})]}, ks}}}),
        Elim.MObs(Machine.Val.observe(b_358), m9 => Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.observe.k1(), [FM.Enc.mobs(m9), FM.Enc.val(b_358), FM.Enc.val(a_357), FM.Enc.p(FM.Enc.val(a_357), FM.Enc.val(b_358)), FM.Enc.quan(q_356), FM.Enc.val(Machine.Val.tup{q_356, a_357, b_358})], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.mobs(Source.Obs.tup.of(m9, Source.Quan.live(q_356), Machine.Val.observe(a_357))), ks}}),
        (2n, {==}),
        +y_360 => Elim.Quan(q_356, m10 => Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.observe.k1(), [FM.Enc.mobs(Some{y_360}), FM.Enc.val(b_358), FM.Enc.val(a_357), FM.Enc.p(FM.Enc.val(a_357), FM.Enc.val(b_358)), FM.Enc.quan(m10), FM.Enc.val(Machine.Val.tup{m10, a_357, b_358})], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.mobs(Source.Obs.tup.of(Some{y_360}, Source.Quan.live(m10), Machine.Val.observe(a_357))), ks}}),
        (5n, {==}),
        FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.observe.k1(), [FM.Enc.mobs(Some{y_360}), FM.Enc.val(b_358), FM.Enc.val(a_357), FM.Enc.p(FM.Enc.val(a_357), FM.Enc.val(b_358)), FM.Enc.quan(Source.Q1{}), FM.Enc.val(Machine.Val.tup{Source.Q1{}, a_357, b_358})], ks}}, Fun.F.iter(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.observe.k1(), [FM.Enc.mobs(Some{y_360}), FM.Enc.val(b_358), FM.Enc.val(a_357), FM.Enc.p(FM.Enc.val(a_357), FM.Enc.val(b_358)), FM.Enc.quan(Source.Q1{}), FM.Enc.val(Machine.Val.tup{Source.Q1{}, a_357, b_358})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.mobs(Source.Obs.tup.of(Some{y_360}, Source.Quan.live(Source.Q1{}), Machine.Val.observe(a_357))), ks}},
        FP.Reach.steps(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.observe.k1(), [FM.Enc.mobs(Some{y_360}), FM.Enc.val(b_358), FM.Enc.val(a_357), FM.Enc.p(FM.Enc.val(a_357), FM.Enc.val(b_358)), FM.Enc.quan(Source.Q1{}), FM.Enc.val(Machine.Val.tup{Source.Q1{}, a_357, b_358})], ks}}),
        FP.Reach.trans(Code.prog(), Fun.F.iter(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.observe.k1(), [FM.Enc.mobs(Some{y_360}), FM.Enc.val(b_358), FM.Enc.val(a_357), FM.Enc.p(FM.Enc.val(a_357), FM.Enc.val(b_358)), FM.Enc.quan(Source.Q1{}), FM.Enc.val(Machine.Val.tup{Source.Q1{}, a_357, b_358})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.mobs(Machine.Val.observe(a_357)), Con{Fun.Fr{Code.F.Val.observe.k2(), [Fun.V.z{}, FM.Enc.obs(y_360), FM.Enc.mobs(Some{y_360}), FM.Enc.val(b_358), FM.Enc.val(a_357), FM.Enc.p(FM.Enc.val(a_357), FM.Enc.val(b_358)), FM.Enc.quan(Source.Q1{}), FM.Enc.val(Machine.Val.tup{Source.Q1{}, a_357, b_358})]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.mobs(Source.Obs.tup.of(Some{y_360}, Source.Quan.live(Source.Q1{}), Machine.Val.observe(a_357))), ks}},
        L.Val.observe(a_357, Con{Fun.Fr{Code.F.Val.observe.k2(), [Fun.V.z{}, FM.Enc.obs(y_360), FM.Enc.mobs(Some{y_360}), FM.Enc.val(b_358), FM.Enc.val(a_357), FM.Enc.p(FM.Enc.val(a_357), FM.Enc.val(b_358)), FM.Enc.quan(Source.Q1{}), FM.Enc.val(Machine.Val.tup{Source.Q1{}, a_357, b_358})]}, ks}),
        FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.mobs(Machine.Val.observe(a_357)), Con{Fun.Fr{Code.F.Val.observe.k2(), [Fun.V.z{}, FM.Enc.obs(y_360), FM.Enc.mobs(Some{y_360}), FM.Enc.val(b_358), FM.Enc.val(a_357), FM.Enc.p(FM.Enc.val(a_357), FM.Enc.val(b_358)), FM.Enc.quan(Source.Q1{}), FM.Enc.val(Machine.Val.tup{Source.Q1{}, a_357, b_358})]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.mobs(Machine.Val.observe(a_357)), Con{Fun.Fr{Code.F.Val.observe.k2(), [Fun.V.z{}, FM.Enc.obs(y_360), FM.Enc.mobs(Some{y_360}), FM.Enc.val(b_358), FM.Enc.val(a_357), FM.Enc.p(FM.Enc.val(a_357), FM.Enc.val(b_358)), FM.Enc.quan(Source.Q1{}), FM.Enc.val(Machine.Val.tup{Source.Q1{}, a_357, b_358})]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.mobs(Source.Obs.tup.of(Some{y_360}, Source.Quan.live(Source.Q1{}), Machine.Val.observe(a_357))), ks}},
        FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.mobs(Machine.Val.observe(a_357)), Con{Fun.Fr{Code.F.Val.observe.k2(), [Fun.V.z{}, FM.Enc.obs(y_360), FM.Enc.mobs(Some{y_360}), FM.Enc.val(b_358), FM.Enc.val(a_357), FM.Enc.p(FM.Enc.val(a_357), FM.Enc.val(b_358)), FM.Enc.quan(Source.Q1{}), FM.Enc.val(Machine.Val.tup{Source.Q1{}, a_357, b_358})]}, ks}}}),
        Elim.MObs(Machine.Val.observe(a_357), m11 => Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.observe.k2(), [FM.Enc.mobs(m11), Fun.V.z{}, FM.Enc.obs(y_360), FM.Enc.mobs(Some{y_360}), FM.Enc.val(b_358), FM.Enc.val(a_357), FM.Enc.p(FM.Enc.val(a_357), FM.Enc.val(b_358)), FM.Enc.quan(Source.Q1{}), FM.Enc.val(Machine.Val.tup{Source.Q1{}, a_357, b_358})], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.mobs(Source.Obs.tup.of(Some{y_360}, Source.Quan.live(Source.Q1{}), m11)), ks}}),
        (2n, {==}),
        +x_362 => (4n, {==}))))),
        FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.observe.k1(), [FM.Enc.mobs(Some{y_360}), FM.Enc.val(b_358), FM.Enc.val(a_357), FM.Enc.p(FM.Enc.val(a_357), FM.Enc.val(b_358)), FM.Enc.quan(Source.Q2{}), FM.Enc.val(Machine.Val.tup{Source.Q2{}, a_357, b_358})], ks}}, Fun.F.iter(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.observe.k1(), [FM.Enc.mobs(Some{y_360}), FM.Enc.val(b_358), FM.Enc.val(a_357), FM.Enc.p(FM.Enc.val(a_357), FM.Enc.val(b_358)), FM.Enc.quan(Source.Q2{}), FM.Enc.val(Machine.Val.tup{Source.Q2{}, a_357, b_358})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.mobs(Source.Obs.tup.of(Some{y_360}, Source.Quan.live(Source.Q2{}), Machine.Val.observe(a_357))), ks}},
        FP.Reach.steps(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.observe.k1(), [FM.Enc.mobs(Some{y_360}), FM.Enc.val(b_358), FM.Enc.val(a_357), FM.Enc.p(FM.Enc.val(a_357), FM.Enc.val(b_358)), FM.Enc.quan(Source.Q2{}), FM.Enc.val(Machine.Val.tup{Source.Q2{}, a_357, b_358})], ks}}),
        FP.Reach.trans(Code.prog(), Fun.F.iter(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.observe.k1(), [FM.Enc.mobs(Some{y_360}), FM.Enc.val(b_358), FM.Enc.val(a_357), FM.Enc.p(FM.Enc.val(a_357), FM.Enc.val(b_358)), FM.Enc.quan(Source.Q2{}), FM.Enc.val(Machine.Val.tup{Source.Q2{}, a_357, b_358})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.mobs(Machine.Val.observe(a_357)), Con{Fun.Fr{Code.F.Val.observe.k2(), [Fun.V.z{}, FM.Enc.obs(y_360), FM.Enc.mobs(Some{y_360}), FM.Enc.val(b_358), FM.Enc.val(a_357), FM.Enc.p(FM.Enc.val(a_357), FM.Enc.val(b_358)), FM.Enc.quan(Source.Q2{}), FM.Enc.val(Machine.Val.tup{Source.Q2{}, a_357, b_358})]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.mobs(Source.Obs.tup.of(Some{y_360}, Source.Quan.live(Source.Q2{}), Machine.Val.observe(a_357))), ks}},
        L.Val.observe(a_357, Con{Fun.Fr{Code.F.Val.observe.k2(), [Fun.V.z{}, FM.Enc.obs(y_360), FM.Enc.mobs(Some{y_360}), FM.Enc.val(b_358), FM.Enc.val(a_357), FM.Enc.p(FM.Enc.val(a_357), FM.Enc.val(b_358)), FM.Enc.quan(Source.Q2{}), FM.Enc.val(Machine.Val.tup{Source.Q2{}, a_357, b_358})]}, ks}),
        FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.mobs(Machine.Val.observe(a_357)), Con{Fun.Fr{Code.F.Val.observe.k2(), [Fun.V.z{}, FM.Enc.obs(y_360), FM.Enc.mobs(Some{y_360}), FM.Enc.val(b_358), FM.Enc.val(a_357), FM.Enc.p(FM.Enc.val(a_357), FM.Enc.val(b_358)), FM.Enc.quan(Source.Q2{}), FM.Enc.val(Machine.Val.tup{Source.Q2{}, a_357, b_358})]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.mobs(Machine.Val.observe(a_357)), Con{Fun.Fr{Code.F.Val.observe.k2(), [Fun.V.z{}, FM.Enc.obs(y_360), FM.Enc.mobs(Some{y_360}), FM.Enc.val(b_358), FM.Enc.val(a_357), FM.Enc.p(FM.Enc.val(a_357), FM.Enc.val(b_358)), FM.Enc.quan(Source.Q2{}), FM.Enc.val(Machine.Val.tup{Source.Q2{}, a_357, b_358})]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.mobs(Source.Obs.tup.of(Some{y_360}, Source.Quan.live(Source.Q2{}), Machine.Val.observe(a_357))), ks}},
        FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.mobs(Machine.Val.observe(a_357)), Con{Fun.Fr{Code.F.Val.observe.k2(), [Fun.V.z{}, FM.Enc.obs(y_360), FM.Enc.mobs(Some{y_360}), FM.Enc.val(b_358), FM.Enc.val(a_357), FM.Enc.p(FM.Enc.val(a_357), FM.Enc.val(b_358)), FM.Enc.quan(Source.Q2{}), FM.Enc.val(Machine.Val.tup{Source.Q2{}, a_357, b_358})]}, ks}}}),
        Elim.MObs(Machine.Val.observe(a_357), m12 => Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.observe.k2(), [FM.Enc.mobs(m12), Fun.V.z{}, FM.Enc.obs(y_360), FM.Enc.mobs(Some{y_360}), FM.Enc.val(b_358), FM.Enc.val(a_357), FM.Enc.p(FM.Enc.val(a_357), FM.Enc.val(b_358)), FM.Enc.quan(Source.Q2{}), FM.Enc.val(Machine.Val.tup{Source.Q2{}, a_357, b_358})], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.mobs(Source.Obs.tup.of(Some{y_360}, Source.Quan.live(Source.Q2{}), m12)), ks}}),
        (2n, {==}),
        +x_364 => (4n, {==}))))))))))
    case Machine.Val.call{+_k_365, +_xs_366}:
      (4n, {==})

def L.Lam.takes(+p_367: Source.Quan, +q_368: Source.Quan, +x_369: Machine.Val, +ks: List<&2, Fun.Fr>) ->
  Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Lam.takes(), [FM.Enc.quan(p_367), FM.Enc.quan(q_368), FM.Enc.val(x_369)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Lam.takes(p_367, q_368, x_369)), ks}}):
  match p_367:
    case Source.Q0{}:
      match q_368:
        case Source.Q0{}:
          (3n, {==})
        case Source.Q1{}:
          (3n, {==})
        case Source.Q2{}:
          (3n, {==})
    case Source.Q1{}:
      match q_368:
        case Source.Q0{}:
          (4n, {==})
        case Source.Q1{}:
          (4n, {==})
        case Source.Q2{}:
          (4n, {==})
    case Source.Q2{}:
      match q_368:
        case Source.Q0{}:
          (4n, {==})
        case Source.Q1{}:
          FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Lam.takes(), [FM.Enc.quan(Source.Q2{}), FM.Enc.quan(Source.Q1{}), FM.Enc.val(x_369)], ks}}, Fun.F.iter(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Lam.takes(), [FM.Enc.quan(Source.Q2{}), FM.Enc.quan(Source.Q1{}), FM.Enc.val(x_369)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Lam.takes(Source.Q2{}, Source.Q1{}, x_369)), ks}},
            FP.Reach.steps(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Lam.takes(), [FM.Enc.quan(Source.Q2{}), FM.Enc.quan(Source.Q1{}), FM.Enc.val(x_369)], ks}}),
            L.Val.is_data(x_369, ks))
        case Source.Q2{}:
          FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Lam.takes(), [FM.Enc.quan(Source.Q2{}), FM.Enc.quan(Source.Q2{}), FM.Enc.val(x_369)], ks}}, Fun.F.iter(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Lam.takes(), [FM.Enc.quan(Source.Q2{}), FM.Enc.quan(Source.Q2{}), FM.Enc.val(x_369)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Lam.takes(Source.Q2{}, Source.Q2{}, x_369)), ks}},
            FP.Reach.steps(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Lam.takes(), [FM.Enc.quan(Source.Q2{}), FM.Enc.quan(Source.Q2{}), FM.Enc.val(x_369)], ks}}),
            L.Val.is_data(x_369, ks))

def L.Head.takes(+f_370: Source.Term, +xs_371: List<&2, Source.Arg>, +ks: List<&2, Fun.Fr>) ->
  Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Head.takes(), [FM.Enc.term(f_370)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Spine.head.takes(Source.Term.unspine(f_370, xs_371))), ks}}):
  match f_370:
    case Source.Term.Var{+_i_372}:
      (6n, {==})
    case Source.Term.Ref{+_k_373}:
      (6n, {==})
    case Source.Term.Ann{+_x_374, +_t_375}:
      (6n, {==})
    case Source.Term.Let{+_q_376, +_v_377, +_f_378}:
      (6n, {==})
    case Source.Term.Typ{+_q_379}:
      (6n, {==})
    case Source.Term.Min{+_a_380, +_b_381}:
      (6n, {==})
    case Source.Term.All{+_q_382, +_a_383, +_b_384}:
      (6n, {==})
    case Source.Term.Lam{+q_385, +b_386}:
      (3n, {==})
    case Source.Term.App{+q_387, +g_388, +x_389}:
      FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Head.takes(), [FM.Enc.term(Source.Term.App{q_387, g_388, x_389})], ks}}, Fun.F.iter(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Head.takes(), [FM.Enc.term(Source.Term.App{q_387, g_388, x_389})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Spine.head.takes(Source.Term.unspine(Source.Term.App{q_387, g_388, x_389}, xs_371))), ks}},
        FP.Reach.steps(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Head.takes(), [FM.Enc.term(Source.Term.App{q_387, g_388, x_389})], ks}}),
        L.Head.takes(g_388, Con{Source.Arg{q_387, x_389}, xs_371}, ks))
    case Source.Term.Sig{+_q_390, +_a_391, +_b_392}:
      (6n, {==})
    case Source.Term.Tup{+_q_393, +_a_394, +_b_395}:
      (6n, {==})
    case Source.Term.Prj{+h_396}:
      (4n, {==})
    case Source.Term.Enu{+_ks_397}:
      (6n, {==})
    case Source.Term.Lab{+_k_398}:
      (6n, {==})
    case Source.Term.Mat{+k_399, +h_400, +m_401}:
      (6n, {==})
    case Source.Term.Efq{}:
      (6n, {==})
    case Source.Term.Eql{+_a_402, +_b_403, +_t_404}:
      (6n, {==})
    case Source.Term.Rfl{}:
      (6n, {==})
    case Source.Term.Rwt{+_e_405, +_p_406, +_f_407}:
      (6n, {==})

def L.Walk.go(+t_408: Source.Term, +e_409: Machine.Val, +xs_410: Machine.Val, +ks: List<&2, Fun.Fr>) ->
  Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go(), [FM.Enc.term(t_408), FM.Enc.val(e_409), FM.Enc.val(xs_410)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Machine.Walk.go(t_408, e_409, xs_410)), ks}}):
  match t_408:
    case Source.Term.Var{+_i_411}:
      (8n, {==})
    case Source.Term.Ref{+_k_412}:
      (8n, {==})
    case Source.Term.Ann{+_x_413, +_t_414}:
      (8n, {==})
    case Source.Term.Let{+_q_415, +_v_416, +_f_417}:
      (8n, {==})
    case Source.Term.Typ{+_q_418}:
      (8n, {==})
    case Source.Term.Min{+_a_419, +_b_420}:
      (8n, {==})
    case Source.Term.All{+_q_421, +_a_422, +_b_423}:
      (8n, {==})
    case Source.Term.Lam{+p_424, +f_425}:
      match xs_410:
        case Machine.Val.nil{}:
          (3n, {==})
        case Machine.Val.env{+_x_426, +_rest_427}:
          (3n, {==})
        case Machine.Val.arg{+q_428, +x_429, +rest_430}:
          FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go(), [FM.Enc.term(Source.Term.Lam{p_424, f_425}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{q_428, x_429, rest_430})], ks}}, Fun.F.iter(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go(), [FM.Enc.term(Source.Term.Lam{p_424, f_425}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{q_428, x_429, rest_430})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Machine.Walk.go(Source.Term.Lam{p_424, f_425}, e_409, Machine.Val.arg{q_428, x_429, rest_430})), ks}},
            FP.Reach.steps(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go(), [FM.Enc.term(Source.Term.Lam{p_424, f_425}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{q_428, x_429, rest_430})], ks}}),
            FP.Reach.trans(Code.prog(), Fun.F.iter(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go(), [FM.Enc.term(Source.Term.Lam{p_424, f_425}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{q_428, x_429, rest_430})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Lam.takes(p_424, q_428, x_429)), Con{Fun.Fr{Code.F.Walk.go.k1(), [FM.Enc.val(rest_430), FM.Enc.val(x_429), FM.Enc.p(FM.Enc.val(x_429), FM.Enc.val(rest_430)), FM.Enc.quan(q_428), FM.Enc.term(f_425), FM.Enc.quan(p_424), FM.Enc.term(Source.Term.Lam{p_424, f_425}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{q_428, x_429, rest_430})]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Machine.Walk.go(Source.Term.Lam{p_424, f_425}, e_409, Machine.Val.arg{q_428, x_429, rest_430})), ks}},
            L.Lam.takes(p_424, q_428, x_429, Con{Fun.Fr{Code.F.Walk.go.k1(), [FM.Enc.val(rest_430), FM.Enc.val(x_429), FM.Enc.p(FM.Enc.val(x_429), FM.Enc.val(rest_430)), FM.Enc.quan(q_428), FM.Enc.term(f_425), FM.Enc.quan(p_424), FM.Enc.term(Source.Term.Lam{p_424, f_425}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{q_428, x_429, rest_430})]}, ks}),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Lam.takes(p_424, q_428, x_429)), Con{Fun.Fr{Code.F.Walk.go.k1(), [FM.Enc.val(rest_430), FM.Enc.val(x_429), FM.Enc.p(FM.Enc.val(x_429), FM.Enc.val(rest_430)), FM.Enc.quan(q_428), FM.Enc.term(f_425), FM.Enc.quan(p_424), FM.Enc.term(Source.Term.Lam{p_424, f_425}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{q_428, x_429, rest_430})]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Lam.takes(p_424, q_428, x_429)), Con{Fun.Fr{Code.F.Walk.go.k1(), [FM.Enc.val(rest_430), FM.Enc.val(x_429), FM.Enc.p(FM.Enc.val(x_429), FM.Enc.val(rest_430)), FM.Enc.quan(q_428), FM.Enc.term(f_425), FM.Enc.quan(p_424), FM.Enc.term(Source.Term.Lam{p_424, f_425}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{q_428, x_429, rest_430})]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Machine.Walk.go(Source.Term.Lam{p_424, f_425}, e_409, Machine.Val.arg{q_428, x_429, rest_430})), ks}},
            FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Lam.takes(p_424, q_428, x_429)), Con{Fun.Fr{Code.F.Walk.go.k1(), [FM.Enc.val(rest_430), FM.Enc.val(x_429), FM.Enc.p(FM.Enc.val(x_429), FM.Enc.val(rest_430)), FM.Enc.quan(q_428), FM.Enc.term(f_425), FM.Enc.quan(p_424), FM.Enc.term(Source.Term.Lam{p_424, f_425}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{q_428, x_429, rest_430})]}, ks}}}),
            Elim.Bool(Machine.Lam.takes(p_424, q_428, x_429), m13 => Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k1(), [FM.Enc.bool(m13), FM.Enc.val(rest_430), FM.Enc.val(x_429), FM.Enc.p(FM.Enc.val(x_429), FM.Enc.val(rest_430)), FM.Enc.quan(q_428), FM.Enc.term(f_425), FM.Enc.quan(p_424), FM.Enc.term(Source.Term.Lam{p_424, f_425}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{q_428, x_429, rest_430})], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Source.Bool.lazy(Machine.Leaf, m13, u => Machine.Walk.go(f_425, Machine.Val.env{x_429, e_409}, rest_430), u => Machine.Leaf.fail{})), ks}}),
            (2n, {==}),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k1(), [FM.Enc.bool(True{}), FM.Enc.val(rest_430), FM.Enc.val(x_429), FM.Enc.p(FM.Enc.val(x_429), FM.Enc.val(rest_430)), FM.Enc.quan(q_428), FM.Enc.term(f_425), FM.Enc.quan(p_424), FM.Enc.term(Source.Term.Lam{p_424, f_425}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{q_428, x_429, rest_430})], ks}}, Fun.F.iter(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k1(), [FM.Enc.bool(True{}), FM.Enc.val(rest_430), FM.Enc.val(x_429), FM.Enc.p(FM.Enc.val(x_429), FM.Enc.val(rest_430)), FM.Enc.quan(q_428), FM.Enc.term(f_425), FM.Enc.quan(p_424), FM.Enc.term(Source.Term.Lam{p_424, f_425}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{q_428, x_429, rest_430})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Source.Bool.lazy(Machine.Leaf, True{}, u => Machine.Walk.go(f_425, Machine.Val.env{x_429, e_409}, rest_430), u => Machine.Leaf.fail{})), ks}},
            FP.Reach.steps(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k1(), [FM.Enc.bool(True{}), FM.Enc.val(rest_430), FM.Enc.val(x_429), FM.Enc.p(FM.Enc.val(x_429), FM.Enc.val(rest_430)), FM.Enc.quan(q_428), FM.Enc.term(f_425), FM.Enc.quan(p_424), FM.Enc.term(Source.Term.Lam{p_424, f_425}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{q_428, x_429, rest_430})], ks}}),
            L.Walk.go(f_425, Machine.Val.env{x_429, e_409}, rest_430, ks))))))
        case Machine.Val.clo{+_t_432, +_e_433}:
          (3n, {==})
        case Machine.Val.lab{+_k_434}:
          (3n, {==})
        case Machine.Val.rfl{}:
          (3n, {==})
        case Machine.Val.tup{+_q_435, +_a_436, +_b_437}:
          (3n, {==})
        case Machine.Val.call{+_k_438, +_xs_439}:
          (3n, {==})
    case Source.Term.App{+q_440, +f_441, +x_442}:
      match x_442:
        case Source.Term.Var{+v_443}:
          FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go(), [FM.Enc.term(Source.Term.App{q_440, f_441, Source.Term.Var{v_443}}), FM.Enc.val(e_409), FM.Enc.val(xs_410)], ks}}, Fun.F.iter(8n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go(), [FM.Enc.term(Source.Term.App{q_440, f_441, Source.Term.Var{v_443}}), FM.Enc.val(e_409), FM.Enc.val(xs_410)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Machine.Walk.go(Source.Term.App{q_440, f_441, Source.Term.Var{v_443}}, e_409, xs_410)), ks}},
            FP.Reach.steps(8n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go(), [FM.Enc.term(Source.Term.App{q_440, f_441, Source.Term.Var{v_443}}), FM.Enc.val(e_409), FM.Enc.val(xs_410)], ks}}),
            FP.Reach.trans(Code.prog(), Fun.F.iter(8n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go(), [FM.Enc.term(Source.Term.App{q_440, f_441, Source.Term.Var{v_443}}), FM.Enc.val(e_409), FM.Enc.val(xs_410)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Spine.head.takes(Source.Term.unspine(f_441, Nil{}))), Con{Fun.Fr{Code.F.Walk.go.k2(), [Fun.V.z{}, FM.Enc.nat(v_443), FM.Enc.term(Source.Term.Var{v_443}), FM.Enc.term(f_441), FM.Enc.p(FM.Enc.term(f_441), FM.Enc.term(Source.Term.Var{v_443})), FM.Enc.quan(q_440), FM.Enc.term(Source.Term.App{q_440, f_441, Source.Term.Var{v_443}}), FM.Enc.val(e_409), FM.Enc.val(xs_410)]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Machine.Walk.go(Source.Term.App{q_440, f_441, Source.Term.Var{v_443}}, e_409, xs_410)), ks}},
            L.Head.takes(f_441, Nil{}, Con{Fun.Fr{Code.F.Walk.go.k2(), [Fun.V.z{}, FM.Enc.nat(v_443), FM.Enc.term(Source.Term.Var{v_443}), FM.Enc.term(f_441), FM.Enc.p(FM.Enc.term(f_441), FM.Enc.term(Source.Term.Var{v_443})), FM.Enc.quan(q_440), FM.Enc.term(Source.Term.App{q_440, f_441, Source.Term.Var{v_443}}), FM.Enc.val(e_409), FM.Enc.val(xs_410)]}, ks}),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Spine.head.takes(Source.Term.unspine(f_441, Nil{}))), Con{Fun.Fr{Code.F.Walk.go.k2(), [Fun.V.z{}, FM.Enc.nat(v_443), FM.Enc.term(Source.Term.Var{v_443}), FM.Enc.term(f_441), FM.Enc.p(FM.Enc.term(f_441), FM.Enc.term(Source.Term.Var{v_443})), FM.Enc.quan(q_440), FM.Enc.term(Source.Term.App{q_440, f_441, Source.Term.Var{v_443}}), FM.Enc.val(e_409), FM.Enc.val(xs_410)]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Spine.head.takes(Source.Term.unspine(f_441, Nil{}))), Con{Fun.Fr{Code.F.Walk.go.k2(), [Fun.V.z{}, FM.Enc.nat(v_443), FM.Enc.term(Source.Term.Var{v_443}), FM.Enc.term(f_441), FM.Enc.p(FM.Enc.term(f_441), FM.Enc.term(Source.Term.Var{v_443})), FM.Enc.quan(q_440), FM.Enc.term(Source.Term.App{q_440, f_441, Source.Term.Var{v_443}}), FM.Enc.val(e_409), FM.Enc.val(xs_410)]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Machine.Walk.go(Source.Term.App{q_440, f_441, Source.Term.Var{v_443}}, e_409, xs_410)), ks}},
            FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Spine.head.takes(Source.Term.unspine(f_441, Nil{}))), Con{Fun.Fr{Code.F.Walk.go.k2(), [Fun.V.z{}, FM.Enc.nat(v_443), FM.Enc.term(Source.Term.Var{v_443}), FM.Enc.term(f_441), FM.Enc.p(FM.Enc.term(f_441), FM.Enc.term(Source.Term.Var{v_443})), FM.Enc.quan(q_440), FM.Enc.term(Source.Term.App{q_440, f_441, Source.Term.Var{v_443}}), FM.Enc.val(e_409), FM.Enc.val(xs_410)]}, ks}}}),
            Elim.Bool(Source.Spine.head.takes(Source.Term.unspine(f_441, Nil{})), m14 => Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k2(), [FM.Enc.bool(m14), Fun.V.z{}, FM.Enc.nat(v_443), FM.Enc.term(Source.Term.Var{v_443}), FM.Enc.term(f_441), FM.Enc.p(FM.Enc.term(f_441), FM.Enc.term(Source.Term.Var{v_443})), FM.Enc.quan(q_440), FM.Enc.term(Source.Term.App{q_440, f_441, Source.Term.Var{v_443}}), FM.Enc.val(e_409), FM.Enc.val(xs_410)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Source.Bool.lazy(Machine.Leaf, m14, u => Machine.Walk.go(f_441, e_409, Machine.Val.arg{q_440, Machine.Env.get(e_409, v_443), xs_410}), u => Machine.Leaf.at{Source.Term.App{q_440, f_441, Source.Term.Var{v_443}}, e_409, xs_410})), ks}}),
            (4n, {==}),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k2(), [FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.nat(v_443), FM.Enc.term(Source.Term.Var{v_443}), FM.Enc.term(f_441), FM.Enc.p(FM.Enc.term(f_441), FM.Enc.term(Source.Term.Var{v_443})), FM.Enc.quan(q_440), FM.Enc.term(Source.Term.App{q_440, f_441, Source.Term.Var{v_443}}), FM.Enc.val(e_409), FM.Enc.val(xs_410)], ks}}, Fun.F.iter(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k2(), [FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.nat(v_443), FM.Enc.term(Source.Term.Var{v_443}), FM.Enc.term(f_441), FM.Enc.p(FM.Enc.term(f_441), FM.Enc.term(Source.Term.Var{v_443})), FM.Enc.quan(q_440), FM.Enc.term(Source.Term.App{q_440, f_441, Source.Term.Var{v_443}}), FM.Enc.val(e_409), FM.Enc.val(xs_410)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Source.Bool.lazy(Machine.Leaf, True{}, u => Machine.Walk.go(f_441, e_409, Machine.Val.arg{q_440, Machine.Env.get(e_409, v_443), xs_410}), u => Machine.Leaf.at{Source.Term.App{q_440, f_441, Source.Term.Var{v_443}}, e_409, xs_410})), ks}},
            FP.Reach.steps(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k2(), [FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.nat(v_443), FM.Enc.term(Source.Term.Var{v_443}), FM.Enc.term(f_441), FM.Enc.p(FM.Enc.term(f_441), FM.Enc.term(Source.Term.Var{v_443})), FM.Enc.quan(q_440), FM.Enc.term(Source.Term.App{q_440, f_441, Source.Term.Var{v_443}}), FM.Enc.val(e_409), FM.Enc.val(xs_410)], ks}}),
            FP.Reach.trans(Code.prog(), Fun.F.iter(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k2(), [FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.nat(v_443), FM.Enc.term(Source.Term.Var{v_443}), FM.Enc.term(f_441), FM.Enc.p(FM.Enc.term(f_441), FM.Enc.term(Source.Term.Var{v_443})), FM.Enc.quan(q_440), FM.Enc.term(Source.Term.App{q_440, f_441, Source.Term.Var{v_443}}), FM.Enc.val(e_409), FM.Enc.val(xs_410)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.val(Machine.Env.get(e_409, v_443)), Con{Fun.Fr{Code.F.Walk.go.k3(), [Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.nat(v_443), FM.Enc.term(Source.Term.Var{v_443}), FM.Enc.term(f_441), FM.Enc.p(FM.Enc.term(f_441), FM.Enc.term(Source.Term.Var{v_443})), FM.Enc.quan(q_440), FM.Enc.term(Source.Term.App{q_440, f_441, Source.Term.Var{v_443}}), FM.Enc.val(e_409), FM.Enc.val(xs_410)]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Source.Bool.lazy(Machine.Leaf, True{}, u => Machine.Walk.go(f_441, e_409, Machine.Val.arg{q_440, Machine.Env.get(e_409, v_443), xs_410}), u => Machine.Leaf.at{Source.Term.App{q_440, f_441, Source.Term.Var{v_443}}, e_409, xs_410})), ks}},
            L.Env.get(e_409, v_443, Con{Fun.Fr{Code.F.Walk.go.k3(), [Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.nat(v_443), FM.Enc.term(Source.Term.Var{v_443}), FM.Enc.term(f_441), FM.Enc.p(FM.Enc.term(f_441), FM.Enc.term(Source.Term.Var{v_443})), FM.Enc.quan(q_440), FM.Enc.term(Source.Term.App{q_440, f_441, Source.Term.Var{v_443}}), FM.Enc.val(e_409), FM.Enc.val(xs_410)]}, ks}),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.val(Machine.Env.get(e_409, v_443)), Con{Fun.Fr{Code.F.Walk.go.k3(), [Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.nat(v_443), FM.Enc.term(Source.Term.Var{v_443}), FM.Enc.term(f_441), FM.Enc.p(FM.Enc.term(f_441), FM.Enc.term(Source.Term.Var{v_443})), FM.Enc.quan(q_440), FM.Enc.term(Source.Term.App{q_440, f_441, Source.Term.Var{v_443}}), FM.Enc.val(e_409), FM.Enc.val(xs_410)]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.val(Machine.Env.get(e_409, v_443)), Con{Fun.Fr{Code.F.Walk.go.k3(), [Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.nat(v_443), FM.Enc.term(Source.Term.Var{v_443}), FM.Enc.term(f_441), FM.Enc.p(FM.Enc.term(f_441), FM.Enc.term(Source.Term.Var{v_443})), FM.Enc.quan(q_440), FM.Enc.term(Source.Term.App{q_440, f_441, Source.Term.Var{v_443}}), FM.Enc.val(e_409), FM.Enc.val(xs_410)]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Source.Bool.lazy(Machine.Leaf, True{}, u => Machine.Walk.go(f_441, e_409, Machine.Val.arg{q_440, Machine.Env.get(e_409, v_443), xs_410}), u => Machine.Leaf.at{Source.Term.App{q_440, f_441, Source.Term.Var{v_443}}, e_409, xs_410})), ks}},
            FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.val(Machine.Env.get(e_409, v_443)), Con{Fun.Fr{Code.F.Walk.go.k3(), [Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.nat(v_443), FM.Enc.term(Source.Term.Var{v_443}), FM.Enc.term(f_441), FM.Enc.p(FM.Enc.term(f_441), FM.Enc.term(Source.Term.Var{v_443})), FM.Enc.quan(q_440), FM.Enc.term(Source.Term.App{q_440, f_441, Source.Term.Var{v_443}}), FM.Enc.val(e_409), FM.Enc.val(xs_410)]}, ks}}}),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k3(), [FM.Enc.val(Machine.Env.get(e_409, v_443)), Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.nat(v_443), FM.Enc.term(Source.Term.Var{v_443}), FM.Enc.term(f_441), FM.Enc.p(FM.Enc.term(f_441), FM.Enc.term(Source.Term.Var{v_443})), FM.Enc.quan(q_440), FM.Enc.term(Source.Term.App{q_440, f_441, Source.Term.Var{v_443}}), FM.Enc.val(e_409), FM.Enc.val(xs_410)], ks}}, Fun.F.iter(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k3(), [FM.Enc.val(Machine.Env.get(e_409, v_443)), Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.nat(v_443), FM.Enc.term(Source.Term.Var{v_443}), FM.Enc.term(f_441), FM.Enc.p(FM.Enc.term(f_441), FM.Enc.term(Source.Term.Var{v_443})), FM.Enc.quan(q_440), FM.Enc.term(Source.Term.App{q_440, f_441, Source.Term.Var{v_443}}), FM.Enc.val(e_409), FM.Enc.val(xs_410)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Machine.Walk.go(f_441, e_409, Machine.Val.arg{q_440, Machine.Env.get(e_409, v_443), xs_410})), ks}},
            FP.Reach.steps(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k3(), [FM.Enc.val(Machine.Env.get(e_409, v_443)), Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.nat(v_443), FM.Enc.term(Source.Term.Var{v_443}), FM.Enc.term(f_441), FM.Enc.p(FM.Enc.term(f_441), FM.Enc.term(Source.Term.Var{v_443})), FM.Enc.quan(q_440), FM.Enc.term(Source.Term.App{q_440, f_441, Source.Term.Var{v_443}}), FM.Enc.val(e_409), FM.Enc.val(xs_410)], ks}}),
            L.Walk.go(f_441, e_409, Machine.Val.arg{q_440, Machine.Env.get(e_409, v_443), xs_410}, ks)))))))))
        case Source.Term.Ref{+_k_446}:
          (10n, {==})
        case Source.Term.Ann{+_x_447, +_t_448}:
          (10n, {==})
        case Source.Term.Let{+_q_449, +_v_450, +_f_451}:
          (10n, {==})
        case Source.Term.Typ{+_q_452}:
          (10n, {==})
        case Source.Term.Min{+_a_453, +_b_454}:
          (10n, {==})
        case Source.Term.All{+_q_455, +_a_456, +_b_457}:
          (10n, {==})
        case Source.Term.Lam{+_q_458, +_f_459}:
          (10n, {==})
        case Source.Term.App{+_q_460, +_f_461, +_x_462}:
          (10n, {==})
        case Source.Term.Sig{+_q_463, +_a_464, +_b_465}:
          (10n, {==})
        case Source.Term.Tup{+_q_466, +_a_467, +_b_468}:
          (10n, {==})
        case Source.Term.Prj{+_h_469}:
          (10n, {==})
        case Source.Term.Enu{+_ks_470}:
          (10n, {==})
        case Source.Term.Lab{+_k_471}:
          (10n, {==})
        case Source.Term.Mat{+_k_472, +_h_473, +_m_474}:
          (10n, {==})
        case Source.Term.Efq{}:
          (10n, {==})
        case Source.Term.Eql{+_a_475, +_b_476, +_t_477}:
          (10n, {==})
        case Source.Term.Rfl{}:
          (10n, {==})
        case Source.Term.Rwt{+_e_478, +_p_479, +_f_480}:
          (10n, {==})
    case Source.Term.Sig{+_q_481, +_a_482, +_b_483}:
      (8n, {==})
    case Source.Term.Tup{+_q_484, +_a_485, +_b_486}:
      (8n, {==})
    case Source.Term.Prj{+h_487}:
      match xs_410:
        case Machine.Val.nil{}:
          (4n, {==})
        case Machine.Val.env{+_x_488, +_rest_489}:
          (4n, {==})
        case Machine.Val.arg{+q_490, +x_491, +rest_492}:
          FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go(), [FM.Enc.term(Source.Term.Prj{h_487}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{q_490, x_491, rest_492})], ks}}, Fun.F.iter(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go(), [FM.Enc.term(Source.Term.Prj{h_487}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{q_490, x_491, rest_492})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Machine.Walk.go(Source.Term.Prj{h_487}, e_409, Machine.Val.arg{q_490, x_491, rest_492})), ks}},
            FP.Reach.steps(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go(), [FM.Enc.term(Source.Term.Prj{h_487}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{q_490, x_491, rest_492})], ks}}),
            FP.Reach.trans(Code.prog(), Fun.F.iter(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go(), [FM.Enc.term(Source.Term.Prj{h_487}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{q_490, x_491, rest_492})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.form(Machine.Val.form(x_491)), Con{Fun.Fr{Code.F.Walk.go.k4(), [FM.Enc.val(rest_492), FM.Enc.val(x_491), FM.Enc.p(FM.Enc.val(x_491), FM.Enc.val(rest_492)), FM.Enc.quan(q_490), Fun.V.z{}, FM.Enc.term(h_487), FM.Enc.term(Source.Term.Prj{h_487}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{q_490, x_491, rest_492})]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Machine.Walk.go(Source.Term.Prj{h_487}, e_409, Machine.Val.arg{q_490, x_491, rest_492})), ks}},
            L.Val.form(x_491, Con{Fun.Fr{Code.F.Walk.go.k4(), [FM.Enc.val(rest_492), FM.Enc.val(x_491), FM.Enc.p(FM.Enc.val(x_491), FM.Enc.val(rest_492)), FM.Enc.quan(q_490), Fun.V.z{}, FM.Enc.term(h_487), FM.Enc.term(Source.Term.Prj{h_487}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{q_490, x_491, rest_492})]}, ks}),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.form(Machine.Val.form(x_491)), Con{Fun.Fr{Code.F.Walk.go.k4(), [FM.Enc.val(rest_492), FM.Enc.val(x_491), FM.Enc.p(FM.Enc.val(x_491), FM.Enc.val(rest_492)), FM.Enc.quan(q_490), Fun.V.z{}, FM.Enc.term(h_487), FM.Enc.term(Source.Term.Prj{h_487}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{q_490, x_491, rest_492})]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.form(Machine.Val.form(x_491)), Con{Fun.Fr{Code.F.Walk.go.k4(), [FM.Enc.val(rest_492), FM.Enc.val(x_491), FM.Enc.p(FM.Enc.val(x_491), FM.Enc.val(rest_492)), FM.Enc.quan(q_490), Fun.V.z{}, FM.Enc.term(h_487), FM.Enc.term(Source.Term.Prj{h_487}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{q_490, x_491, rest_492})]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Machine.Walk.go(Source.Term.Prj{h_487}, e_409, Machine.Val.arg{q_490, x_491, rest_492})), ks}},
            FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.form(Machine.Val.form(x_491)), Con{Fun.Fr{Code.F.Walk.go.k4(), [FM.Enc.val(rest_492), FM.Enc.val(x_491), FM.Enc.p(FM.Enc.val(x_491), FM.Enc.val(rest_492)), FM.Enc.quan(q_490), Fun.V.z{}, FM.Enc.term(h_487), FM.Enc.term(Source.Term.Prj{h_487}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{q_490, x_491, rest_492})]}, ks}}}),
            Elim.Form(Machine.Val.form(x_491), m15 => Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k4(), [FM.Enc.form(m15), FM.Enc.val(rest_492), FM.Enc.val(x_491), FM.Enc.p(FM.Enc.val(x_491), FM.Enc.val(rest_492)), FM.Enc.quan(q_490), Fun.V.z{}, FM.Enc.term(h_487), FM.Enc.term(Source.Term.Prj{h_487}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{q_490, x_491, rest_492})], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Machine.Walk.prj.of(m15, q_490, rest_492, ys => Machine.Walk.go(h_487, e_409, ys))), ks}}),
            +r_494 => +a_495 => +b_496 => Elim.Quan(q_490, m16 => Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k4(), [FM.Enc.form(Machine.Form.tup{r_494, a_495, b_496}), FM.Enc.val(rest_492), FM.Enc.val(x_491), FM.Enc.p(FM.Enc.val(x_491), FM.Enc.val(rest_492)), FM.Enc.quan(m16), Fun.V.z{}, FM.Enc.term(h_487), FM.Enc.term(Source.Term.Prj{h_487}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{m16, x_491, rest_492})], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Machine.Walk.prj.of(Machine.Form.tup{r_494, a_495, b_496}, m16, rest_492, ys => Machine.Walk.go(h_487, e_409, ys))), ks}}),
            (4n, {==}),
            Elim.Quan(r_494, m17 => Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k4(), [FM.Enc.form(Machine.Form.tup{m17, a_495, b_496}), FM.Enc.val(rest_492), FM.Enc.val(x_491), FM.Enc.p(FM.Enc.val(x_491), FM.Enc.val(rest_492)), FM.Enc.quan(Source.Q1{}), Fun.V.z{}, FM.Enc.term(h_487), FM.Enc.term(Source.Term.Prj{h_487}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q1{}, x_491, rest_492})], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Machine.Walk.prj.of(Machine.Form.tup{m17, a_495, b_496}, Source.Q1{}, rest_492, ys => Machine.Walk.go(h_487, e_409, ys))), ks}}),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k4(), [FM.Enc.form(Machine.Form.tup{Source.Q0{}, a_495, b_496}), FM.Enc.val(rest_492), FM.Enc.val(x_491), FM.Enc.p(FM.Enc.val(x_491), FM.Enc.val(rest_492)), FM.Enc.quan(Source.Q1{}), Fun.V.z{}, FM.Enc.term(h_487), FM.Enc.term(Source.Term.Prj{h_487}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q1{}, x_491, rest_492})], ks}}, Fun.F.iter(9n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k4(), [FM.Enc.form(Machine.Form.tup{Source.Q0{}, a_495, b_496}), FM.Enc.val(rest_492), FM.Enc.val(x_491), FM.Enc.p(FM.Enc.val(x_491), FM.Enc.val(rest_492)), FM.Enc.quan(Source.Q1{}), Fun.V.z{}, FM.Enc.term(h_487), FM.Enc.term(Source.Term.Prj{h_487}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q1{}, x_491, rest_492})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Machine.Walk.prj.of(Machine.Form.tup{Source.Q0{}, a_495, b_496}, Source.Q1{}, rest_492, ys => Machine.Walk.go(h_487, e_409, ys))), ks}},
            FP.Reach.steps(9n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k4(), [FM.Enc.form(Machine.Form.tup{Source.Q0{}, a_495, b_496}), FM.Enc.val(rest_492), FM.Enc.val(x_491), FM.Enc.p(FM.Enc.val(x_491), FM.Enc.val(rest_492)), FM.Enc.quan(Source.Q1{}), Fun.V.z{}, FM.Enc.term(h_487), FM.Enc.term(Source.Term.Prj{h_487}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q1{}, x_491, rest_492})], ks}}),
            L.Walk.go(h_487, e_409, Machine.Val.arg{Source.Q0{}, a_495, Machine.Val.arg{Source.Q1{}, b_496, rest_492}}, ks)),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k4(), [FM.Enc.form(Machine.Form.tup{Source.Q1{}, a_495, b_496}), FM.Enc.val(rest_492), FM.Enc.val(x_491), FM.Enc.p(FM.Enc.val(x_491), FM.Enc.val(rest_492)), FM.Enc.quan(Source.Q1{}), Fun.V.z{}, FM.Enc.term(h_487), FM.Enc.term(Source.Term.Prj{h_487}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q1{}, x_491, rest_492})], ks}}, Fun.F.iter(9n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k4(), [FM.Enc.form(Machine.Form.tup{Source.Q1{}, a_495, b_496}), FM.Enc.val(rest_492), FM.Enc.val(x_491), FM.Enc.p(FM.Enc.val(x_491), FM.Enc.val(rest_492)), FM.Enc.quan(Source.Q1{}), Fun.V.z{}, FM.Enc.term(h_487), FM.Enc.term(Source.Term.Prj{h_487}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q1{}, x_491, rest_492})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Machine.Walk.prj.of(Machine.Form.tup{Source.Q1{}, a_495, b_496}, Source.Q1{}, rest_492, ys => Machine.Walk.go(h_487, e_409, ys))), ks}},
            FP.Reach.steps(9n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k4(), [FM.Enc.form(Machine.Form.tup{Source.Q1{}, a_495, b_496}), FM.Enc.val(rest_492), FM.Enc.val(x_491), FM.Enc.p(FM.Enc.val(x_491), FM.Enc.val(rest_492)), FM.Enc.quan(Source.Q1{}), Fun.V.z{}, FM.Enc.term(h_487), FM.Enc.term(Source.Term.Prj{h_487}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q1{}, x_491, rest_492})], ks}}),
            L.Walk.go(h_487, e_409, Machine.Val.arg{Source.Q1{}, a_495, Machine.Val.arg{Source.Q1{}, b_496, rest_492}}, ks)),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k4(), [FM.Enc.form(Machine.Form.tup{Source.Q2{}, a_495, b_496}), FM.Enc.val(rest_492), FM.Enc.val(x_491), FM.Enc.p(FM.Enc.val(x_491), FM.Enc.val(rest_492)), FM.Enc.quan(Source.Q1{}), Fun.V.z{}, FM.Enc.term(h_487), FM.Enc.term(Source.Term.Prj{h_487}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q1{}, x_491, rest_492})], ks}}, Fun.F.iter(9n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k4(), [FM.Enc.form(Machine.Form.tup{Source.Q2{}, a_495, b_496}), FM.Enc.val(rest_492), FM.Enc.val(x_491), FM.Enc.p(FM.Enc.val(x_491), FM.Enc.val(rest_492)), FM.Enc.quan(Source.Q1{}), Fun.V.z{}, FM.Enc.term(h_487), FM.Enc.term(Source.Term.Prj{h_487}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q1{}, x_491, rest_492})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Machine.Walk.prj.of(Machine.Form.tup{Source.Q2{}, a_495, b_496}, Source.Q1{}, rest_492, ys => Machine.Walk.go(h_487, e_409, ys))), ks}},
            FP.Reach.steps(9n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k4(), [FM.Enc.form(Machine.Form.tup{Source.Q2{}, a_495, b_496}), FM.Enc.val(rest_492), FM.Enc.val(x_491), FM.Enc.p(FM.Enc.val(x_491), FM.Enc.val(rest_492)), FM.Enc.quan(Source.Q1{}), Fun.V.z{}, FM.Enc.term(h_487), FM.Enc.term(Source.Term.Prj{h_487}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q1{}, x_491, rest_492})], ks}}),
            L.Walk.go(h_487, e_409, Machine.Val.arg{Source.Q2{}, a_495, Machine.Val.arg{Source.Q1{}, b_496, rest_492}}, ks))),
            Elim.Quan(r_494, m18 => Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k4(), [FM.Enc.form(Machine.Form.tup{m18, a_495, b_496}), FM.Enc.val(rest_492), FM.Enc.val(x_491), FM.Enc.p(FM.Enc.val(x_491), FM.Enc.val(rest_492)), FM.Enc.quan(Source.Q2{}), Fun.V.z{}, FM.Enc.term(h_487), FM.Enc.term(Source.Term.Prj{h_487}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q2{}, x_491, rest_492})], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Machine.Walk.prj.of(Machine.Form.tup{m18, a_495, b_496}, Source.Q2{}, rest_492, ys => Machine.Walk.go(h_487, e_409, ys))), ks}}),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k4(), [FM.Enc.form(Machine.Form.tup{Source.Q0{}, a_495, b_496}), FM.Enc.val(rest_492), FM.Enc.val(x_491), FM.Enc.p(FM.Enc.val(x_491), FM.Enc.val(rest_492)), FM.Enc.quan(Source.Q2{}), Fun.V.z{}, FM.Enc.term(h_487), FM.Enc.term(Source.Term.Prj{h_487}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q2{}, x_491, rest_492})], ks}}, Fun.F.iter(9n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k4(), [FM.Enc.form(Machine.Form.tup{Source.Q0{}, a_495, b_496}), FM.Enc.val(rest_492), FM.Enc.val(x_491), FM.Enc.p(FM.Enc.val(x_491), FM.Enc.val(rest_492)), FM.Enc.quan(Source.Q2{}), Fun.V.z{}, FM.Enc.term(h_487), FM.Enc.term(Source.Term.Prj{h_487}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q2{}, x_491, rest_492})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Machine.Walk.prj.of(Machine.Form.tup{Source.Q0{}, a_495, b_496}, Source.Q2{}, rest_492, ys => Machine.Walk.go(h_487, e_409, ys))), ks}},
            FP.Reach.steps(9n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k4(), [FM.Enc.form(Machine.Form.tup{Source.Q0{}, a_495, b_496}), FM.Enc.val(rest_492), FM.Enc.val(x_491), FM.Enc.p(FM.Enc.val(x_491), FM.Enc.val(rest_492)), FM.Enc.quan(Source.Q2{}), Fun.V.z{}, FM.Enc.term(h_487), FM.Enc.term(Source.Term.Prj{h_487}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q2{}, x_491, rest_492})], ks}}),
            L.Walk.go(h_487, e_409, Machine.Val.arg{Source.Q0{}, a_495, Machine.Val.arg{Source.Q2{}, b_496, rest_492}}, ks)),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k4(), [FM.Enc.form(Machine.Form.tup{Source.Q1{}, a_495, b_496}), FM.Enc.val(rest_492), FM.Enc.val(x_491), FM.Enc.p(FM.Enc.val(x_491), FM.Enc.val(rest_492)), FM.Enc.quan(Source.Q2{}), Fun.V.z{}, FM.Enc.term(h_487), FM.Enc.term(Source.Term.Prj{h_487}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q2{}, x_491, rest_492})], ks}}, Fun.F.iter(9n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k4(), [FM.Enc.form(Machine.Form.tup{Source.Q1{}, a_495, b_496}), FM.Enc.val(rest_492), FM.Enc.val(x_491), FM.Enc.p(FM.Enc.val(x_491), FM.Enc.val(rest_492)), FM.Enc.quan(Source.Q2{}), Fun.V.z{}, FM.Enc.term(h_487), FM.Enc.term(Source.Term.Prj{h_487}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q2{}, x_491, rest_492})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Machine.Walk.prj.of(Machine.Form.tup{Source.Q1{}, a_495, b_496}, Source.Q2{}, rest_492, ys => Machine.Walk.go(h_487, e_409, ys))), ks}},
            FP.Reach.steps(9n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k4(), [FM.Enc.form(Machine.Form.tup{Source.Q1{}, a_495, b_496}), FM.Enc.val(rest_492), FM.Enc.val(x_491), FM.Enc.p(FM.Enc.val(x_491), FM.Enc.val(rest_492)), FM.Enc.quan(Source.Q2{}), Fun.V.z{}, FM.Enc.term(h_487), FM.Enc.term(Source.Term.Prj{h_487}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q2{}, x_491, rest_492})], ks}}),
            L.Walk.go(h_487, e_409, Machine.Val.arg{Source.Q2{}, a_495, Machine.Val.arg{Source.Q2{}, b_496, rest_492}}, ks)),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k4(), [FM.Enc.form(Machine.Form.tup{Source.Q2{}, a_495, b_496}), FM.Enc.val(rest_492), FM.Enc.val(x_491), FM.Enc.p(FM.Enc.val(x_491), FM.Enc.val(rest_492)), FM.Enc.quan(Source.Q2{}), Fun.V.z{}, FM.Enc.term(h_487), FM.Enc.term(Source.Term.Prj{h_487}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q2{}, x_491, rest_492})], ks}}, Fun.F.iter(9n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k4(), [FM.Enc.form(Machine.Form.tup{Source.Q2{}, a_495, b_496}), FM.Enc.val(rest_492), FM.Enc.val(x_491), FM.Enc.p(FM.Enc.val(x_491), FM.Enc.val(rest_492)), FM.Enc.quan(Source.Q2{}), Fun.V.z{}, FM.Enc.term(h_487), FM.Enc.term(Source.Term.Prj{h_487}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q2{}, x_491, rest_492})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Machine.Walk.prj.of(Machine.Form.tup{Source.Q2{}, a_495, b_496}, Source.Q2{}, rest_492, ys => Machine.Walk.go(h_487, e_409, ys))), ks}},
            FP.Reach.steps(9n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k4(), [FM.Enc.form(Machine.Form.tup{Source.Q2{}, a_495, b_496}), FM.Enc.val(rest_492), FM.Enc.val(x_491), FM.Enc.p(FM.Enc.val(x_491), FM.Enc.val(rest_492)), FM.Enc.quan(Source.Q2{}), Fun.V.z{}, FM.Enc.term(h_487), FM.Enc.term(Source.Term.Prj{h_487}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q2{}, x_491, rest_492})], ks}}),
            L.Walk.go(h_487, e_409, Machine.Val.arg{Source.Q2{}, a_495, Machine.Val.arg{Source.Q2{}, b_496, rest_492}}, ks)))),
            +_k_497 => (2n, {==}),
            (2n, {==})))))
        case Machine.Val.clo{+_t_498, +_e_499}:
          (4n, {==})
        case Machine.Val.lab{+_k_500}:
          (4n, {==})
        case Machine.Val.rfl{}:
          (4n, {==})
        case Machine.Val.tup{+_q_501, +_a_502, +_b_503}:
          (4n, {==})
        case Machine.Val.call{+_k_504, +_xs_505}:
          (4n, {==})
    case Source.Term.Enu{+_ks_506}:
      (8n, {==})
    case Source.Term.Lab{+_k_507}:
      (8n, {==})
    case Source.Term.Mat{+k_508, +h_509, +m_510}:
      match xs_410:
        case Machine.Val.nil{}:
          (6n, {==})
        case Machine.Val.env{+_x_511, +_rest_512}:
          (6n, {==})
        case Machine.Val.arg{+q_513, +x_514, +rest_515}:
          FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go(), [FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{q_513, x_514, rest_515})], ks}}, Fun.F.iter(7n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go(), [FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{q_513, x_514, rest_515})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Machine.Walk.go(Source.Term.Mat{k_508, h_509, m_510}, e_409, Machine.Val.arg{q_513, x_514, rest_515})), ks}},
            FP.Reach.steps(7n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go(), [FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{q_513, x_514, rest_515})], ks}}),
            FP.Reach.trans(Code.prog(), Fun.F.iter(7n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go(), [FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{q_513, x_514, rest_515})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.form(Machine.Val.form(x_514)), Con{Fun.Fr{Code.F.Walk.go.k5(), [FM.Enc.val(rest_515), FM.Enc.val(x_514), FM.Enc.p(FM.Enc.val(x_514), FM.Enc.val(rest_515)), FM.Enc.quan(q_513), FM.Enc.term(m_510), FM.Enc.term(h_509), FM.Enc.p(FM.Enc.term(h_509), FM.Enc.term(m_510)), FM.Enc.name(k_508), FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{q_513, x_514, rest_515})]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Machine.Walk.go(Source.Term.Mat{k_508, h_509, m_510}, e_409, Machine.Val.arg{q_513, x_514, rest_515})), ks}},
            L.Val.form(x_514, Con{Fun.Fr{Code.F.Walk.go.k5(), [FM.Enc.val(rest_515), FM.Enc.val(x_514), FM.Enc.p(FM.Enc.val(x_514), FM.Enc.val(rest_515)), FM.Enc.quan(q_513), FM.Enc.term(m_510), FM.Enc.term(h_509), FM.Enc.p(FM.Enc.term(h_509), FM.Enc.term(m_510)), FM.Enc.name(k_508), FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{q_513, x_514, rest_515})]}, ks}),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.form(Machine.Val.form(x_514)), Con{Fun.Fr{Code.F.Walk.go.k5(), [FM.Enc.val(rest_515), FM.Enc.val(x_514), FM.Enc.p(FM.Enc.val(x_514), FM.Enc.val(rest_515)), FM.Enc.quan(q_513), FM.Enc.term(m_510), FM.Enc.term(h_509), FM.Enc.p(FM.Enc.term(h_509), FM.Enc.term(m_510)), FM.Enc.name(k_508), FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{q_513, x_514, rest_515})]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.form(Machine.Val.form(x_514)), Con{Fun.Fr{Code.F.Walk.go.k5(), [FM.Enc.val(rest_515), FM.Enc.val(x_514), FM.Enc.p(FM.Enc.val(x_514), FM.Enc.val(rest_515)), FM.Enc.quan(q_513), FM.Enc.term(m_510), FM.Enc.term(h_509), FM.Enc.p(FM.Enc.term(h_509), FM.Enc.term(m_510)), FM.Enc.name(k_508), FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{q_513, x_514, rest_515})]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Machine.Walk.go(Source.Term.Mat{k_508, h_509, m_510}, e_409, Machine.Val.arg{q_513, x_514, rest_515})), ks}},
            FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.form(Machine.Val.form(x_514)), Con{Fun.Fr{Code.F.Walk.go.k5(), [FM.Enc.val(rest_515), FM.Enc.val(x_514), FM.Enc.p(FM.Enc.val(x_514), FM.Enc.val(rest_515)), FM.Enc.quan(q_513), FM.Enc.term(m_510), FM.Enc.term(h_509), FM.Enc.p(FM.Enc.term(h_509), FM.Enc.term(m_510)), FM.Enc.name(k_508), FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{q_513, x_514, rest_515})]}, ks}}}),
            Elim.Form(Machine.Val.form(x_514), m19 => Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k5(), [FM.Enc.form(m19), FM.Enc.val(rest_515), FM.Enc.val(x_514), FM.Enc.p(FM.Enc.val(x_514), FM.Enc.val(rest_515)), FM.Enc.quan(q_513), FM.Enc.term(m_510), FM.Enc.term(h_509), FM.Enc.p(FM.Enc.term(h_509), FM.Enc.term(m_510)), FM.Enc.name(k_508), FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{q_513, x_514, rest_515})], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Machine.Walk.mat.of(m19, q_513, k_508, rest_515, ys => Machine.Walk.go(h_509, e_409, ys), ys => Machine.Walk.go(m_510, e_409, ys))), ks}}),
            +_r_517 => +_a_518 => +_b_519 => (2n, {==}),
            +j_520 => Elim.Quan(q_513, m20 => Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k5(), [FM.Enc.form(Machine.Form.lab{j_520}), FM.Enc.val(rest_515), FM.Enc.val(x_514), FM.Enc.p(FM.Enc.val(x_514), FM.Enc.val(rest_515)), FM.Enc.quan(m20), FM.Enc.term(m_510), FM.Enc.term(h_509), FM.Enc.p(FM.Enc.term(h_509), FM.Enc.term(m_510)), FM.Enc.name(k_508), FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{m20, x_514, rest_515})], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Machine.Walk.mat.of(Machine.Form.lab{j_520}, m20, k_508, rest_515, ys => Machine.Walk.go(h_509, e_409, ys), ys => Machine.Walk.go(m_510, e_409, ys))), ks}}),
            (3n, {==}),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k5(), [FM.Enc.form(Machine.Form.lab{j_520}), FM.Enc.val(rest_515), FM.Enc.val(x_514), FM.Enc.p(FM.Enc.val(x_514), FM.Enc.val(rest_515)), FM.Enc.quan(Source.Q1{}), FM.Enc.term(m_510), FM.Enc.term(h_509), FM.Enc.p(FM.Enc.term(h_509), FM.Enc.term(m_510)), FM.Enc.name(k_508), FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q1{}, x_514, rest_515})], ks}}, Fun.F.iter(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k5(), [FM.Enc.form(Machine.Form.lab{j_520}), FM.Enc.val(rest_515), FM.Enc.val(x_514), FM.Enc.p(FM.Enc.val(x_514), FM.Enc.val(rest_515)), FM.Enc.quan(Source.Q1{}), FM.Enc.term(m_510), FM.Enc.term(h_509), FM.Enc.p(FM.Enc.term(h_509), FM.Enc.term(m_510)), FM.Enc.name(k_508), FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q1{}, x_514, rest_515})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Machine.Walk.mat.of(Machine.Form.lab{j_520}, Source.Q1{}, k_508, rest_515, ys => Machine.Walk.go(h_509, e_409, ys), ys => Machine.Walk.go(m_510, e_409, ys))), ks}},
            FP.Reach.steps(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k5(), [FM.Enc.form(Machine.Form.lab{j_520}), FM.Enc.val(rest_515), FM.Enc.val(x_514), FM.Enc.p(FM.Enc.val(x_514), FM.Enc.val(rest_515)), FM.Enc.quan(Source.Q1{}), FM.Enc.term(m_510), FM.Enc.term(h_509), FM.Enc.p(FM.Enc.term(h_509), FM.Enc.term(m_510)), FM.Enc.name(k_508), FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q1{}, x_514, rest_515})], ks}}),
            FP.Reach.trans(Code.prog(), Fun.F.iter(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k5(), [FM.Enc.form(Machine.Form.lab{j_520}), FM.Enc.val(rest_515), FM.Enc.val(x_514), FM.Enc.p(FM.Enc.val(x_514), FM.Enc.val(rest_515)), FM.Enc.quan(Source.Q1{}), FM.Enc.term(m_510), FM.Enc.term(h_509), FM.Enc.p(FM.Enc.term(h_509), FM.Enc.term(m_510)), FM.Enc.name(k_508), FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q1{}, x_514, rest_515})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(j_520, k_508)), Con{Fun.Fr{Code.F.Walk.go.k6(), [Fun.V.z{}, FM.Enc.name(j_520), FM.Enc.form(Machine.Form.lab{j_520}), FM.Enc.val(rest_515), FM.Enc.val(x_514), FM.Enc.p(FM.Enc.val(x_514), FM.Enc.val(rest_515)), FM.Enc.quan(Source.Q1{}), FM.Enc.term(m_510), FM.Enc.term(h_509), FM.Enc.p(FM.Enc.term(h_509), FM.Enc.term(m_510)), FM.Enc.name(k_508), FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q1{}, x_514, rest_515})]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Machine.Walk.mat.of(Machine.Form.lab{j_520}, Source.Q1{}, k_508, rest_515, ys => Machine.Walk.go(h_509, e_409, ys), ys => Machine.Walk.go(m_510, e_409, ys))), ks}},
            L.Name.is_eq(j_520, k_508, Con{Fun.Fr{Code.F.Walk.go.k6(), [Fun.V.z{}, FM.Enc.name(j_520), FM.Enc.form(Machine.Form.lab{j_520}), FM.Enc.val(rest_515), FM.Enc.val(x_514), FM.Enc.p(FM.Enc.val(x_514), FM.Enc.val(rest_515)), FM.Enc.quan(Source.Q1{}), FM.Enc.term(m_510), FM.Enc.term(h_509), FM.Enc.p(FM.Enc.term(h_509), FM.Enc.term(m_510)), FM.Enc.name(k_508), FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q1{}, x_514, rest_515})]}, ks}),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(j_520, k_508)), Con{Fun.Fr{Code.F.Walk.go.k6(), [Fun.V.z{}, FM.Enc.name(j_520), FM.Enc.form(Machine.Form.lab{j_520}), FM.Enc.val(rest_515), FM.Enc.val(x_514), FM.Enc.p(FM.Enc.val(x_514), FM.Enc.val(rest_515)), FM.Enc.quan(Source.Q1{}), FM.Enc.term(m_510), FM.Enc.term(h_509), FM.Enc.p(FM.Enc.term(h_509), FM.Enc.term(m_510)), FM.Enc.name(k_508), FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q1{}, x_514, rest_515})]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(j_520, k_508)), Con{Fun.Fr{Code.F.Walk.go.k6(), [Fun.V.z{}, FM.Enc.name(j_520), FM.Enc.form(Machine.Form.lab{j_520}), FM.Enc.val(rest_515), FM.Enc.val(x_514), FM.Enc.p(FM.Enc.val(x_514), FM.Enc.val(rest_515)), FM.Enc.quan(Source.Q1{}), FM.Enc.term(m_510), FM.Enc.term(h_509), FM.Enc.p(FM.Enc.term(h_509), FM.Enc.term(m_510)), FM.Enc.name(k_508), FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q1{}, x_514, rest_515})]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Machine.Walk.mat.of(Machine.Form.lab{j_520}, Source.Q1{}, k_508, rest_515, ys => Machine.Walk.go(h_509, e_409, ys), ys => Machine.Walk.go(m_510, e_409, ys))), ks}},
            FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(j_520, k_508)), Con{Fun.Fr{Code.F.Walk.go.k6(), [Fun.V.z{}, FM.Enc.name(j_520), FM.Enc.form(Machine.Form.lab{j_520}), FM.Enc.val(rest_515), FM.Enc.val(x_514), FM.Enc.p(FM.Enc.val(x_514), FM.Enc.val(rest_515)), FM.Enc.quan(Source.Q1{}), FM.Enc.term(m_510), FM.Enc.term(h_509), FM.Enc.p(FM.Enc.term(h_509), FM.Enc.term(m_510)), FM.Enc.name(k_508), FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q1{}, x_514, rest_515})]}, ks}}}),
            Elim.Bool(Source.Name.is_eq(j_520, k_508), m21 => Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k6(), [FM.Enc.bool(m21), Fun.V.z{}, FM.Enc.name(j_520), FM.Enc.form(Machine.Form.lab{j_520}), FM.Enc.val(rest_515), FM.Enc.val(x_514), FM.Enc.p(FM.Enc.val(x_514), FM.Enc.val(rest_515)), FM.Enc.quan(Source.Q1{}), FM.Enc.term(m_510), FM.Enc.term(h_509), FM.Enc.p(FM.Enc.term(h_509), FM.Enc.term(m_510)), FM.Enc.name(k_508), FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q1{}, x_514, rest_515})], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Source.Bool.lazy(Machine.Leaf, m21, w => Machine.Walk.go(h_509, e_409, rest_515), w => Machine.Walk.go(m_510, e_409, Machine.Val.arg{Source.Q1{}, Machine.Val.lab{j_520}, rest_515}))), ks}}),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k6(), [FM.Enc.bool(False{}), Fun.V.z{}, FM.Enc.name(j_520), FM.Enc.form(Machine.Form.lab{j_520}), FM.Enc.val(rest_515), FM.Enc.val(x_514), FM.Enc.p(FM.Enc.val(x_514), FM.Enc.val(rest_515)), FM.Enc.quan(Source.Q1{}), FM.Enc.term(m_510), FM.Enc.term(h_509), FM.Enc.p(FM.Enc.term(h_509), FM.Enc.term(m_510)), FM.Enc.name(k_508), FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q1{}, x_514, rest_515})], ks}}, Fun.F.iter(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k6(), [FM.Enc.bool(False{}), Fun.V.z{}, FM.Enc.name(j_520), FM.Enc.form(Machine.Form.lab{j_520}), FM.Enc.val(rest_515), FM.Enc.val(x_514), FM.Enc.p(FM.Enc.val(x_514), FM.Enc.val(rest_515)), FM.Enc.quan(Source.Q1{}), FM.Enc.term(m_510), FM.Enc.term(h_509), FM.Enc.p(FM.Enc.term(h_509), FM.Enc.term(m_510)), FM.Enc.name(k_508), FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q1{}, x_514, rest_515})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Source.Bool.lazy(Machine.Leaf, False{}, w => Machine.Walk.go(h_509, e_409, rest_515), w => Machine.Walk.go(m_510, e_409, Machine.Val.arg{Source.Q1{}, Machine.Val.lab{j_520}, rest_515}))), ks}},
            FP.Reach.steps(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k6(), [FM.Enc.bool(False{}), Fun.V.z{}, FM.Enc.name(j_520), FM.Enc.form(Machine.Form.lab{j_520}), FM.Enc.val(rest_515), FM.Enc.val(x_514), FM.Enc.p(FM.Enc.val(x_514), FM.Enc.val(rest_515)), FM.Enc.quan(Source.Q1{}), FM.Enc.term(m_510), FM.Enc.term(h_509), FM.Enc.p(FM.Enc.term(h_509), FM.Enc.term(m_510)), FM.Enc.name(k_508), FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q1{}, x_514, rest_515})], ks}}),
            L.Walk.go(m_510, e_409, Machine.Val.arg{Source.Q1{}, Machine.Val.lab{j_520}, rest_515}, ks)),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k6(), [FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(j_520), FM.Enc.form(Machine.Form.lab{j_520}), FM.Enc.val(rest_515), FM.Enc.val(x_514), FM.Enc.p(FM.Enc.val(x_514), FM.Enc.val(rest_515)), FM.Enc.quan(Source.Q1{}), FM.Enc.term(m_510), FM.Enc.term(h_509), FM.Enc.p(FM.Enc.term(h_509), FM.Enc.term(m_510)), FM.Enc.name(k_508), FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q1{}, x_514, rest_515})], ks}}, Fun.F.iter(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k6(), [FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(j_520), FM.Enc.form(Machine.Form.lab{j_520}), FM.Enc.val(rest_515), FM.Enc.val(x_514), FM.Enc.p(FM.Enc.val(x_514), FM.Enc.val(rest_515)), FM.Enc.quan(Source.Q1{}), FM.Enc.term(m_510), FM.Enc.term(h_509), FM.Enc.p(FM.Enc.term(h_509), FM.Enc.term(m_510)), FM.Enc.name(k_508), FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q1{}, x_514, rest_515})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Source.Bool.lazy(Machine.Leaf, True{}, w => Machine.Walk.go(h_509, e_409, rest_515), w => Machine.Walk.go(m_510, e_409, Machine.Val.arg{Source.Q1{}, Machine.Val.lab{j_520}, rest_515}))), ks}},
            FP.Reach.steps(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k6(), [FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(j_520), FM.Enc.form(Machine.Form.lab{j_520}), FM.Enc.val(rest_515), FM.Enc.val(x_514), FM.Enc.p(FM.Enc.val(x_514), FM.Enc.val(rest_515)), FM.Enc.quan(Source.Q1{}), FM.Enc.term(m_510), FM.Enc.term(h_509), FM.Enc.p(FM.Enc.term(h_509), FM.Enc.term(m_510)), FM.Enc.name(k_508), FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q1{}, x_514, rest_515})], ks}}),
            L.Walk.go(h_509, e_409, rest_515, ks)))))),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k5(), [FM.Enc.form(Machine.Form.lab{j_520}), FM.Enc.val(rest_515), FM.Enc.val(x_514), FM.Enc.p(FM.Enc.val(x_514), FM.Enc.val(rest_515)), FM.Enc.quan(Source.Q2{}), FM.Enc.term(m_510), FM.Enc.term(h_509), FM.Enc.p(FM.Enc.term(h_509), FM.Enc.term(m_510)), FM.Enc.name(k_508), FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q2{}, x_514, rest_515})], ks}}, Fun.F.iter(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k5(), [FM.Enc.form(Machine.Form.lab{j_520}), FM.Enc.val(rest_515), FM.Enc.val(x_514), FM.Enc.p(FM.Enc.val(x_514), FM.Enc.val(rest_515)), FM.Enc.quan(Source.Q2{}), FM.Enc.term(m_510), FM.Enc.term(h_509), FM.Enc.p(FM.Enc.term(h_509), FM.Enc.term(m_510)), FM.Enc.name(k_508), FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q2{}, x_514, rest_515})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Machine.Walk.mat.of(Machine.Form.lab{j_520}, Source.Q2{}, k_508, rest_515, ys => Machine.Walk.go(h_509, e_409, ys), ys => Machine.Walk.go(m_510, e_409, ys))), ks}},
            FP.Reach.steps(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k5(), [FM.Enc.form(Machine.Form.lab{j_520}), FM.Enc.val(rest_515), FM.Enc.val(x_514), FM.Enc.p(FM.Enc.val(x_514), FM.Enc.val(rest_515)), FM.Enc.quan(Source.Q2{}), FM.Enc.term(m_510), FM.Enc.term(h_509), FM.Enc.p(FM.Enc.term(h_509), FM.Enc.term(m_510)), FM.Enc.name(k_508), FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q2{}, x_514, rest_515})], ks}}),
            FP.Reach.trans(Code.prog(), Fun.F.iter(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k5(), [FM.Enc.form(Machine.Form.lab{j_520}), FM.Enc.val(rest_515), FM.Enc.val(x_514), FM.Enc.p(FM.Enc.val(x_514), FM.Enc.val(rest_515)), FM.Enc.quan(Source.Q2{}), FM.Enc.term(m_510), FM.Enc.term(h_509), FM.Enc.p(FM.Enc.term(h_509), FM.Enc.term(m_510)), FM.Enc.name(k_508), FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q2{}, x_514, rest_515})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(j_520, k_508)), Con{Fun.Fr{Code.F.Walk.go.k6(), [Fun.V.z{}, FM.Enc.name(j_520), FM.Enc.form(Machine.Form.lab{j_520}), FM.Enc.val(rest_515), FM.Enc.val(x_514), FM.Enc.p(FM.Enc.val(x_514), FM.Enc.val(rest_515)), FM.Enc.quan(Source.Q2{}), FM.Enc.term(m_510), FM.Enc.term(h_509), FM.Enc.p(FM.Enc.term(h_509), FM.Enc.term(m_510)), FM.Enc.name(k_508), FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q2{}, x_514, rest_515})]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Machine.Walk.mat.of(Machine.Form.lab{j_520}, Source.Q2{}, k_508, rest_515, ys => Machine.Walk.go(h_509, e_409, ys), ys => Machine.Walk.go(m_510, e_409, ys))), ks}},
            L.Name.is_eq(j_520, k_508, Con{Fun.Fr{Code.F.Walk.go.k6(), [Fun.V.z{}, FM.Enc.name(j_520), FM.Enc.form(Machine.Form.lab{j_520}), FM.Enc.val(rest_515), FM.Enc.val(x_514), FM.Enc.p(FM.Enc.val(x_514), FM.Enc.val(rest_515)), FM.Enc.quan(Source.Q2{}), FM.Enc.term(m_510), FM.Enc.term(h_509), FM.Enc.p(FM.Enc.term(h_509), FM.Enc.term(m_510)), FM.Enc.name(k_508), FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q2{}, x_514, rest_515})]}, ks}),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(j_520, k_508)), Con{Fun.Fr{Code.F.Walk.go.k6(), [Fun.V.z{}, FM.Enc.name(j_520), FM.Enc.form(Machine.Form.lab{j_520}), FM.Enc.val(rest_515), FM.Enc.val(x_514), FM.Enc.p(FM.Enc.val(x_514), FM.Enc.val(rest_515)), FM.Enc.quan(Source.Q2{}), FM.Enc.term(m_510), FM.Enc.term(h_509), FM.Enc.p(FM.Enc.term(h_509), FM.Enc.term(m_510)), FM.Enc.name(k_508), FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q2{}, x_514, rest_515})]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(j_520, k_508)), Con{Fun.Fr{Code.F.Walk.go.k6(), [Fun.V.z{}, FM.Enc.name(j_520), FM.Enc.form(Machine.Form.lab{j_520}), FM.Enc.val(rest_515), FM.Enc.val(x_514), FM.Enc.p(FM.Enc.val(x_514), FM.Enc.val(rest_515)), FM.Enc.quan(Source.Q2{}), FM.Enc.term(m_510), FM.Enc.term(h_509), FM.Enc.p(FM.Enc.term(h_509), FM.Enc.term(m_510)), FM.Enc.name(k_508), FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q2{}, x_514, rest_515})]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Machine.Walk.mat.of(Machine.Form.lab{j_520}, Source.Q2{}, k_508, rest_515, ys => Machine.Walk.go(h_509, e_409, ys), ys => Machine.Walk.go(m_510, e_409, ys))), ks}},
            FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(j_520, k_508)), Con{Fun.Fr{Code.F.Walk.go.k6(), [Fun.V.z{}, FM.Enc.name(j_520), FM.Enc.form(Machine.Form.lab{j_520}), FM.Enc.val(rest_515), FM.Enc.val(x_514), FM.Enc.p(FM.Enc.val(x_514), FM.Enc.val(rest_515)), FM.Enc.quan(Source.Q2{}), FM.Enc.term(m_510), FM.Enc.term(h_509), FM.Enc.p(FM.Enc.term(h_509), FM.Enc.term(m_510)), FM.Enc.name(k_508), FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q2{}, x_514, rest_515})]}, ks}}}),
            Elim.Bool(Source.Name.is_eq(j_520, k_508), m22 => Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k6(), [FM.Enc.bool(m22), Fun.V.z{}, FM.Enc.name(j_520), FM.Enc.form(Machine.Form.lab{j_520}), FM.Enc.val(rest_515), FM.Enc.val(x_514), FM.Enc.p(FM.Enc.val(x_514), FM.Enc.val(rest_515)), FM.Enc.quan(Source.Q2{}), FM.Enc.term(m_510), FM.Enc.term(h_509), FM.Enc.p(FM.Enc.term(h_509), FM.Enc.term(m_510)), FM.Enc.name(k_508), FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q2{}, x_514, rest_515})], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Source.Bool.lazy(Machine.Leaf, m22, w => Machine.Walk.go(h_509, e_409, rest_515), w => Machine.Walk.go(m_510, e_409, Machine.Val.arg{Source.Q2{}, Machine.Val.lab{j_520}, rest_515}))), ks}}),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k6(), [FM.Enc.bool(False{}), Fun.V.z{}, FM.Enc.name(j_520), FM.Enc.form(Machine.Form.lab{j_520}), FM.Enc.val(rest_515), FM.Enc.val(x_514), FM.Enc.p(FM.Enc.val(x_514), FM.Enc.val(rest_515)), FM.Enc.quan(Source.Q2{}), FM.Enc.term(m_510), FM.Enc.term(h_509), FM.Enc.p(FM.Enc.term(h_509), FM.Enc.term(m_510)), FM.Enc.name(k_508), FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q2{}, x_514, rest_515})], ks}}, Fun.F.iter(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k6(), [FM.Enc.bool(False{}), Fun.V.z{}, FM.Enc.name(j_520), FM.Enc.form(Machine.Form.lab{j_520}), FM.Enc.val(rest_515), FM.Enc.val(x_514), FM.Enc.p(FM.Enc.val(x_514), FM.Enc.val(rest_515)), FM.Enc.quan(Source.Q2{}), FM.Enc.term(m_510), FM.Enc.term(h_509), FM.Enc.p(FM.Enc.term(h_509), FM.Enc.term(m_510)), FM.Enc.name(k_508), FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q2{}, x_514, rest_515})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Source.Bool.lazy(Machine.Leaf, False{}, w => Machine.Walk.go(h_509, e_409, rest_515), w => Machine.Walk.go(m_510, e_409, Machine.Val.arg{Source.Q2{}, Machine.Val.lab{j_520}, rest_515}))), ks}},
            FP.Reach.steps(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k6(), [FM.Enc.bool(False{}), Fun.V.z{}, FM.Enc.name(j_520), FM.Enc.form(Machine.Form.lab{j_520}), FM.Enc.val(rest_515), FM.Enc.val(x_514), FM.Enc.p(FM.Enc.val(x_514), FM.Enc.val(rest_515)), FM.Enc.quan(Source.Q2{}), FM.Enc.term(m_510), FM.Enc.term(h_509), FM.Enc.p(FM.Enc.term(h_509), FM.Enc.term(m_510)), FM.Enc.name(k_508), FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q2{}, x_514, rest_515})], ks}}),
            L.Walk.go(m_510, e_409, Machine.Val.arg{Source.Q2{}, Machine.Val.lab{j_520}, rest_515}, ks)),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k6(), [FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(j_520), FM.Enc.form(Machine.Form.lab{j_520}), FM.Enc.val(rest_515), FM.Enc.val(x_514), FM.Enc.p(FM.Enc.val(x_514), FM.Enc.val(rest_515)), FM.Enc.quan(Source.Q2{}), FM.Enc.term(m_510), FM.Enc.term(h_509), FM.Enc.p(FM.Enc.term(h_509), FM.Enc.term(m_510)), FM.Enc.name(k_508), FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q2{}, x_514, rest_515})], ks}}, Fun.F.iter(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k6(), [FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(j_520), FM.Enc.form(Machine.Form.lab{j_520}), FM.Enc.val(rest_515), FM.Enc.val(x_514), FM.Enc.p(FM.Enc.val(x_514), FM.Enc.val(rest_515)), FM.Enc.quan(Source.Q2{}), FM.Enc.term(m_510), FM.Enc.term(h_509), FM.Enc.p(FM.Enc.term(h_509), FM.Enc.term(m_510)), FM.Enc.name(k_508), FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q2{}, x_514, rest_515})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Source.Bool.lazy(Machine.Leaf, True{}, w => Machine.Walk.go(h_509, e_409, rest_515), w => Machine.Walk.go(m_510, e_409, Machine.Val.arg{Source.Q2{}, Machine.Val.lab{j_520}, rest_515}))), ks}},
            FP.Reach.steps(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k6(), [FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(j_520), FM.Enc.form(Machine.Form.lab{j_520}), FM.Enc.val(rest_515), FM.Enc.val(x_514), FM.Enc.p(FM.Enc.val(x_514), FM.Enc.val(rest_515)), FM.Enc.quan(Source.Q2{}), FM.Enc.term(m_510), FM.Enc.term(h_509), FM.Enc.p(FM.Enc.term(h_509), FM.Enc.term(m_510)), FM.Enc.name(k_508), FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q2{}, x_514, rest_515})], ks}}),
            L.Walk.go(h_509, e_409, rest_515, ks))))))),
            (2n, {==})))))
        case Machine.Val.clo{+_t_523, +_e_524}:
          (6n, {==})
        case Machine.Val.lab{+_k_525}:
          (6n, {==})
        case Machine.Val.rfl{}:
          (6n, {==})
        case Machine.Val.tup{+_q_526, +_a_527, +_b_528}:
          (6n, {==})
        case Machine.Val.call{+_k_529, +_xs_530}:
          (6n, {==})
    case Source.Term.Efq{}:
      match xs_410:
        case Machine.Val.nil{}:
          (6n, {==})
        case Machine.Val.env{+_x_531, +_rest_532}:
          (6n, {==})
        case Machine.Val.arg{+q_533, +x_534, +rest_535}:
          (7n, {==})
        case Machine.Val.clo{+_t_536, +_e_537}:
          (6n, {==})
        case Machine.Val.lab{+_k_538}:
          (6n, {==})
        case Machine.Val.rfl{}:
          (6n, {==})
        case Machine.Val.tup{+_q_539, +_a_540, +_b_541}:
          (6n, {==})
        case Machine.Val.call{+_k_542, +_xs_543}:
          (6n, {==})
    case Source.Term.Eql{+_a_544, +_b_545, +_t_546}:
      (8n, {==})
    case Source.Term.Rfl{}:
      (8n, {==})
    case Source.Term.Rwt{+_e_547, +_p_548, +_f_549}:
      (8n, {==})

def L.Args.snoc(+xs_550: Machine.Val, +q_551: Source.Quan, +x_552: Machine.Val, +ks: List<&2, Fun.Fr>) ->
  Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Args.snoc(), [FM.Enc.val(xs_550), FM.Enc.quan(q_551), FM.Enc.val(x_552)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.val(Machine.Args.snoc(xs_550, q_551, x_552)), ks}}):
  match xs_550:
    case Machine.Val.nil{}:
      (4n, {==})
    case Machine.Val.env{+_x_553, +_rest_554}:
      (4n, {==})
    case Machine.Val.arg{+p_555, +y_556, +rest_557}:
      FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Args.snoc(), [FM.Enc.val(Machine.Val.arg{p_555, y_556, rest_557}), FM.Enc.quan(q_551), FM.Enc.val(x_552)], ks}}, Fun.F.iter(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Args.snoc(), [FM.Enc.val(Machine.Val.arg{p_555, y_556, rest_557}), FM.Enc.quan(q_551), FM.Enc.val(x_552)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.val(Machine.Args.snoc(Machine.Val.arg{p_555, y_556, rest_557}, q_551, x_552)), ks}},
        FP.Reach.steps(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Args.snoc(), [FM.Enc.val(Machine.Val.arg{p_555, y_556, rest_557}), FM.Enc.quan(q_551), FM.Enc.val(x_552)], ks}}),
        FP.Reach.trans(Code.prog(), Fun.F.iter(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Args.snoc(), [FM.Enc.val(Machine.Val.arg{p_555, y_556, rest_557}), FM.Enc.quan(q_551), FM.Enc.val(x_552)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.val(Machine.Args.snoc(rest_557, q_551, x_552)), Con{Fun.Fr{Code.F.Args.snoc.k1(), [FM.Enc.val(rest_557), FM.Enc.val(y_556), FM.Enc.p(FM.Enc.val(y_556), FM.Enc.val(rest_557)), FM.Enc.quan(p_555), FM.Enc.val(Machine.Val.arg{p_555, y_556, rest_557}), FM.Enc.quan(q_551), FM.Enc.val(x_552)]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.val(Machine.Args.snoc(Machine.Val.arg{p_555, y_556, rest_557}, q_551, x_552)), ks}},
        L.Args.snoc(rest_557, q_551, x_552, Con{Fun.Fr{Code.F.Args.snoc.k1(), [FM.Enc.val(rest_557), FM.Enc.val(y_556), FM.Enc.p(FM.Enc.val(y_556), FM.Enc.val(rest_557)), FM.Enc.quan(p_555), FM.Enc.val(Machine.Val.arg{p_555, y_556, rest_557}), FM.Enc.quan(q_551), FM.Enc.val(x_552)]}, ks}),
        FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.val(Machine.Args.snoc(rest_557, q_551, x_552)), Con{Fun.Fr{Code.F.Args.snoc.k1(), [FM.Enc.val(rest_557), FM.Enc.val(y_556), FM.Enc.p(FM.Enc.val(y_556), FM.Enc.val(rest_557)), FM.Enc.quan(p_555), FM.Enc.val(Machine.Val.arg{p_555, y_556, rest_557}), FM.Enc.quan(q_551), FM.Enc.val(x_552)]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.val(Machine.Args.snoc(rest_557, q_551, x_552)), Con{Fun.Fr{Code.F.Args.snoc.k1(), [FM.Enc.val(rest_557), FM.Enc.val(y_556), FM.Enc.p(FM.Enc.val(y_556), FM.Enc.val(rest_557)), FM.Enc.quan(p_555), FM.Enc.val(Machine.Val.arg{p_555, y_556, rest_557}), FM.Enc.quan(q_551), FM.Enc.val(x_552)]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.val(Machine.Args.snoc(Machine.Val.arg{p_555, y_556, rest_557}, q_551, x_552)), ks}},
        FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.val(Machine.Args.snoc(rest_557, q_551, x_552)), Con{Fun.Fr{Code.F.Args.snoc.k1(), [FM.Enc.val(rest_557), FM.Enc.val(y_556), FM.Enc.p(FM.Enc.val(y_556), FM.Enc.val(rest_557)), FM.Enc.quan(p_555), FM.Enc.val(Machine.Val.arg{p_555, y_556, rest_557}), FM.Enc.quan(q_551), FM.Enc.val(x_552)]}, ks}}}),
        (3n, {==}))))
    case Machine.Val.clo{+_t_559, +_e_560}:
      (4n, {==})
    case Machine.Val.lab{+_k_561}:
      (4n, {==})
    case Machine.Val.rfl{}:
      (4n, {==})
    case Machine.Val.tup{+_q_562, +_a_563, +_b_564}:
      (4n, {==})
    case Machine.Val.call{+_k_565, +_xs_566}:
      (4n, {==})

def L.Args.frames(+xs_567: Machine.Val, +fs_568: List<&2, Machine.Fr>, +ks: List<&2, Fun.Fr>) ->
  Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Args.frames(), [FM.Enc.val(xs_567), FM.Enc.frs(fs_568)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.frs(Machine.Args.frames(xs_567, fs_568)), ks}}):
  match xs_567:
    case Machine.Val.nil{}:
      (2n, {==})
    case Machine.Val.env{+_x_569, +_rest_570}:
      (2n, {==})
    case Machine.Val.arg{+q_571, +x_572, +rest_573}:
      FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Args.frames(), [FM.Enc.val(Machine.Val.arg{q_571, x_572, rest_573}), FM.Enc.frs(fs_568)], ks}}, Fun.F.iter(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Args.frames(), [FM.Enc.val(Machine.Val.arg{q_571, x_572, rest_573}), FM.Enc.frs(fs_568)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.frs(Machine.Args.frames(Machine.Val.arg{q_571, x_572, rest_573}, fs_568)), ks}},
        FP.Reach.steps(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Args.frames(), [FM.Enc.val(Machine.Val.arg{q_571, x_572, rest_573}), FM.Enc.frs(fs_568)], ks}}),
        FP.Reach.trans(Code.prog(), Fun.F.iter(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Args.frames(), [FM.Enc.val(Machine.Val.arg{q_571, x_572, rest_573}), FM.Enc.frs(fs_568)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.frs(Machine.Args.frames(rest_573, fs_568)), Con{Fun.Fr{Code.F.Args.frames.k1(), [FM.Enc.val(rest_573), FM.Enc.val(x_572), FM.Enc.p(FM.Enc.val(x_572), FM.Enc.val(rest_573)), FM.Enc.quan(q_571), FM.Enc.val(Machine.Val.arg{q_571, x_572, rest_573}), FM.Enc.frs(fs_568)]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.frs(Machine.Args.frames(Machine.Val.arg{q_571, x_572, rest_573}, fs_568)), ks}},
        L.Args.frames(rest_573, fs_568, Con{Fun.Fr{Code.F.Args.frames.k1(), [FM.Enc.val(rest_573), FM.Enc.val(x_572), FM.Enc.p(FM.Enc.val(x_572), FM.Enc.val(rest_573)), FM.Enc.quan(q_571), FM.Enc.val(Machine.Val.arg{q_571, x_572, rest_573}), FM.Enc.frs(fs_568)]}, ks}),
        FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.frs(Machine.Args.frames(rest_573, fs_568)), Con{Fun.Fr{Code.F.Args.frames.k1(), [FM.Enc.val(rest_573), FM.Enc.val(x_572), FM.Enc.p(FM.Enc.val(x_572), FM.Enc.val(rest_573)), FM.Enc.quan(q_571), FM.Enc.val(Machine.Val.arg{q_571, x_572, rest_573}), FM.Enc.frs(fs_568)]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.frs(Machine.Args.frames(rest_573, fs_568)), Con{Fun.Fr{Code.F.Args.frames.k1(), [FM.Enc.val(rest_573), FM.Enc.val(x_572), FM.Enc.p(FM.Enc.val(x_572), FM.Enc.val(rest_573)), FM.Enc.quan(q_571), FM.Enc.val(Machine.Val.arg{q_571, x_572, rest_573}), FM.Enc.frs(fs_568)]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.frs(Machine.Args.frames(Machine.Val.arg{q_571, x_572, rest_573}, fs_568)), ks}},
        FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.frs(Machine.Args.frames(rest_573, fs_568)), Con{Fun.Fr{Code.F.Args.frames.k1(), [FM.Enc.val(rest_573), FM.Enc.val(x_572), FM.Enc.p(FM.Enc.val(x_572), FM.Enc.val(rest_573)), FM.Enc.quan(q_571), FM.Enc.val(Machine.Val.arg{q_571, x_572, rest_573}), FM.Enc.frs(fs_568)]}, ks}}}),
        (3n, {==}))))
    case Machine.Val.clo{+_t_575, +_e_576}:
      (2n, {==})
    case Machine.Val.lab{+_k_577}:
      (2n, {==})
    case Machine.Val.rfl{}:
      (2n, {==})
    case Machine.Val.tup{+_q_578, +_a_579, +_b_580}:
      (2n, {==})
    case Machine.Val.call{+_k_581, +_xs_582}:
      (2n, {==})

def L.Call.leaf(+w_583: Machine.Leaf, +k_584: List<&2, Nat>, +xs_585: Machine.Val, +fs_586: List<&2, Machine.Fr>, +ks: List<&2, Fun.Fr>) ->
  Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Call.leaf(), [FM.Enc.leaf(w_583), FM.Enc.name(k_584), FM.Enc.val(xs_585), FM.Enc.frs(fs_586)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Call.leaf(w_583, k_584, xs_585, fs_586)), ks}}):
  match w_583:
    case Machine.Leaf.need{}:
      (5n, {==})
    case Machine.Leaf.at{+t_587, +e_588, +rest_589}:
      FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Call.leaf(), [FM.Enc.leaf(Machine.Leaf.at{t_587, e_588, rest_589}), FM.Enc.name(k_584), FM.Enc.val(xs_585), FM.Enc.frs(fs_586)], ks}}, Fun.F.iter(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Call.leaf(), [FM.Enc.leaf(Machine.Leaf.at{t_587, e_588, rest_589}), FM.Enc.name(k_584), FM.Enc.val(xs_585), FM.Enc.frs(fs_586)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Call.leaf(Machine.Leaf.at{t_587, e_588, rest_589}, k_584, xs_585, fs_586)), ks}},
        FP.Reach.steps(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Call.leaf(), [FM.Enc.leaf(Machine.Leaf.at{t_587, e_588, rest_589}), FM.Enc.name(k_584), FM.Enc.val(xs_585), FM.Enc.frs(fs_586)], ks}}),
        FP.Reach.trans(Code.prog(), Fun.F.iter(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Call.leaf(), [FM.Enc.leaf(Machine.Leaf.at{t_587, e_588, rest_589}), FM.Enc.name(k_584), FM.Enc.val(xs_585), FM.Enc.frs(fs_586)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.frs(Machine.Args.frames(rest_589, fs_586)), Con{Fun.Fr{Code.F.Call.leaf.k1(), [FM.Enc.val(rest_589), FM.Enc.val(e_588), FM.Enc.p(FM.Enc.val(e_588), FM.Enc.val(rest_589)), FM.Enc.term(t_587), FM.Enc.leaf(Machine.Leaf.at{t_587, e_588, rest_589}), FM.Enc.name(k_584), FM.Enc.val(xs_585), FM.Enc.frs(fs_586)]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Call.leaf(Machine.Leaf.at{t_587, e_588, rest_589}, k_584, xs_585, fs_586)), ks}},
        L.Args.frames(rest_589, fs_586, Con{Fun.Fr{Code.F.Call.leaf.k1(), [FM.Enc.val(rest_589), FM.Enc.val(e_588), FM.Enc.p(FM.Enc.val(e_588), FM.Enc.val(rest_589)), FM.Enc.term(t_587), FM.Enc.leaf(Machine.Leaf.at{t_587, e_588, rest_589}), FM.Enc.name(k_584), FM.Enc.val(xs_585), FM.Enc.frs(fs_586)]}, ks}),
        FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.frs(Machine.Args.frames(rest_589, fs_586)), Con{Fun.Fr{Code.F.Call.leaf.k1(), [FM.Enc.val(rest_589), FM.Enc.val(e_588), FM.Enc.p(FM.Enc.val(e_588), FM.Enc.val(rest_589)), FM.Enc.term(t_587), FM.Enc.leaf(Machine.Leaf.at{t_587, e_588, rest_589}), FM.Enc.name(k_584), FM.Enc.val(xs_585), FM.Enc.frs(fs_586)]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.frs(Machine.Args.frames(rest_589, fs_586)), Con{Fun.Fr{Code.F.Call.leaf.k1(), [FM.Enc.val(rest_589), FM.Enc.val(e_588), FM.Enc.p(FM.Enc.val(e_588), FM.Enc.val(rest_589)), FM.Enc.term(t_587), FM.Enc.leaf(Machine.Leaf.at{t_587, e_588, rest_589}), FM.Enc.name(k_584), FM.Enc.val(xs_585), FM.Enc.frs(fs_586)]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Call.leaf(Machine.Leaf.at{t_587, e_588, rest_589}, k_584, xs_585, fs_586)), ks}},
        FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.frs(Machine.Args.frames(rest_589, fs_586)), Con{Fun.Fr{Code.F.Call.leaf.k1(), [FM.Enc.val(rest_589), FM.Enc.val(e_588), FM.Enc.p(FM.Enc.val(e_588), FM.Enc.val(rest_589)), FM.Enc.term(t_587), FM.Enc.leaf(Machine.Leaf.at{t_587, e_588, rest_589}), FM.Enc.name(k_584), FM.Enc.val(xs_585), FM.Enc.frs(fs_586)]}, ks}}}),
        (4n, {==}))))
    case Machine.Leaf.fail{}:
      (3n, {==})

def L.Call.try(+bk_591: List<&2, Source.Def>, +k_592: List<&2, Nat>, +xs_593: Machine.Val, +fs_594: List<&2, Machine.Fr>, +ks: List<&2, Fun.Fr>) ->
  Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Call.try(), [FM.Enc.book(bk_591), FM.Enc.name(k_592), FM.Enc.val(xs_593), FM.Enc.frs(fs_594)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Call.try(bk_591, k_592, xs_593, fs_594)), ks}}):
  FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Call.try(), [FM.Enc.book(bk_591), FM.Enc.name(k_592), FM.Enc.val(xs_593), FM.Enc.frs(fs_594)], ks}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Call.try(), [FM.Enc.book(bk_591), FM.Enc.name(k_592), FM.Enc.val(xs_593), FM.Enc.frs(fs_594)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Call.try(bk_591, k_592, xs_593, fs_594)), ks}},
    FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Call.try(), [FM.Enc.book(bk_591), FM.Enc.name(k_592), FM.Enc.val(xs_593), FM.Enc.frs(fs_594)], ks}}),
    FP.Reach.trans(Code.prog(), Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Call.try(), [FM.Enc.book(bk_591), FM.Enc.name(k_592), FM.Enc.val(xs_593), FM.Enc.frs(fs_594)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.mdef(Source.Book.get(bk_591, k_592)), Con{Fun.Fr{Code.F.Call.try.k1(), [FM.Enc.book(bk_591), FM.Enc.name(k_592), FM.Enc.val(xs_593), FM.Enc.frs(fs_594)]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Call.try(bk_591, k_592, xs_593, fs_594)), ks}},
    L.Book.get(bk_591, k_592, Con{Fun.Fr{Code.F.Call.try.k1(), [FM.Enc.book(bk_591), FM.Enc.name(k_592), FM.Enc.val(xs_593), FM.Enc.frs(fs_594)]}, ks}),
    FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.mdef(Source.Book.get(bk_591, k_592)), Con{Fun.Fr{Code.F.Call.try.k1(), [FM.Enc.book(bk_591), FM.Enc.name(k_592), FM.Enc.val(xs_593), FM.Enc.frs(fs_594)]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.mdef(Source.Book.get(bk_591, k_592)), Con{Fun.Fr{Code.F.Call.try.k1(), [FM.Enc.book(bk_591), FM.Enc.name(k_592), FM.Enc.val(xs_593), FM.Enc.frs(fs_594)]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Call.try(bk_591, k_592, xs_593, fs_594)), ks}},
    FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.mdef(Source.Book.get(bk_591, k_592)), Con{Fun.Fr{Code.F.Call.try.k1(), [FM.Enc.book(bk_591), FM.Enc.name(k_592), FM.Enc.val(xs_593), FM.Enc.frs(fs_594)]}, ks}}}),
    Elim.MDef(Source.Book.get(bk_591, k_592), m23 => Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Call.try.k1(), [FM.Enc.mdef(m23), FM.Enc.book(bk_591), FM.Enc.name(k_592), FM.Enc.val(xs_593), FM.Enc.frs(fs_594)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Call.got(m23, k_592, xs_593, fs_594)), ks}}),
    (2n, {==}),
    +df_596 => Elim.Def(df_596, m24 => Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Call.try.k1(), [FM.Enc.mdef(Some{m24}), FM.Enc.book(bk_591), FM.Enc.name(k_592), FM.Enc.val(xs_593), FM.Enc.frs(fs_594)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Call.got(Some{m24}, k_592, xs_593, fs_594)), ks}}),
    +n_597 => +t_598 => +v_599 => +o_600 => FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Call.try.k1(), [FM.Enc.mdef(Some{Source.Def{n_597, t_598, v_599, o_600}}), FM.Enc.book(bk_591), FM.Enc.name(k_592), FM.Enc.val(xs_593), FM.Enc.frs(fs_594)], ks}}, Fun.F.iter(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Call.try.k1(), [FM.Enc.mdef(Some{Source.Def{n_597, t_598, v_599, o_600}}), FM.Enc.book(bk_591), FM.Enc.name(k_592), FM.Enc.val(xs_593), FM.Enc.frs(fs_594)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Call.got(Some{Source.Def{n_597, t_598, v_599, o_600}}, k_592, xs_593, fs_594)), ks}},
    FP.Reach.steps(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Call.try.k1(), [FM.Enc.mdef(Some{Source.Def{n_597, t_598, v_599, o_600}}), FM.Enc.book(bk_591), FM.Enc.name(k_592), FM.Enc.val(xs_593), FM.Enc.frs(fs_594)], ks}}),
    FP.Reach.trans(Code.prog(), Fun.F.iter(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Call.try.k1(), [FM.Enc.mdef(Some{Source.Def{n_597, t_598, v_599, o_600}}), FM.Enc.book(bk_591), FM.Enc.name(k_592), FM.Enc.val(xs_593), FM.Enc.frs(fs_594)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Machine.Walk.go(v_599, Machine.Val.nil{}, xs_593)), Con{Fun.Fr{Code.F.Call.try.k2(), [FM.Enc.term(v_599), FM.Enc.name(n_597), Fun.V.z{}, FM.Enc.def(Source.Def{n_597, t_598, v_599, o_600}), FM.Enc.mdef(Some{Source.Def{n_597, t_598, v_599, o_600}}), FM.Enc.book(bk_591), FM.Enc.name(k_592), FM.Enc.val(xs_593), FM.Enc.frs(fs_594)]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Call.got(Some{Source.Def{n_597, t_598, v_599, o_600}}, k_592, xs_593, fs_594)), ks}},
    L.Walk.go(v_599, Machine.Val.nil{}, xs_593, Con{Fun.Fr{Code.F.Call.try.k2(), [FM.Enc.term(v_599), FM.Enc.name(n_597), Fun.V.z{}, FM.Enc.def(Source.Def{n_597, t_598, v_599, o_600}), FM.Enc.mdef(Some{Source.Def{n_597, t_598, v_599, o_600}}), FM.Enc.book(bk_591), FM.Enc.name(k_592), FM.Enc.val(xs_593), FM.Enc.frs(fs_594)]}, ks}),
    FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Machine.Walk.go(v_599, Machine.Val.nil{}, xs_593)), Con{Fun.Fr{Code.F.Call.try.k2(), [FM.Enc.term(v_599), FM.Enc.name(n_597), Fun.V.z{}, FM.Enc.def(Source.Def{n_597, t_598, v_599, o_600}), FM.Enc.mdef(Some{Source.Def{n_597, t_598, v_599, o_600}}), FM.Enc.book(bk_591), FM.Enc.name(k_592), FM.Enc.val(xs_593), FM.Enc.frs(fs_594)]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Machine.Walk.go(v_599, Machine.Val.nil{}, xs_593)), Con{Fun.Fr{Code.F.Call.try.k2(), [FM.Enc.term(v_599), FM.Enc.name(n_597), Fun.V.z{}, FM.Enc.def(Source.Def{n_597, t_598, v_599, o_600}), FM.Enc.mdef(Some{Source.Def{n_597, t_598, v_599, o_600}}), FM.Enc.book(bk_591), FM.Enc.name(k_592), FM.Enc.val(xs_593), FM.Enc.frs(fs_594)]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Call.got(Some{Source.Def{n_597, t_598, v_599, o_600}}, k_592, xs_593, fs_594)), ks}},
    FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Machine.Walk.go(v_599, Machine.Val.nil{}, xs_593)), Con{Fun.Fr{Code.F.Call.try.k2(), [FM.Enc.term(v_599), FM.Enc.name(n_597), Fun.V.z{}, FM.Enc.def(Source.Def{n_597, t_598, v_599, o_600}), FM.Enc.mdef(Some{Source.Def{n_597, t_598, v_599, o_600}}), FM.Enc.book(bk_591), FM.Enc.name(k_592), FM.Enc.val(xs_593), FM.Enc.frs(fs_594)]}, ks}}}),
    FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Call.try.k2(), [FM.Enc.leaf(Machine.Walk.go(v_599, Machine.Val.nil{}, xs_593)), FM.Enc.term(v_599), FM.Enc.name(n_597), Fun.V.z{}, FM.Enc.def(Source.Def{n_597, t_598, v_599, o_600}), FM.Enc.mdef(Some{Source.Def{n_597, t_598, v_599, o_600}}), FM.Enc.book(bk_591), FM.Enc.name(k_592), FM.Enc.val(xs_593), FM.Enc.frs(fs_594)], ks}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Call.try.k2(), [FM.Enc.leaf(Machine.Walk.go(v_599, Machine.Val.nil{}, xs_593)), FM.Enc.term(v_599), FM.Enc.name(n_597), Fun.V.z{}, FM.Enc.def(Source.Def{n_597, t_598, v_599, o_600}), FM.Enc.mdef(Some{Source.Def{n_597, t_598, v_599, o_600}}), FM.Enc.book(bk_591), FM.Enc.name(k_592), FM.Enc.val(xs_593), FM.Enc.frs(fs_594)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Call.leaf(Machine.Walk.go(v_599, Machine.Val.nil{}, xs_593), k_592, xs_593, fs_594)), ks}},
    FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Call.try.k2(), [FM.Enc.leaf(Machine.Walk.go(v_599, Machine.Val.nil{}, xs_593)), FM.Enc.term(v_599), FM.Enc.name(n_597), Fun.V.z{}, FM.Enc.def(Source.Def{n_597, t_598, v_599, o_600}), FM.Enc.mdef(Some{Source.Def{n_597, t_598, v_599, o_600}}), FM.Enc.book(bk_591), FM.Enc.name(k_592), FM.Enc.val(xs_593), FM.Enc.frs(fs_594)], ks}}),
    L.Call.leaf(Machine.Walk.go(v_599, Machine.Val.nil{}, xs_593), k_592, xs_593, fs_594, ks))))))))))

def L.Apply.go(+f_602: Machine.Val, +q_603: Source.Quan, +x_604: Machine.Val, +bk_605: List<&2, Source.Def>, +fs_606: List<&2, Machine.Fr>, +ks: List<&2, Fun.Fr>) ->
  Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Apply.go(), [FM.Enc.val(f_602), FM.Enc.quan(q_603), FM.Enc.val(x_604), FM.Enc.book(bk_605), FM.Enc.frs(fs_606)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Apply.go(f_602, q_603, x_604, bk_605, fs_606)), ks}}):
  match f_602:
    case Machine.Val.nil{}:
      (3n, {==})
    case Machine.Val.env{+_x_607, +_rest_608}:
      (3n, {==})
    case Machine.Val.arg{+_q_609, +_x_610, +_rest_611}:
      (3n, {==})
    case Machine.Val.clo{+t_612, +e_613}:
      match t_612:
        case Source.Term.Var{+_i_614}:
          (5n, {==})
        case Source.Term.Ref{+_k_615}:
          (5n, {==})
        case Source.Term.Ann{+_x_616, +_t_617}:
          (5n, {==})
        case Source.Term.Let{+_q_618, +_v_619, +_f_620}:
          (5n, {==})
        case Source.Term.Typ{+_q_621}:
          (5n, {==})
        case Source.Term.Min{+_a_622, +_b_623}:
          (5n, {==})
        case Source.Term.All{+_q_624, +_a_625, +_b_626}:
          (5n, {==})
        case Source.Term.Lam{+p_627, +b_628}:
          FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Apply.go(), [FM.Enc.val(Machine.Val.clo{Source.Term.Lam{p_627, b_628}, e_613}), FM.Enc.quan(q_603), FM.Enc.val(x_604), FM.Enc.book(bk_605), FM.Enc.frs(fs_606)], ks}}, Fun.F.iter(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Apply.go(), [FM.Enc.val(Machine.Val.clo{Source.Term.Lam{p_627, b_628}, e_613}), FM.Enc.quan(q_603), FM.Enc.val(x_604), FM.Enc.book(bk_605), FM.Enc.frs(fs_606)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Apply.go(Machine.Val.clo{Source.Term.Lam{p_627, b_628}, e_613}, q_603, x_604, bk_605, fs_606)), ks}},
            FP.Reach.steps(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Apply.go(), [FM.Enc.val(Machine.Val.clo{Source.Term.Lam{p_627, b_628}, e_613}), FM.Enc.quan(q_603), FM.Enc.val(x_604), FM.Enc.book(bk_605), FM.Enc.frs(fs_606)], ks}}),
            FP.Reach.trans(Code.prog(), Fun.F.iter(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Apply.go(), [FM.Enc.val(Machine.Val.clo{Source.Term.Lam{p_627, b_628}, e_613}), FM.Enc.quan(q_603), FM.Enc.val(x_604), FM.Enc.book(bk_605), FM.Enc.frs(fs_606)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Lam.takes(p_627, q_603, x_604)), Con{Fun.Fr{Code.F.Apply.go.k1(), [FM.Enc.term(b_628), FM.Enc.quan(p_627), FM.Enc.val(e_613), FM.Enc.term(Source.Term.Lam{p_627, b_628}), FM.Enc.val(Machine.Val.clo{Source.Term.Lam{p_627, b_628}, e_613}), FM.Enc.quan(q_603), FM.Enc.val(x_604), FM.Enc.book(bk_605), FM.Enc.frs(fs_606)]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Apply.go(Machine.Val.clo{Source.Term.Lam{p_627, b_628}, e_613}, q_603, x_604, bk_605, fs_606)), ks}},
            L.Lam.takes(p_627, q_603, x_604, Con{Fun.Fr{Code.F.Apply.go.k1(), [FM.Enc.term(b_628), FM.Enc.quan(p_627), FM.Enc.val(e_613), FM.Enc.term(Source.Term.Lam{p_627, b_628}), FM.Enc.val(Machine.Val.clo{Source.Term.Lam{p_627, b_628}, e_613}), FM.Enc.quan(q_603), FM.Enc.val(x_604), FM.Enc.book(bk_605), FM.Enc.frs(fs_606)]}, ks}),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Lam.takes(p_627, q_603, x_604)), Con{Fun.Fr{Code.F.Apply.go.k1(), [FM.Enc.term(b_628), FM.Enc.quan(p_627), FM.Enc.val(e_613), FM.Enc.term(Source.Term.Lam{p_627, b_628}), FM.Enc.val(Machine.Val.clo{Source.Term.Lam{p_627, b_628}, e_613}), FM.Enc.quan(q_603), FM.Enc.val(x_604), FM.Enc.book(bk_605), FM.Enc.frs(fs_606)]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Lam.takes(p_627, q_603, x_604)), Con{Fun.Fr{Code.F.Apply.go.k1(), [FM.Enc.term(b_628), FM.Enc.quan(p_627), FM.Enc.val(e_613), FM.Enc.term(Source.Term.Lam{p_627, b_628}), FM.Enc.val(Machine.Val.clo{Source.Term.Lam{p_627, b_628}, e_613}), FM.Enc.quan(q_603), FM.Enc.val(x_604), FM.Enc.book(bk_605), FM.Enc.frs(fs_606)]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Apply.go(Machine.Val.clo{Source.Term.Lam{p_627, b_628}, e_613}, q_603, x_604, bk_605, fs_606)), ks}},
            FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Lam.takes(p_627, q_603, x_604)), Con{Fun.Fr{Code.F.Apply.go.k1(), [FM.Enc.term(b_628), FM.Enc.quan(p_627), FM.Enc.val(e_613), FM.Enc.term(Source.Term.Lam{p_627, b_628}), FM.Enc.val(Machine.Val.clo{Source.Term.Lam{p_627, b_628}, e_613}), FM.Enc.quan(q_603), FM.Enc.val(x_604), FM.Enc.book(bk_605), FM.Enc.frs(fs_606)]}, ks}}}),
            Elim.Bool(Machine.Lam.takes(p_627, q_603, x_604), m25 => Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Apply.go.k1(), [FM.Enc.bool(m25), FM.Enc.term(b_628), FM.Enc.quan(p_627), FM.Enc.val(e_613), FM.Enc.term(Source.Term.Lam{p_627, b_628}), FM.Enc.val(Machine.Val.clo{Source.Term.Lam{p_627, b_628}, e_613}), FM.Enc.quan(q_603), FM.Enc.val(x_604), FM.Enc.book(bk_605), FM.Enc.frs(fs_606)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.move(Source.Bool.lazy(Machine.Move, m25, u => Machine.Move.go{Machine.St.eval{b_628, Machine.Val.env{x_604, e_613}, fs_606}}, u => Machine.Move.stuck{})), ks}}),
            (2n, {==}),
            (6n, {==})))))
        case Source.Term.App{+_q_630, +_f_631, +_x_632}:
          (5n, {==})
        case Source.Term.Sig{+_q_633, +_a_634, +_b_635}:
          (5n, {==})
        case Source.Term.Tup{+_q_636, +_a_637, +_b_638}:
          (5n, {==})
        case Source.Term.Prj{+h_639}:
          match q_603:
            case Source.Q0{}:
              (5n, {==})
            case Source.Q1{}:
              match x_604:
                case Machine.Val.nil{}:
                  (6n, {==})
                case Machine.Val.env{+_x_640, +_rest_641}:
                  (6n, {==})
                case Machine.Val.arg{+_q_642, +_x_643, +_rest_644}:
                  (6n, {==})
                case Machine.Val.clo{+_t_645, +_e_646}:
                  (6n, {==})
                case Machine.Val.lab{+_k_647}:
                  (6n, {==})
                case Machine.Val.rfl{}:
                  (6n, {==})
                case Machine.Val.tup{+r_648, +a_649, +b_650}:
                  match r_648:
                    case Source.Q0{}:
                      (15n, {==})
                    case Source.Q1{}:
                      (15n, {==})
                    case Source.Q2{}:
                      (15n, {==})
                case Machine.Val.call{+_k_651, +_xs_652}:
                  (6n, {==})
            case Source.Q2{}:
              match x_604:
                case Machine.Val.nil{}:
                  (6n, {==})
                case Machine.Val.env{+_x_653, +_rest_654}:
                  (6n, {==})
                case Machine.Val.arg{+_q_655, +_x_656, +_rest_657}:
                  (6n, {==})
                case Machine.Val.clo{+_t_658, +_e_659}:
                  (6n, {==})
                case Machine.Val.lab{+_k_660}:
                  (6n, {==})
                case Machine.Val.rfl{}:
                  (6n, {==})
                case Machine.Val.tup{+r_661, +a_662, +b_663}:
                  match r_661:
                    case Source.Q0{}:
                      (15n, {==})
                    case Source.Q1{}:
                      (15n, {==})
                    case Source.Q2{}:
                      (15n, {==})
                case Machine.Val.call{+_k_664, +_xs_665}:
                  (6n, {==})
        case Source.Term.Enu{+_ks_666}:
          (5n, {==})
        case Source.Term.Lab{+_k_667}:
          (5n, {==})
        case Source.Term.Mat{+k_668, +h_669, +m_670}:
          match q_603:
            case Source.Q0{}:
              (7n, {==})
            case Source.Q1{}:
              match x_604:
                case Machine.Val.nil{}:
                  (8n, {==})
                case Machine.Val.env{+_x_671, +_rest_672}:
                  (8n, {==})
                case Machine.Val.arg{+_q_673, +_x_674, +_rest_675}:
                  (8n, {==})
                case Machine.Val.clo{+_t_676, +_e_677}:
                  (8n, {==})
                case Machine.Val.lab{+j_678}:
                  FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Apply.go(), [FM.Enc.val(Machine.Val.clo{Source.Term.Mat{k_668, h_669, m_670}, e_613}), FM.Enc.quan(Source.Q1{}), FM.Enc.val(Machine.Val.lab{j_678}), FM.Enc.book(bk_605), FM.Enc.frs(fs_606)], ks}}, Fun.F.iter(8n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Apply.go(), [FM.Enc.val(Machine.Val.clo{Source.Term.Mat{k_668, h_669, m_670}, e_613}), FM.Enc.quan(Source.Q1{}), FM.Enc.val(Machine.Val.lab{j_678}), FM.Enc.book(bk_605), FM.Enc.frs(fs_606)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Apply.go(Machine.Val.clo{Source.Term.Mat{k_668, h_669, m_670}, e_613}, Source.Q1{}, Machine.Val.lab{j_678}, bk_605, fs_606)), ks}},
                    FP.Reach.steps(8n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Apply.go(), [FM.Enc.val(Machine.Val.clo{Source.Term.Mat{k_668, h_669, m_670}, e_613}), FM.Enc.quan(Source.Q1{}), FM.Enc.val(Machine.Val.lab{j_678}), FM.Enc.book(bk_605), FM.Enc.frs(fs_606)], ks}}),
                    FP.Reach.trans(Code.prog(), Fun.F.iter(8n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Apply.go(), [FM.Enc.val(Machine.Val.clo{Source.Term.Mat{k_668, h_669, m_670}, e_613}), FM.Enc.quan(Source.Q1{}), FM.Enc.val(Machine.Val.lab{j_678}), FM.Enc.book(bk_605), FM.Enc.frs(fs_606)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(j_678, k_668)), Con{Fun.Fr{Code.F.Apply.go.k2(), [Fun.V.z{}, FM.Enc.name(j_678), FM.Enc.term(m_670), FM.Enc.term(h_669), FM.Enc.p(FM.Enc.term(h_669), FM.Enc.term(m_670)), FM.Enc.name(k_668), FM.Enc.val(e_613), FM.Enc.term(Source.Term.Mat{k_668, h_669, m_670}), FM.Enc.val(Machine.Val.clo{Source.Term.Mat{k_668, h_669, m_670}, e_613}), FM.Enc.quan(Source.Q1{}), FM.Enc.val(Machine.Val.lab{j_678}), FM.Enc.book(bk_605), FM.Enc.frs(fs_606)]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Apply.go(Machine.Val.clo{Source.Term.Mat{k_668, h_669, m_670}, e_613}, Source.Q1{}, Machine.Val.lab{j_678}, bk_605, fs_606)), ks}},
                    L.Name.is_eq(j_678, k_668, Con{Fun.Fr{Code.F.Apply.go.k2(), [Fun.V.z{}, FM.Enc.name(j_678), FM.Enc.term(m_670), FM.Enc.term(h_669), FM.Enc.p(FM.Enc.term(h_669), FM.Enc.term(m_670)), FM.Enc.name(k_668), FM.Enc.val(e_613), FM.Enc.term(Source.Term.Mat{k_668, h_669, m_670}), FM.Enc.val(Machine.Val.clo{Source.Term.Mat{k_668, h_669, m_670}, e_613}), FM.Enc.quan(Source.Q1{}), FM.Enc.val(Machine.Val.lab{j_678}), FM.Enc.book(bk_605), FM.Enc.frs(fs_606)]}, ks}),
                    FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(j_678, k_668)), Con{Fun.Fr{Code.F.Apply.go.k2(), [Fun.V.z{}, FM.Enc.name(j_678), FM.Enc.term(m_670), FM.Enc.term(h_669), FM.Enc.p(FM.Enc.term(h_669), FM.Enc.term(m_670)), FM.Enc.name(k_668), FM.Enc.val(e_613), FM.Enc.term(Source.Term.Mat{k_668, h_669, m_670}), FM.Enc.val(Machine.Val.clo{Source.Term.Mat{k_668, h_669, m_670}, e_613}), FM.Enc.quan(Source.Q1{}), FM.Enc.val(Machine.Val.lab{j_678}), FM.Enc.book(bk_605), FM.Enc.frs(fs_606)]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(j_678, k_668)), Con{Fun.Fr{Code.F.Apply.go.k2(), [Fun.V.z{}, FM.Enc.name(j_678), FM.Enc.term(m_670), FM.Enc.term(h_669), FM.Enc.p(FM.Enc.term(h_669), FM.Enc.term(m_670)), FM.Enc.name(k_668), FM.Enc.val(e_613), FM.Enc.term(Source.Term.Mat{k_668, h_669, m_670}), FM.Enc.val(Machine.Val.clo{Source.Term.Mat{k_668, h_669, m_670}, e_613}), FM.Enc.quan(Source.Q1{}), FM.Enc.val(Machine.Val.lab{j_678}), FM.Enc.book(bk_605), FM.Enc.frs(fs_606)]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Apply.go(Machine.Val.clo{Source.Term.Mat{k_668, h_669, m_670}, e_613}, Source.Q1{}, Machine.Val.lab{j_678}, bk_605, fs_606)), ks}},
                    FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(j_678, k_668)), Con{Fun.Fr{Code.F.Apply.go.k2(), [Fun.V.z{}, FM.Enc.name(j_678), FM.Enc.term(m_670), FM.Enc.term(h_669), FM.Enc.p(FM.Enc.term(h_669), FM.Enc.term(m_670)), FM.Enc.name(k_668), FM.Enc.val(e_613), FM.Enc.term(Source.Term.Mat{k_668, h_669, m_670}), FM.Enc.val(Machine.Val.clo{Source.Term.Mat{k_668, h_669, m_670}, e_613}), FM.Enc.quan(Source.Q1{}), FM.Enc.val(Machine.Val.lab{j_678}), FM.Enc.book(bk_605), FM.Enc.frs(fs_606)]}, ks}}}),
                    Elim.Bool(Source.Name.is_eq(j_678, k_668), m26 => Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Apply.go.k2(), [FM.Enc.bool(m26), Fun.V.z{}, FM.Enc.name(j_678), FM.Enc.term(m_670), FM.Enc.term(h_669), FM.Enc.p(FM.Enc.term(h_669), FM.Enc.term(m_670)), FM.Enc.name(k_668), FM.Enc.val(e_613), FM.Enc.term(Source.Term.Mat{k_668, h_669, m_670}), FM.Enc.val(Machine.Val.clo{Source.Term.Mat{k_668, h_669, m_670}, e_613}), FM.Enc.quan(Source.Q1{}), FM.Enc.val(Machine.Val.lab{j_678}), FM.Enc.book(bk_605), FM.Enc.frs(fs_606)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.move(Source.Bool.lazy(Machine.Move, m26, u => Machine.Move.go{Machine.St.eval{h_669, e_613, fs_606}}, u => Machine.Move.go{Machine.St.eval{m_670, e_613, Con{Machine.Fr.arg{Source.Q1{}, Machine.Val.lab{j_678}}, fs_606}}})), ks}}),
                    (8n, {==}),
                    (5n, {==})))))
                case Machine.Val.rfl{}:
                  (8n, {==})
                case Machine.Val.tup{+_q_680, +_a_681, +_b_682}:
                  (8n, {==})
                case Machine.Val.call{+_k_683, +_xs_684}:
                  (8n, {==})
            case Source.Q2{}:
              match x_604:
                case Machine.Val.nil{}:
                  (8n, {==})
                case Machine.Val.env{+_x_685, +_rest_686}:
                  (8n, {==})
                case Machine.Val.arg{+_q_687, +_x_688, +_rest_689}:
                  (8n, {==})
                case Machine.Val.clo{+_t_690, +_e_691}:
                  (8n, {==})
                case Machine.Val.lab{+j_692}:
                  FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Apply.go(), [FM.Enc.val(Machine.Val.clo{Source.Term.Mat{k_668, h_669, m_670}, e_613}), FM.Enc.quan(Source.Q2{}), FM.Enc.val(Machine.Val.lab{j_692}), FM.Enc.book(bk_605), FM.Enc.frs(fs_606)], ks}}, Fun.F.iter(8n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Apply.go(), [FM.Enc.val(Machine.Val.clo{Source.Term.Mat{k_668, h_669, m_670}, e_613}), FM.Enc.quan(Source.Q2{}), FM.Enc.val(Machine.Val.lab{j_692}), FM.Enc.book(bk_605), FM.Enc.frs(fs_606)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Apply.go(Machine.Val.clo{Source.Term.Mat{k_668, h_669, m_670}, e_613}, Source.Q2{}, Machine.Val.lab{j_692}, bk_605, fs_606)), ks}},
                    FP.Reach.steps(8n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Apply.go(), [FM.Enc.val(Machine.Val.clo{Source.Term.Mat{k_668, h_669, m_670}, e_613}), FM.Enc.quan(Source.Q2{}), FM.Enc.val(Machine.Val.lab{j_692}), FM.Enc.book(bk_605), FM.Enc.frs(fs_606)], ks}}),
                    FP.Reach.trans(Code.prog(), Fun.F.iter(8n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Apply.go(), [FM.Enc.val(Machine.Val.clo{Source.Term.Mat{k_668, h_669, m_670}, e_613}), FM.Enc.quan(Source.Q2{}), FM.Enc.val(Machine.Val.lab{j_692}), FM.Enc.book(bk_605), FM.Enc.frs(fs_606)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(j_692, k_668)), Con{Fun.Fr{Code.F.Apply.go.k2(), [Fun.V.z{}, FM.Enc.name(j_692), FM.Enc.term(m_670), FM.Enc.term(h_669), FM.Enc.p(FM.Enc.term(h_669), FM.Enc.term(m_670)), FM.Enc.name(k_668), FM.Enc.val(e_613), FM.Enc.term(Source.Term.Mat{k_668, h_669, m_670}), FM.Enc.val(Machine.Val.clo{Source.Term.Mat{k_668, h_669, m_670}, e_613}), FM.Enc.quan(Source.Q2{}), FM.Enc.val(Machine.Val.lab{j_692}), FM.Enc.book(bk_605), FM.Enc.frs(fs_606)]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Apply.go(Machine.Val.clo{Source.Term.Mat{k_668, h_669, m_670}, e_613}, Source.Q2{}, Machine.Val.lab{j_692}, bk_605, fs_606)), ks}},
                    L.Name.is_eq(j_692, k_668, Con{Fun.Fr{Code.F.Apply.go.k2(), [Fun.V.z{}, FM.Enc.name(j_692), FM.Enc.term(m_670), FM.Enc.term(h_669), FM.Enc.p(FM.Enc.term(h_669), FM.Enc.term(m_670)), FM.Enc.name(k_668), FM.Enc.val(e_613), FM.Enc.term(Source.Term.Mat{k_668, h_669, m_670}), FM.Enc.val(Machine.Val.clo{Source.Term.Mat{k_668, h_669, m_670}, e_613}), FM.Enc.quan(Source.Q2{}), FM.Enc.val(Machine.Val.lab{j_692}), FM.Enc.book(bk_605), FM.Enc.frs(fs_606)]}, ks}),
                    FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(j_692, k_668)), Con{Fun.Fr{Code.F.Apply.go.k2(), [Fun.V.z{}, FM.Enc.name(j_692), FM.Enc.term(m_670), FM.Enc.term(h_669), FM.Enc.p(FM.Enc.term(h_669), FM.Enc.term(m_670)), FM.Enc.name(k_668), FM.Enc.val(e_613), FM.Enc.term(Source.Term.Mat{k_668, h_669, m_670}), FM.Enc.val(Machine.Val.clo{Source.Term.Mat{k_668, h_669, m_670}, e_613}), FM.Enc.quan(Source.Q2{}), FM.Enc.val(Machine.Val.lab{j_692}), FM.Enc.book(bk_605), FM.Enc.frs(fs_606)]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(j_692, k_668)), Con{Fun.Fr{Code.F.Apply.go.k2(), [Fun.V.z{}, FM.Enc.name(j_692), FM.Enc.term(m_670), FM.Enc.term(h_669), FM.Enc.p(FM.Enc.term(h_669), FM.Enc.term(m_670)), FM.Enc.name(k_668), FM.Enc.val(e_613), FM.Enc.term(Source.Term.Mat{k_668, h_669, m_670}), FM.Enc.val(Machine.Val.clo{Source.Term.Mat{k_668, h_669, m_670}, e_613}), FM.Enc.quan(Source.Q2{}), FM.Enc.val(Machine.Val.lab{j_692}), FM.Enc.book(bk_605), FM.Enc.frs(fs_606)]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Apply.go(Machine.Val.clo{Source.Term.Mat{k_668, h_669, m_670}, e_613}, Source.Q2{}, Machine.Val.lab{j_692}, bk_605, fs_606)), ks}},
                    FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(j_692, k_668)), Con{Fun.Fr{Code.F.Apply.go.k2(), [Fun.V.z{}, FM.Enc.name(j_692), FM.Enc.term(m_670), FM.Enc.term(h_669), FM.Enc.p(FM.Enc.term(h_669), FM.Enc.term(m_670)), FM.Enc.name(k_668), FM.Enc.val(e_613), FM.Enc.term(Source.Term.Mat{k_668, h_669, m_670}), FM.Enc.val(Machine.Val.clo{Source.Term.Mat{k_668, h_669, m_670}, e_613}), FM.Enc.quan(Source.Q2{}), FM.Enc.val(Machine.Val.lab{j_692}), FM.Enc.book(bk_605), FM.Enc.frs(fs_606)]}, ks}}}),
                    Elim.Bool(Source.Name.is_eq(j_692, k_668), m27 => Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Apply.go.k2(), [FM.Enc.bool(m27), Fun.V.z{}, FM.Enc.name(j_692), FM.Enc.term(m_670), FM.Enc.term(h_669), FM.Enc.p(FM.Enc.term(h_669), FM.Enc.term(m_670)), FM.Enc.name(k_668), FM.Enc.val(e_613), FM.Enc.term(Source.Term.Mat{k_668, h_669, m_670}), FM.Enc.val(Machine.Val.clo{Source.Term.Mat{k_668, h_669, m_670}, e_613}), FM.Enc.quan(Source.Q2{}), FM.Enc.val(Machine.Val.lab{j_692}), FM.Enc.book(bk_605), FM.Enc.frs(fs_606)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.move(Source.Bool.lazy(Machine.Move, m27, u => Machine.Move.go{Machine.St.eval{h_669, e_613, fs_606}}, u => Machine.Move.go{Machine.St.eval{m_670, e_613, Con{Machine.Fr.arg{Source.Q2{}, Machine.Val.lab{j_692}}, fs_606}}})), ks}}),
                    (8n, {==}),
                    (5n, {==})))))
                case Machine.Val.rfl{}:
                  (8n, {==})
                case Machine.Val.tup{+_q_694, +_a_695, +_b_696}:
                  (8n, {==})
                case Machine.Val.call{+_k_697, +_xs_698}:
                  (8n, {==})
        case Source.Term.Efq{}:
          (5n, {==})
        case Source.Term.Eql{+_a_699, +_b_700, +_t_701}:
          (5n, {==})
        case Source.Term.Rfl{}:
          (5n, {==})
        case Source.Term.Rwt{+_e_702, +_p_703, +_f_704}:
          (5n, {==})
    case Machine.Val.lab{+_k_705}:
      (3n, {==})
    case Machine.Val.rfl{}:
      (3n, {==})
    case Machine.Val.tup{+_q_706, +_a_707, +_b_708}:
      (3n, {==})
    case Machine.Val.call{+k_709, +xs_710}:
      FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Apply.go(), [FM.Enc.val(Machine.Val.call{k_709, xs_710}), FM.Enc.quan(q_603), FM.Enc.val(x_604), FM.Enc.book(bk_605), FM.Enc.frs(fs_606)], ks}}, Fun.F.iter(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Apply.go(), [FM.Enc.val(Machine.Val.call{k_709, xs_710}), FM.Enc.quan(q_603), FM.Enc.val(x_604), FM.Enc.book(bk_605), FM.Enc.frs(fs_606)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Apply.go(Machine.Val.call{k_709, xs_710}, q_603, x_604, bk_605, fs_606)), ks}},
        FP.Reach.steps(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Apply.go(), [FM.Enc.val(Machine.Val.call{k_709, xs_710}), FM.Enc.quan(q_603), FM.Enc.val(x_604), FM.Enc.book(bk_605), FM.Enc.frs(fs_606)], ks}}),
        FP.Reach.trans(Code.prog(), Fun.F.iter(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Apply.go(), [FM.Enc.val(Machine.Val.call{k_709, xs_710}), FM.Enc.quan(q_603), FM.Enc.val(x_604), FM.Enc.book(bk_605), FM.Enc.frs(fs_606)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.val(Machine.Args.snoc(xs_710, q_603, x_604)), Con{Fun.Fr{Code.F.Apply.go.k3(), [FM.Enc.val(xs_710), FM.Enc.name(k_709), FM.Enc.val(Machine.Val.call{k_709, xs_710}), FM.Enc.quan(q_603), FM.Enc.val(x_604), FM.Enc.book(bk_605), FM.Enc.frs(fs_606)]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Apply.go(Machine.Val.call{k_709, xs_710}, q_603, x_604, bk_605, fs_606)), ks}},
        L.Args.snoc(xs_710, q_603, x_604, Con{Fun.Fr{Code.F.Apply.go.k3(), [FM.Enc.val(xs_710), FM.Enc.name(k_709), FM.Enc.val(Machine.Val.call{k_709, xs_710}), FM.Enc.quan(q_603), FM.Enc.val(x_604), FM.Enc.book(bk_605), FM.Enc.frs(fs_606)]}, ks}),
        FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.val(Machine.Args.snoc(xs_710, q_603, x_604)), Con{Fun.Fr{Code.F.Apply.go.k3(), [FM.Enc.val(xs_710), FM.Enc.name(k_709), FM.Enc.val(Machine.Val.call{k_709, xs_710}), FM.Enc.quan(q_603), FM.Enc.val(x_604), FM.Enc.book(bk_605), FM.Enc.frs(fs_606)]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.val(Machine.Args.snoc(xs_710, q_603, x_604)), Con{Fun.Fr{Code.F.Apply.go.k3(), [FM.Enc.val(xs_710), FM.Enc.name(k_709), FM.Enc.val(Machine.Val.call{k_709, xs_710}), FM.Enc.quan(q_603), FM.Enc.val(x_604), FM.Enc.book(bk_605), FM.Enc.frs(fs_606)]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Apply.go(Machine.Val.call{k_709, xs_710}, q_603, x_604, bk_605, fs_606)), ks}},
        FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.val(Machine.Args.snoc(xs_710, q_603, x_604)), Con{Fun.Fr{Code.F.Apply.go.k3(), [FM.Enc.val(xs_710), FM.Enc.name(k_709), FM.Enc.val(Machine.Val.call{k_709, xs_710}), FM.Enc.quan(q_603), FM.Enc.val(x_604), FM.Enc.book(bk_605), FM.Enc.frs(fs_606)]}, ks}}}),
        FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Apply.go.k3(), [FM.Enc.val(Machine.Args.snoc(xs_710, q_603, x_604)), FM.Enc.val(xs_710), FM.Enc.name(k_709), FM.Enc.val(Machine.Val.call{k_709, xs_710}), FM.Enc.quan(q_603), FM.Enc.val(x_604), FM.Enc.book(bk_605), FM.Enc.frs(fs_606)], ks}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Apply.go.k3(), [FM.Enc.val(Machine.Args.snoc(xs_710, q_603, x_604)), FM.Enc.val(xs_710), FM.Enc.name(k_709), FM.Enc.val(Machine.Val.call{k_709, xs_710}), FM.Enc.quan(q_603), FM.Enc.val(x_604), FM.Enc.book(bk_605), FM.Enc.frs(fs_606)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Call.try(bk_605, k_709, Machine.Args.snoc(xs_710, q_603, x_604), fs_606)), ks}},
        FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Apply.go.k3(), [FM.Enc.val(Machine.Args.snoc(xs_710, q_603, x_604)), FM.Enc.val(xs_710), FM.Enc.name(k_709), FM.Enc.val(Machine.Val.call{k_709, xs_710}), FM.Enc.quan(q_603), FM.Enc.val(x_604), FM.Enc.book(bk_605), FM.Enc.frs(fs_606)], ks}}),
        L.Call.try(bk_605, k_709, Machine.Args.snoc(xs_710, q_603, x_604), fs_606, ks)))))

def L.Val.force(+x_712: Machine.Val, +fs_713: List<&2, Machine.Fr>, +ks: List<&2, Fun.Fr>) ->
  Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.force(), [FM.Enc.val(x_712), FM.Enc.frs(fs_713)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Val.force(x_712, fs_713)), ks}}):
  match x_712:
    case Machine.Val.nil{}:
      (4n, {==})
    case Machine.Val.env{+_x_714, +_rest_715}:
      (4n, {==})
    case Machine.Val.arg{+_q_716, +_x_717, +_rest_718}:
      (4n, {==})
    case Machine.Val.clo{+t_719, +e_720}:
      (5n, {==})
    case Machine.Val.lab{+_k_721}:
      (4n, {==})
    case Machine.Val.rfl{}:
      (4n, {==})
    case Machine.Val.tup{+_q_722, +_a_723, +_b_724}:
      (4n, {==})
    case Machine.Val.call{+_k_725, +_xs_726}:
      (4n, {==})

def L.Eval.go(+t_727: Source.Term, +e_728: Machine.Val, +fs_729: List<&2, Machine.Fr>, +bk_730: List<&2, Source.Def>, +ks: List<&2, Fun.Fr>) ->
  Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Eval.go(), [FM.Enc.term(t_727), FM.Enc.val(e_728), FM.Enc.frs(fs_729), FM.Enc.book(bk_730)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Eval.go(t_727, e_728, fs_729, bk_730)), ks}}):
  match t_727:
    case Source.Term.Var{+i_731}:
      FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Eval.go(), [FM.Enc.term(Source.Term.Var{i_731}), FM.Enc.val(e_728), FM.Enc.frs(fs_729), FM.Enc.book(bk_730)], ks}}, Fun.F.iter(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Eval.go(), [FM.Enc.term(Source.Term.Var{i_731}), FM.Enc.val(e_728), FM.Enc.frs(fs_729), FM.Enc.book(bk_730)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Eval.go(Source.Term.Var{i_731}, e_728, fs_729, bk_730)), ks}},
        FP.Reach.steps(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Eval.go(), [FM.Enc.term(Source.Term.Var{i_731}), FM.Enc.val(e_728), FM.Enc.frs(fs_729), FM.Enc.book(bk_730)], ks}}),
        FP.Reach.trans(Code.prog(), Fun.F.iter(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Eval.go(), [FM.Enc.term(Source.Term.Var{i_731}), FM.Enc.val(e_728), FM.Enc.frs(fs_729), FM.Enc.book(bk_730)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.look(Machine.Env.find(e_728, i_731)), Con{Fun.Fr{Code.F.Eval.go.k1(), [Fun.V.z{}, FM.Enc.nat(i_731), FM.Enc.term(Source.Term.Var{i_731}), FM.Enc.val(e_728), FM.Enc.frs(fs_729), FM.Enc.book(bk_730)]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Eval.go(Source.Term.Var{i_731}, e_728, fs_729, bk_730)), ks}},
        L.Env.find(e_728, i_731, Con{Fun.Fr{Code.F.Eval.go.k1(), [Fun.V.z{}, FM.Enc.nat(i_731), FM.Enc.term(Source.Term.Var{i_731}), FM.Enc.val(e_728), FM.Enc.frs(fs_729), FM.Enc.book(bk_730)]}, ks}),
        FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.look(Machine.Env.find(e_728, i_731)), Con{Fun.Fr{Code.F.Eval.go.k1(), [Fun.V.z{}, FM.Enc.nat(i_731), FM.Enc.term(Source.Term.Var{i_731}), FM.Enc.val(e_728), FM.Enc.frs(fs_729), FM.Enc.book(bk_730)]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.look(Machine.Env.find(e_728, i_731)), Con{Fun.Fr{Code.F.Eval.go.k1(), [Fun.V.z{}, FM.Enc.nat(i_731), FM.Enc.term(Source.Term.Var{i_731}), FM.Enc.val(e_728), FM.Enc.frs(fs_729), FM.Enc.book(bk_730)]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Eval.go(Source.Term.Var{i_731}, e_728, fs_729, bk_730)), ks}},
        FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.look(Machine.Env.find(e_728, i_731)), Con{Fun.Fr{Code.F.Eval.go.k1(), [Fun.V.z{}, FM.Enc.nat(i_731), FM.Enc.term(Source.Term.Var{i_731}), FM.Enc.val(e_728), FM.Enc.frs(fs_729), FM.Enc.book(bk_730)]}, ks}}}),
        Elim.Look(Machine.Env.find(e_728, i_731), m28 => Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Eval.go.k1(), [FM.Enc.look(m28), Fun.V.z{}, FM.Enc.nat(i_731), FM.Enc.term(Source.Term.Var{i_731}), FM.Enc.val(e_728), FM.Enc.frs(fs_729), FM.Enc.book(bk_730)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Eval.var(m28, fs_729)), ks}}),
        +x_733 => FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Eval.go.k1(), [FM.Enc.look(Machine.Look.val{x_733}), Fun.V.z{}, FM.Enc.nat(i_731), FM.Enc.term(Source.Term.Var{i_731}), FM.Enc.val(e_728), FM.Enc.frs(fs_729), FM.Enc.book(bk_730)], ks}}, Fun.F.iter(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Eval.go.k1(), [FM.Enc.look(Machine.Look.val{x_733}), Fun.V.z{}, FM.Enc.nat(i_731), FM.Enc.term(Source.Term.Var{i_731}), FM.Enc.val(e_728), FM.Enc.frs(fs_729), FM.Enc.book(bk_730)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Eval.var(Machine.Look.val{x_733}, fs_729)), ks}},
        FP.Reach.steps(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Eval.go.k1(), [FM.Enc.look(Machine.Look.val{x_733}), Fun.V.z{}, FM.Enc.nat(i_731), FM.Enc.term(Source.Term.Var{i_731}), FM.Enc.val(e_728), FM.Enc.frs(fs_729), FM.Enc.book(bk_730)], ks}}),
        L.Val.force(x_733, fs_729, ks)),
        +j_734 => (3n, {==})))))
    case Source.Term.Ref{+k_735}:
      FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Eval.go(), [FM.Enc.term(Source.Term.Ref{k_735}), FM.Enc.val(e_728), FM.Enc.frs(fs_729), FM.Enc.book(bk_730)], ks}}, Fun.F.iter(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Eval.go(), [FM.Enc.term(Source.Term.Ref{k_735}), FM.Enc.val(e_728), FM.Enc.frs(fs_729), FM.Enc.book(bk_730)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Eval.go(Source.Term.Ref{k_735}, e_728, fs_729, bk_730)), ks}},
        FP.Reach.steps(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Eval.go(), [FM.Enc.term(Source.Term.Ref{k_735}), FM.Enc.val(e_728), FM.Enc.frs(fs_729), FM.Enc.book(bk_730)], ks}}),
        L.Call.try(bk_730, k_735, Machine.Val.nil{}, fs_729, ks))
    case Source.Term.Ann{+x_736, +a_737}:
      (7n, {==})
    case Source.Term.Let{+q_738, +v_739, +f_740}:
      match q_738:
        case Source.Q0{}:
          (12n, {==})
        case Source.Q1{}:
          (13n, {==})
        case Source.Q2{}:
          (13n, {==})
    case Source.Term.Typ{+_q_741}:
      (14n, {==})
    case Source.Term.Min{+a_742, +b_743}:
      (14n, {==})
    case Source.Term.All{+_q_744, +_a_745, +_b_746}:
      (14n, {==})
    case Source.Term.Lam{+_q_747, +_f_748}:
      (14n, {==})
    case Source.Term.App{+q_749, +f_750, +x_751}:
      (14n, {==})
    case Source.Term.Sig{+_q_752, +_a_753, +_b_754}:
      (14n, {==})
    case Source.Term.Tup{+q_755, +a_756, +b_757}:
      match q_755:
        case Source.Q0{}:
          (14n, {==})
        case Source.Q1{}:
          (14n, {==})
        case Source.Q2{}:
          (14n, {==})
    case Source.Term.Prj{+_h_758}:
      (14n, {==})
    case Source.Term.Enu{+_ks_759}:
      (14n, {==})
    case Source.Term.Lab{+k_760}:
      (13n, {==})
    case Source.Term.Mat{+_k_761, +_h_762, +_m_763}:
      (14n, {==})
    case Source.Term.Efq{}:
      (14n, {==})
    case Source.Term.Eql{+_a_764, +_b_765, +_t_766}:
      (14n, {==})
    case Source.Term.Rfl{}:
      (13n, {==})
    case Source.Term.Rwt{+x_767, +p_768, +f_769}:
      (15n, {==})

def L.Name.is_quan(+n_770: List<&2, Nat>, +ks: List<&2, Fun.Fr>) ->
  Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Name.is_quan(), [FM.Enc.name(n_770)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_quan(n_770)), ks}}):
  FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Name.is_quan(), [FM.Enc.name(n_770)], ks}}, Fun.F.iter(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Name.is_quan(), [FM.Enc.name(n_770)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_quan(n_770)), ks}},
    FP.Reach.steps(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Name.is_quan(), [FM.Enc.name(n_770)], ks}}),
    FP.Reach.trans(Code.prog(), Fun.F.iter(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Name.is_quan(), [FM.Enc.name(n_770)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(n_770, Source.Name.of("Q0"))), Con{Fun.Fr{Code.F.Name.is_quan.k1(), [FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.name(n_770)]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_quan(n_770)), ks}},
    L.Name.is_eq(n_770, Source.Name.of("Q0"), Con{Fun.Fr{Code.F.Name.is_quan.k1(), [FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.name(n_770)]}, ks}),
    FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(n_770, Source.Name.of("Q0"))), Con{Fun.Fr{Code.F.Name.is_quan.k1(), [FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.name(n_770)]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(n_770, Source.Name.of("Q0"))), Con{Fun.Fr{Code.F.Name.is_quan.k1(), [FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.name(n_770)]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_quan(n_770)), ks}},
    FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(n_770, Source.Name.of("Q0"))), Con{Fun.Fr{Code.F.Name.is_quan.k1(), [FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.name(n_770)]}, ks}}}),
    Elim.Bool(Source.Name.is_eq(n_770, Source.Name.of("Q0")), m29 => Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Name.is_quan.k1(), [FM.Enc.bool(m29), FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.name(n_770)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(m29 || Source.Name.is_eq(n_770, Source.Name.of("Q1")) || Source.Name.is_eq(n_770, Source.Name.of("Q2"))), ks}}),
    FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Name.is_quan.k1(), [FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.name(n_770)], ks}}, Fun.F.iter(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Name.is_quan.k1(), [FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.name(n_770)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(False{} || Source.Name.is_eq(n_770, Source.Name.of("Q1")) || Source.Name.is_eq(n_770, Source.Name.of("Q2"))), ks}},
    FP.Reach.steps(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Name.is_quan.k1(), [FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.name(n_770)], ks}}),
    FP.Reach.trans(Code.prog(), Fun.F.iter(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Name.is_quan.k1(), [FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.name(n_770)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(n_770, Source.Name.of("Q1"))), Con{Fun.Fr{Code.F.Name.is_quan.k2(), [FM.Enc.name(Source.Name.of("Q1")), FM.Enc.name(Source.Name.of("1")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.name(n_770)]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(False{} || Source.Name.is_eq(n_770, Source.Name.of("Q1")) || Source.Name.is_eq(n_770, Source.Name.of("Q2"))), ks}},
    L.Name.is_eq(n_770, Source.Name.of("Q1"), Con{Fun.Fr{Code.F.Name.is_quan.k2(), [FM.Enc.name(Source.Name.of("Q1")), FM.Enc.name(Source.Name.of("1")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.name(n_770)]}, ks}),
    FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(n_770, Source.Name.of("Q1"))), Con{Fun.Fr{Code.F.Name.is_quan.k2(), [FM.Enc.name(Source.Name.of("Q1")), FM.Enc.name(Source.Name.of("1")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.name(n_770)]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(n_770, Source.Name.of("Q1"))), Con{Fun.Fr{Code.F.Name.is_quan.k2(), [FM.Enc.name(Source.Name.of("Q1")), FM.Enc.name(Source.Name.of("1")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.name(n_770)]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(False{} || Source.Name.is_eq(n_770, Source.Name.of("Q1")) || Source.Name.is_eq(n_770, Source.Name.of("Q2"))), ks}},
    FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(n_770, Source.Name.of("Q1"))), Con{Fun.Fr{Code.F.Name.is_quan.k2(), [FM.Enc.name(Source.Name.of("Q1")), FM.Enc.name(Source.Name.of("1")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.name(n_770)]}, ks}}}),
    Elim.Bool(Source.Name.is_eq(n_770, Source.Name.of("Q1")), m30 => Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Name.is_quan.k2(), [FM.Enc.bool(m30), FM.Enc.name(Source.Name.of("Q1")), FM.Enc.name(Source.Name.of("1")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.name(n_770)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(False{} || m30 || Source.Name.is_eq(n_770, Source.Name.of("Q2"))), ks}}),
    FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Name.is_quan.k2(), [FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q1")), FM.Enc.name(Source.Name.of("1")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.name(n_770)], ks}}, Fun.F.iter(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Name.is_quan.k2(), [FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q1")), FM.Enc.name(Source.Name.of("1")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.name(n_770)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(False{} || False{} || Source.Name.is_eq(n_770, Source.Name.of("Q2"))), ks}},
    FP.Reach.steps(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Name.is_quan.k2(), [FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q1")), FM.Enc.name(Source.Name.of("1")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.name(n_770)], ks}}),
    L.Name.is_eq(n_770, Source.Name.of("Q2"), ks)),
    (2n, {==}))))),
    (2n, {==})))))

def L.Term.qmin(+i_773: List<&2, Nat>, +j_774: List<&2, Nat>, +ks: List<&2, Fun.Fr>) ->
  Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Term.qmin(), [FM.Enc.name(i_773), FM.Enc.name(j_774)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.term(Source.Term.qmin(i_773, j_774)), ks}}):
  FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Term.qmin(), [FM.Enc.name(i_773), FM.Enc.name(j_774)], ks}}, Fun.F.iter(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Term.qmin(), [FM.Enc.name(i_773), FM.Enc.name(j_774)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.term(Source.Term.qmin(i_773, j_774)), ks}},
    FP.Reach.steps(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Term.qmin(), [FM.Enc.name(i_773), FM.Enc.name(j_774)], ks}}),
    FP.Reach.trans(Code.prog(), Fun.F.iter(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Term.qmin(), [FM.Enc.name(i_773), FM.Enc.name(j_774)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(i_773, Source.Name.of("Q2"))), Con{Fun.Fr{Code.F.Term.qmin.k1(), [FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.term(Source.Term.qmin(i_773, j_774)), ks}},
    L.Name.is_eq(i_773, Source.Name.of("Q2"), Con{Fun.Fr{Code.F.Term.qmin.k1(), [FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)]}, ks}),
    FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(i_773, Source.Name.of("Q2"))), Con{Fun.Fr{Code.F.Term.qmin.k1(), [FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(i_773, Source.Name.of("Q2"))), Con{Fun.Fr{Code.F.Term.qmin.k1(), [FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.term(Source.Term.qmin(i_773, j_774)), ks}},
    FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(i_773, Source.Name.of("Q2"))), Con{Fun.Fr{Code.F.Term.qmin.k1(), [FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)]}, ks}}}),
    Elim.Bool(Source.Name.is_eq(i_773, Source.Name.of("Q2")), m31 => Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Term.qmin.k1(), [FM.Enc.bool(m31), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.term(Source.Bool.if(Source.Term, m31, Source.Term.Lab{j_774}, Source.Bool.if(Source.Term, Source.Name.is_eq(j_774, Source.Name.of("Q2")), Source.Term.Lab{i_773}, Source.Bool.if(Source.Term, Source.Name.is_eq(i_773, Source.Name.of("Q0")) || Source.Name.is_eq(j_774, Source.Name.of("Q0")), Source.Term.Lab{Source.Name.of("Q0")}, Source.Term.Lab{Source.Name.of("Q1")})))), ks}}),
    FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Term.qmin.k1(), [FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)], ks}}, Fun.F.iter(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Term.qmin.k1(), [FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.term(Source.Bool.if(Source.Term, False{}, Source.Term.Lab{j_774}, Source.Bool.if(Source.Term, Source.Name.is_eq(j_774, Source.Name.of("Q2")), Source.Term.Lab{i_773}, Source.Bool.if(Source.Term, Source.Name.is_eq(i_773, Source.Name.of("Q0")) || Source.Name.is_eq(j_774, Source.Name.of("Q0")), Source.Term.Lab{Source.Name.of("Q0")}, Source.Term.Lab{Source.Name.of("Q1")})))), ks}},
    FP.Reach.steps(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Term.qmin.k1(), [FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)], ks}}),
    FP.Reach.trans(Code.prog(), Fun.F.iter(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Term.qmin.k1(), [FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(j_774, Source.Name.of("Q2"))), Con{Fun.Fr{Code.F.Term.qmin.k2(), [FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.term(Source.Bool.if(Source.Term, False{}, Source.Term.Lab{j_774}, Source.Bool.if(Source.Term, Source.Name.is_eq(j_774, Source.Name.of("Q2")), Source.Term.Lab{i_773}, Source.Bool.if(Source.Term, Source.Name.is_eq(i_773, Source.Name.of("Q0")) || Source.Name.is_eq(j_774, Source.Name.of("Q0")), Source.Term.Lab{Source.Name.of("Q0")}, Source.Term.Lab{Source.Name.of("Q1")})))), ks}},
    L.Name.is_eq(j_774, Source.Name.of("Q2"), Con{Fun.Fr{Code.F.Term.qmin.k2(), [FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)]}, ks}),
    FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(j_774, Source.Name.of("Q2"))), Con{Fun.Fr{Code.F.Term.qmin.k2(), [FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(j_774, Source.Name.of("Q2"))), Con{Fun.Fr{Code.F.Term.qmin.k2(), [FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.term(Source.Bool.if(Source.Term, False{}, Source.Term.Lab{j_774}, Source.Bool.if(Source.Term, Source.Name.is_eq(j_774, Source.Name.of("Q2")), Source.Term.Lab{i_773}, Source.Bool.if(Source.Term, Source.Name.is_eq(i_773, Source.Name.of("Q0")) || Source.Name.is_eq(j_774, Source.Name.of("Q0")), Source.Term.Lab{Source.Name.of("Q0")}, Source.Term.Lab{Source.Name.of("Q1")})))), ks}},
    FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(j_774, Source.Name.of("Q2"))), Con{Fun.Fr{Code.F.Term.qmin.k2(), [FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)]}, ks}}}),
    Elim.Bool(Source.Name.is_eq(j_774, Source.Name.of("Q2")), m32 => Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Term.qmin.k2(), [FM.Enc.bool(m32), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.term(Source.Bool.if(Source.Term, m32, Source.Term.Lab{i_773}, Source.Bool.if(Source.Term, Source.Name.is_eq(i_773, Source.Name.of("Q0")) || Source.Name.is_eq(j_774, Source.Name.of("Q0")), Source.Term.Lab{Source.Name.of("Q0")}, Source.Term.Lab{Source.Name.of("Q1")}))), ks}}),
    FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Term.qmin.k2(), [FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)], ks}}, Fun.F.iter(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Term.qmin.k2(), [FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.term(Source.Bool.if(Source.Term, False{}, Source.Term.Lab{i_773}, Source.Bool.if(Source.Term, Source.Name.is_eq(i_773, Source.Name.of("Q0")) || Source.Name.is_eq(j_774, Source.Name.of("Q0")), Source.Term.Lab{Source.Name.of("Q0")}, Source.Term.Lab{Source.Name.of("Q1")}))), ks}},
    FP.Reach.steps(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Term.qmin.k2(), [FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)], ks}}),
    FP.Reach.trans(Code.prog(), Fun.F.iter(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Term.qmin.k2(), [FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(i_773, Source.Name.of("Q0"))), Con{Fun.Fr{Code.F.Term.qmin.k3(), [FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.term(Source.Bool.if(Source.Term, False{}, Source.Term.Lab{i_773}, Source.Bool.if(Source.Term, Source.Name.is_eq(i_773, Source.Name.of("Q0")) || Source.Name.is_eq(j_774, Source.Name.of("Q0")), Source.Term.Lab{Source.Name.of("Q0")}, Source.Term.Lab{Source.Name.of("Q1")}))), ks}},
    L.Name.is_eq(i_773, Source.Name.of("Q0"), Con{Fun.Fr{Code.F.Term.qmin.k3(), [FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)]}, ks}),
    FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(i_773, Source.Name.of("Q0"))), Con{Fun.Fr{Code.F.Term.qmin.k3(), [FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(i_773, Source.Name.of("Q0"))), Con{Fun.Fr{Code.F.Term.qmin.k3(), [FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.term(Source.Bool.if(Source.Term, False{}, Source.Term.Lab{i_773}, Source.Bool.if(Source.Term, Source.Name.is_eq(i_773, Source.Name.of("Q0")) || Source.Name.is_eq(j_774, Source.Name.of("Q0")), Source.Term.Lab{Source.Name.of("Q0")}, Source.Term.Lab{Source.Name.of("Q1")}))), ks}},
    FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(i_773, Source.Name.of("Q0"))), Con{Fun.Fr{Code.F.Term.qmin.k3(), [FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)]}, ks}}}),
    Elim.Bool(Source.Name.is_eq(i_773, Source.Name.of("Q0")), m33 => Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Term.qmin.k3(), [FM.Enc.bool(m33), FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.term(Source.Bool.if(Source.Term, m33 || Source.Name.is_eq(j_774, Source.Name.of("Q0")), Source.Term.Lab{Source.Name.of("Q0")}, Source.Term.Lab{Source.Name.of("Q1")})), ks}}),
    FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Term.qmin.k3(), [FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)], ks}}, Fun.F.iter(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Term.qmin.k3(), [FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.term(Source.Bool.if(Source.Term, False{} || Source.Name.is_eq(j_774, Source.Name.of("Q0")), Source.Term.Lab{Source.Name.of("Q0")}, Source.Term.Lab{Source.Name.of("Q1")})), ks}},
    FP.Reach.steps(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Term.qmin.k3(), [FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)], ks}}),
    FP.Reach.trans(Code.prog(), Fun.F.iter(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Term.qmin.k3(), [FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(j_774, Source.Name.of("Q0"))), Con{Fun.Fr{Code.F.Term.qmin.k4(), [FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.term(Source.Bool.if(Source.Term, False{} || Source.Name.is_eq(j_774, Source.Name.of("Q0")), Source.Term.Lab{Source.Name.of("Q0")}, Source.Term.Lab{Source.Name.of("Q1")})), ks}},
    L.Name.is_eq(j_774, Source.Name.of("Q0"), Con{Fun.Fr{Code.F.Term.qmin.k4(), [FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)]}, ks}),
    FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(j_774, Source.Name.of("Q0"))), Con{Fun.Fr{Code.F.Term.qmin.k4(), [FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(j_774, Source.Name.of("Q0"))), Con{Fun.Fr{Code.F.Term.qmin.k4(), [FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.term(Source.Bool.if(Source.Term, False{} || Source.Name.is_eq(j_774, Source.Name.of("Q0")), Source.Term.Lab{Source.Name.of("Q0")}, Source.Term.Lab{Source.Name.of("Q1")})), ks}},
    FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(j_774, Source.Name.of("Q0"))), Con{Fun.Fr{Code.F.Term.qmin.k4(), [FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)]}, ks}}}),
    Elim.Bool(Source.Name.is_eq(j_774, Source.Name.of("Q0")), m34 => Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Term.qmin.k4(), [FM.Enc.bool(m34), FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.term(Source.Bool.if(Source.Term, False{} || m34, Source.Term.Lab{Source.Name.of("Q0")}, Source.Term.Lab{Source.Name.of("Q1")})), ks}}),
    (5n, {==}),
    (5n, {==}))))),
    (5n, {==}))))),
    (3n, {==}))))),
    (3n, {==})))))

def L.Ret.meet(+a_779: Machine.Val, +b_780: Machine.Val, +fs_781: List<&2, Machine.Fr>, +ks: List<&2, Fun.Fr>) ->
  Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ret.meet(), [FM.Enc.val(a_779), FM.Enc.val(b_780), FM.Enc.frs(fs_781)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Ret.meet(a_779, b_780, fs_781)), ks}}):
  match a_779:
    case Machine.Val.nil{}:
      (2n, {==})
    case Machine.Val.env{+_x_782, +_rest_783}:
      (2n, {==})
    case Machine.Val.arg{+_q_784, +_x_785, +_rest_786}:
      (2n, {==})
    case Machine.Val.clo{+_t_787, +_e_788}:
      (2n, {==})
    case Machine.Val.lab{+i_789}:
      match b_780:
        case Machine.Val.nil{}:
          (3n, {==})
        case Machine.Val.env{+_x_790, +_rest_791}:
          (3n, {==})
        case Machine.Val.arg{+_q_792, +_x_793, +_rest_794}:
          (3n, {==})
        case Machine.Val.clo{+_t_795, +_e_796}:
          (3n, {==})
        case Machine.Val.lab{+j_797}:
          FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ret.meet(), [FM.Enc.val(Machine.Val.lab{i_789}), FM.Enc.val(Machine.Val.lab{j_797}), FM.Enc.frs(fs_781)], ks}}, Fun.F.iter(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ret.meet(), [FM.Enc.val(Machine.Val.lab{i_789}), FM.Enc.val(Machine.Val.lab{j_797}), FM.Enc.frs(fs_781)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Ret.meet(Machine.Val.lab{i_789}, Machine.Val.lab{j_797}, fs_781)), ks}},
            FP.Reach.steps(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ret.meet(), [FM.Enc.val(Machine.Val.lab{i_789}), FM.Enc.val(Machine.Val.lab{j_797}), FM.Enc.frs(fs_781)], ks}}),
            FP.Reach.trans(Code.prog(), Fun.F.iter(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ret.meet(), [FM.Enc.val(Machine.Val.lab{i_789}), FM.Enc.val(Machine.Val.lab{j_797}), FM.Enc.frs(fs_781)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_quan(i_789)), Con{Fun.Fr{Code.F.Ret.meet.k1(), [Fun.V.z{}, FM.Enc.name(j_797), Fun.V.z{}, FM.Enc.name(i_789), FM.Enc.val(Machine.Val.lab{i_789}), FM.Enc.val(Machine.Val.lab{j_797}), FM.Enc.frs(fs_781)]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Ret.meet(Machine.Val.lab{i_789}, Machine.Val.lab{j_797}, fs_781)), ks}},
            L.Name.is_quan(i_789, Con{Fun.Fr{Code.F.Ret.meet.k1(), [Fun.V.z{}, FM.Enc.name(j_797), Fun.V.z{}, FM.Enc.name(i_789), FM.Enc.val(Machine.Val.lab{i_789}), FM.Enc.val(Machine.Val.lab{j_797}), FM.Enc.frs(fs_781)]}, ks}),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_quan(i_789)), Con{Fun.Fr{Code.F.Ret.meet.k1(), [Fun.V.z{}, FM.Enc.name(j_797), Fun.V.z{}, FM.Enc.name(i_789), FM.Enc.val(Machine.Val.lab{i_789}), FM.Enc.val(Machine.Val.lab{j_797}), FM.Enc.frs(fs_781)]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_quan(i_789)), Con{Fun.Fr{Code.F.Ret.meet.k1(), [Fun.V.z{}, FM.Enc.name(j_797), Fun.V.z{}, FM.Enc.name(i_789), FM.Enc.val(Machine.Val.lab{i_789}), FM.Enc.val(Machine.Val.lab{j_797}), FM.Enc.frs(fs_781)]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Ret.meet(Machine.Val.lab{i_789}, Machine.Val.lab{j_797}, fs_781)), ks}},
            FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_quan(i_789)), Con{Fun.Fr{Code.F.Ret.meet.k1(), [Fun.V.z{}, FM.Enc.name(j_797), Fun.V.z{}, FM.Enc.name(i_789), FM.Enc.val(Machine.Val.lab{i_789}), FM.Enc.val(Machine.Val.lab{j_797}), FM.Enc.frs(fs_781)]}, ks}}}),
            Elim.Bool(Source.Name.is_quan(i_789), m35 => Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ret.meet.k1(), [FM.Enc.bool(m35), Fun.V.z{}, FM.Enc.name(j_797), Fun.V.z{}, FM.Enc.name(i_789), FM.Enc.val(Machine.Val.lab{i_789}), FM.Enc.val(Machine.Val.lab{j_797}), FM.Enc.frs(fs_781)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.move(Source.Bool.lazy(Machine.Move, m35 && Source.Name.is_quan(j_797), u => Machine.Move.go{Machine.St.eval{Source.Term.qmin(i_789, j_797), Machine.Val.nil{}, fs_781}}, u => Machine.Move.stuck{})), ks}}),
            (2n, {==}),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ret.meet.k1(), [FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(j_797), Fun.V.z{}, FM.Enc.name(i_789), FM.Enc.val(Machine.Val.lab{i_789}), FM.Enc.val(Machine.Val.lab{j_797}), FM.Enc.frs(fs_781)], ks}}, Fun.F.iter(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ret.meet.k1(), [FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(j_797), Fun.V.z{}, FM.Enc.name(i_789), FM.Enc.val(Machine.Val.lab{i_789}), FM.Enc.val(Machine.Val.lab{j_797}), FM.Enc.frs(fs_781)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.move(Source.Bool.lazy(Machine.Move, True{} && Source.Name.is_quan(j_797), u => Machine.Move.go{Machine.St.eval{Source.Term.qmin(i_789, j_797), Machine.Val.nil{}, fs_781}}, u => Machine.Move.stuck{})), ks}},
            FP.Reach.steps(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ret.meet.k1(), [FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(j_797), Fun.V.z{}, FM.Enc.name(i_789), FM.Enc.val(Machine.Val.lab{i_789}), FM.Enc.val(Machine.Val.lab{j_797}), FM.Enc.frs(fs_781)], ks}}),
            FP.Reach.trans(Code.prog(), Fun.F.iter(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ret.meet.k1(), [FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(j_797), Fun.V.z{}, FM.Enc.name(i_789), FM.Enc.val(Machine.Val.lab{i_789}), FM.Enc.val(Machine.Val.lab{j_797}), FM.Enc.frs(fs_781)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_quan(j_797)), Con{Fun.Fr{Code.F.Ret.meet.k2(), [Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(j_797), Fun.V.z{}, FM.Enc.name(i_789), FM.Enc.val(Machine.Val.lab{i_789}), FM.Enc.val(Machine.Val.lab{j_797}), FM.Enc.frs(fs_781)]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.move(Source.Bool.lazy(Machine.Move, True{} && Source.Name.is_quan(j_797), u => Machine.Move.go{Machine.St.eval{Source.Term.qmin(i_789, j_797), Machine.Val.nil{}, fs_781}}, u => Machine.Move.stuck{})), ks}},
            L.Name.is_quan(j_797, Con{Fun.Fr{Code.F.Ret.meet.k2(), [Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(j_797), Fun.V.z{}, FM.Enc.name(i_789), FM.Enc.val(Machine.Val.lab{i_789}), FM.Enc.val(Machine.Val.lab{j_797}), FM.Enc.frs(fs_781)]}, ks}),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_quan(j_797)), Con{Fun.Fr{Code.F.Ret.meet.k2(), [Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(j_797), Fun.V.z{}, FM.Enc.name(i_789), FM.Enc.val(Machine.Val.lab{i_789}), FM.Enc.val(Machine.Val.lab{j_797}), FM.Enc.frs(fs_781)]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_quan(j_797)), Con{Fun.Fr{Code.F.Ret.meet.k2(), [Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(j_797), Fun.V.z{}, FM.Enc.name(i_789), FM.Enc.val(Machine.Val.lab{i_789}), FM.Enc.val(Machine.Val.lab{j_797}), FM.Enc.frs(fs_781)]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.move(Source.Bool.lazy(Machine.Move, True{} && Source.Name.is_quan(j_797), u => Machine.Move.go{Machine.St.eval{Source.Term.qmin(i_789, j_797), Machine.Val.nil{}, fs_781}}, u => Machine.Move.stuck{})), ks}},
            FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_quan(j_797)), Con{Fun.Fr{Code.F.Ret.meet.k2(), [Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(j_797), Fun.V.z{}, FM.Enc.name(i_789), FM.Enc.val(Machine.Val.lab{i_789}), FM.Enc.val(Machine.Val.lab{j_797}), FM.Enc.frs(fs_781)]}, ks}}}),
            Elim.Bool(Source.Name.is_quan(j_797), m36 => Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ret.meet.k2(), [FM.Enc.bool(m36), Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(j_797), Fun.V.z{}, FM.Enc.name(i_789), FM.Enc.val(Machine.Val.lab{i_789}), FM.Enc.val(Machine.Val.lab{j_797}), FM.Enc.frs(fs_781)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.move(Source.Bool.lazy(Machine.Move, m36, u => Machine.Move.go{Machine.St.eval{Source.Term.qmin(i_789, j_797), Machine.Val.nil{}, fs_781}}, u => Machine.Move.stuck{})), ks}}),
            (2n, {==}),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ret.meet.k2(), [FM.Enc.bool(True{}), Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(j_797), Fun.V.z{}, FM.Enc.name(i_789), FM.Enc.val(Machine.Val.lab{i_789}), FM.Enc.val(Machine.Val.lab{j_797}), FM.Enc.frs(fs_781)], ks}}, Fun.F.iter(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ret.meet.k2(), [FM.Enc.bool(True{}), Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(j_797), Fun.V.z{}, FM.Enc.name(i_789), FM.Enc.val(Machine.Val.lab{i_789}), FM.Enc.val(Machine.Val.lab{j_797}), FM.Enc.frs(fs_781)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.move(Source.Bool.lazy(Machine.Move, True{}, u => Machine.Move.go{Machine.St.eval{Source.Term.qmin(i_789, j_797), Machine.Val.nil{}, fs_781}}, u => Machine.Move.stuck{})), ks}},
            FP.Reach.steps(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ret.meet.k2(), [FM.Enc.bool(True{}), Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(j_797), Fun.V.z{}, FM.Enc.name(i_789), FM.Enc.val(Machine.Val.lab{i_789}), FM.Enc.val(Machine.Val.lab{j_797}), FM.Enc.frs(fs_781)], ks}}),
            FP.Reach.trans(Code.prog(), Fun.F.iter(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ret.meet.k2(), [FM.Enc.bool(True{}), Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(j_797), Fun.V.z{}, FM.Enc.name(i_789), FM.Enc.val(Machine.Val.lab{i_789}), FM.Enc.val(Machine.Val.lab{j_797}), FM.Enc.frs(fs_781)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.term(Source.Term.qmin(i_789, j_797)), Con{Fun.Fr{Code.F.Ret.meet.k3(), [Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(j_797), Fun.V.z{}, FM.Enc.name(i_789), FM.Enc.val(Machine.Val.lab{i_789}), FM.Enc.val(Machine.Val.lab{j_797}), FM.Enc.frs(fs_781)]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.move(Source.Bool.lazy(Machine.Move, True{}, u => Machine.Move.go{Machine.St.eval{Source.Term.qmin(i_789, j_797), Machine.Val.nil{}, fs_781}}, u => Machine.Move.stuck{})), ks}},
            L.Term.qmin(i_789, j_797, Con{Fun.Fr{Code.F.Ret.meet.k3(), [Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(j_797), Fun.V.z{}, FM.Enc.name(i_789), FM.Enc.val(Machine.Val.lab{i_789}), FM.Enc.val(Machine.Val.lab{j_797}), FM.Enc.frs(fs_781)]}, ks}),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.term(Source.Term.qmin(i_789, j_797)), Con{Fun.Fr{Code.F.Ret.meet.k3(), [Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(j_797), Fun.V.z{}, FM.Enc.name(i_789), FM.Enc.val(Machine.Val.lab{i_789}), FM.Enc.val(Machine.Val.lab{j_797}), FM.Enc.frs(fs_781)]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.term(Source.Term.qmin(i_789, j_797)), Con{Fun.Fr{Code.F.Ret.meet.k3(), [Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(j_797), Fun.V.z{}, FM.Enc.name(i_789), FM.Enc.val(Machine.Val.lab{i_789}), FM.Enc.val(Machine.Val.lab{j_797}), FM.Enc.frs(fs_781)]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.move(Source.Bool.lazy(Machine.Move, True{}, u => Machine.Move.go{Machine.St.eval{Source.Term.qmin(i_789, j_797), Machine.Val.nil{}, fs_781}}, u => Machine.Move.stuck{})), ks}},
            FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.term(Source.Term.qmin(i_789, j_797)), Con{Fun.Fr{Code.F.Ret.meet.k3(), [Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(j_797), Fun.V.z{}, FM.Enc.name(i_789), FM.Enc.val(Machine.Val.lab{i_789}), FM.Enc.val(Machine.Val.lab{j_797}), FM.Enc.frs(fs_781)]}, ks}}}),
            (4n, {==}))))))))))))
        case Machine.Val.rfl{}:
          (3n, {==})
        case Machine.Val.tup{+_q_801, +_a_802, +_b_803}:
          (3n, {==})
        case Machine.Val.call{+_k_804, +_xs_805}:
          (3n, {==})
    case Machine.Val.rfl{}:
      (2n, {==})
    case Machine.Val.tup{+_q_806, +_a_807, +_b_808}:
      (2n, {==})
    case Machine.Val.call{+_k_809, +_xs_810}:
      (2n, {==})

def L.Ret.frame(+fr_811: Machine.Fr, +v_812: Machine.Val, +fs_813: List<&2, Machine.Fr>, +bk_814: List<&2, Source.Def>, +ks: List<&2, Fun.Fr>) ->
  Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ret.frame(), [FM.Enc.fr(fr_811), FM.Enc.val(v_812), FM.Enc.frs(fs_813), FM.Enc.book(bk_814)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Ret.frame(fr_811, v_812, fs_813, bk_814)), ks}}):
  match fr_811:
    case Machine.Fr.arg{+q_815, +x_816}:
      match q_815:
        case Source.Q0{}:
          FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ret.frame(), [FM.Enc.fr(Machine.Fr.arg{Source.Q0{}, x_816}), FM.Enc.val(v_812), FM.Enc.frs(fs_813), FM.Enc.book(bk_814)], ks}}, Fun.F.iter(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ret.frame(), [FM.Enc.fr(Machine.Fr.arg{Source.Q0{}, x_816}), FM.Enc.val(v_812), FM.Enc.frs(fs_813), FM.Enc.book(bk_814)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Ret.frame(Machine.Fr.arg{Source.Q0{}, x_816}, v_812, fs_813, bk_814)), ks}},
            FP.Reach.steps(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ret.frame(), [FM.Enc.fr(Machine.Fr.arg{Source.Q0{}, x_816}), FM.Enc.val(v_812), FM.Enc.frs(fs_813), FM.Enc.book(bk_814)], ks}}),
            L.Apply.go(v_812, Source.Q0{}, x_816, bk_814, fs_813, ks))
        case Source.Q1{}:
          FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ret.frame(), [FM.Enc.fr(Machine.Fr.arg{Source.Q1{}, x_816}), FM.Enc.val(v_812), FM.Enc.frs(fs_813), FM.Enc.book(bk_814)], ks}}, Fun.F.iter(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ret.frame(), [FM.Enc.fr(Machine.Fr.arg{Source.Q1{}, x_816}), FM.Enc.val(v_812), FM.Enc.frs(fs_813), FM.Enc.book(bk_814)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Ret.frame(Machine.Fr.arg{Source.Q1{}, x_816}, v_812, fs_813, bk_814)), ks}},
            FP.Reach.steps(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ret.frame(), [FM.Enc.fr(Machine.Fr.arg{Source.Q1{}, x_816}), FM.Enc.val(v_812), FM.Enc.frs(fs_813), FM.Enc.book(bk_814)], ks}}),
            L.Val.force(x_816, Con{Machine.Fr.fun{Source.Q1{}, v_812}, fs_813}, ks))
        case Source.Q2{}:
          FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ret.frame(), [FM.Enc.fr(Machine.Fr.arg{Source.Q2{}, x_816}), FM.Enc.val(v_812), FM.Enc.frs(fs_813), FM.Enc.book(bk_814)], ks}}, Fun.F.iter(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ret.frame(), [FM.Enc.fr(Machine.Fr.arg{Source.Q2{}, x_816}), FM.Enc.val(v_812), FM.Enc.frs(fs_813), FM.Enc.book(bk_814)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Ret.frame(Machine.Fr.arg{Source.Q2{}, x_816}, v_812, fs_813, bk_814)), ks}},
            FP.Reach.steps(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ret.frame(), [FM.Enc.fr(Machine.Fr.arg{Source.Q2{}, x_816}), FM.Enc.val(v_812), FM.Enc.frs(fs_813), FM.Enc.book(bk_814)], ks}}),
            L.Val.force(x_816, Con{Machine.Fr.fun{Source.Q2{}, v_812}, fs_813}, ks))
    case Machine.Fr.fun{+q_817, +f_818}:
      FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ret.frame(), [FM.Enc.fr(Machine.Fr.fun{q_817, f_818}), FM.Enc.val(v_812), FM.Enc.frs(fs_813), FM.Enc.book(bk_814)], ks}}, Fun.F.iter(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ret.frame(), [FM.Enc.fr(Machine.Fr.fun{q_817, f_818}), FM.Enc.val(v_812), FM.Enc.frs(fs_813), FM.Enc.book(bk_814)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Ret.frame(Machine.Fr.fun{q_817, f_818}, v_812, fs_813, bk_814)), ks}},
        FP.Reach.steps(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ret.frame(), [FM.Enc.fr(Machine.Fr.fun{q_817, f_818}), FM.Enc.val(v_812), FM.Enc.frs(fs_813), FM.Enc.book(bk_814)], ks}}),
        L.Apply.go(f_818, q_817, v_812, bk_814, fs_813, ks))
    case Machine.Fr.let{+q_819, +f_820, +e_821}:
      match q_819:
        case Source.Q0{}:
          (10n, {==})
        case Source.Q1{}:
          (10n, {==})
        case Source.Q2{}:
          FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ret.frame(), [FM.Enc.fr(Machine.Fr.let{Source.Q2{}, f_820, e_821}), FM.Enc.val(v_812), FM.Enc.frs(fs_813), FM.Enc.book(bk_814)], ks}}, Fun.F.iter(6n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ret.frame(), [FM.Enc.fr(Machine.Fr.let{Source.Q2{}, f_820, e_821}), FM.Enc.val(v_812), FM.Enc.frs(fs_813), FM.Enc.book(bk_814)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Ret.frame(Machine.Fr.let{Source.Q2{}, f_820, e_821}, v_812, fs_813, bk_814)), ks}},
            FP.Reach.steps(6n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ret.frame(), [FM.Enc.fr(Machine.Fr.let{Source.Q2{}, f_820, e_821}), FM.Enc.val(v_812), FM.Enc.frs(fs_813), FM.Enc.book(bk_814)], ks}}),
            FP.Reach.trans(Code.prog(), Fun.F.iter(6n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ret.frame(), [FM.Enc.fr(Machine.Fr.let{Source.Q2{}, f_820, e_821}), FM.Enc.val(v_812), FM.Enc.frs(fs_813), FM.Enc.book(bk_814)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.is_data(v_812)), Con{Fun.Fr{Code.F.Ret.frame.k1(), [Fun.V.z{}, Fun.V.z{}, FM.Enc.val(e_821), FM.Enc.term(f_820), FM.Enc.p(FM.Enc.term(f_820), FM.Enc.val(e_821)), FM.Enc.quan(Source.Q2{}), FM.Enc.fr(Machine.Fr.let{Source.Q2{}, f_820, e_821}), FM.Enc.val(v_812), FM.Enc.frs(fs_813), FM.Enc.book(bk_814)]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Ret.frame(Machine.Fr.let{Source.Q2{}, f_820, e_821}, v_812, fs_813, bk_814)), ks}},
            L.Val.is_data(v_812, Con{Fun.Fr{Code.F.Ret.frame.k1(), [Fun.V.z{}, Fun.V.z{}, FM.Enc.val(e_821), FM.Enc.term(f_820), FM.Enc.p(FM.Enc.term(f_820), FM.Enc.val(e_821)), FM.Enc.quan(Source.Q2{}), FM.Enc.fr(Machine.Fr.let{Source.Q2{}, f_820, e_821}), FM.Enc.val(v_812), FM.Enc.frs(fs_813), FM.Enc.book(bk_814)]}, ks}),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.is_data(v_812)), Con{Fun.Fr{Code.F.Ret.frame.k1(), [Fun.V.z{}, Fun.V.z{}, FM.Enc.val(e_821), FM.Enc.term(f_820), FM.Enc.p(FM.Enc.term(f_820), FM.Enc.val(e_821)), FM.Enc.quan(Source.Q2{}), FM.Enc.fr(Machine.Fr.let{Source.Q2{}, f_820, e_821}), FM.Enc.val(v_812), FM.Enc.frs(fs_813), FM.Enc.book(bk_814)]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.is_data(v_812)), Con{Fun.Fr{Code.F.Ret.frame.k1(), [Fun.V.z{}, Fun.V.z{}, FM.Enc.val(e_821), FM.Enc.term(f_820), FM.Enc.p(FM.Enc.term(f_820), FM.Enc.val(e_821)), FM.Enc.quan(Source.Q2{}), FM.Enc.fr(Machine.Fr.let{Source.Q2{}, f_820, e_821}), FM.Enc.val(v_812), FM.Enc.frs(fs_813), FM.Enc.book(bk_814)]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Ret.frame(Machine.Fr.let{Source.Q2{}, f_820, e_821}, v_812, fs_813, bk_814)), ks}},
            FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.is_data(v_812)), Con{Fun.Fr{Code.F.Ret.frame.k1(), [Fun.V.z{}, Fun.V.z{}, FM.Enc.val(e_821), FM.Enc.term(f_820), FM.Enc.p(FM.Enc.term(f_820), FM.Enc.val(e_821)), FM.Enc.quan(Source.Q2{}), FM.Enc.fr(Machine.Fr.let{Source.Q2{}, f_820, e_821}), FM.Enc.val(v_812), FM.Enc.frs(fs_813), FM.Enc.book(bk_814)]}, ks}}}),
            Elim.Bool(Machine.Val.is_data(v_812), m37 => Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ret.frame.k1(), [FM.Enc.bool(m37), Fun.V.z{}, Fun.V.z{}, FM.Enc.val(e_821), FM.Enc.term(f_820), FM.Enc.p(FM.Enc.term(f_820), FM.Enc.val(e_821)), FM.Enc.quan(Source.Q2{}), FM.Enc.fr(Machine.Fr.let{Source.Q2{}, f_820, e_821}), FM.Enc.val(v_812), FM.Enc.frs(fs_813), FM.Enc.book(bk_814)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.move(Source.Bool.lazy(Machine.Move, Bool.not(Source.Quan.is_q2(Source.Q2{})) || m37, u => Machine.Move.go{Machine.St.eval{f_820, Machine.Val.env{v_812, e_821}, fs_813}}, u => Machine.Move.stuck{})), ks}}),
            (2n, {==}),
            (6n, {==})))))
    case Machine.Fr.fst{+q_823, +b_824, +e_825}:
      (11n, {==})
    case Machine.Fr.snd{+q_826, +a_827}:
      (10n, {==})
    case Machine.Fr.rwt{+p_828, +f_829, +e_830}:
      match v_812:
        case Machine.Val.nil{}:
          (9n, {==})
        case Machine.Val.env{+_x_831, +_rest_832}:
          (9n, {==})
        case Machine.Val.arg{+_q_833, +_x_834, +_rest_835}:
          (9n, {==})
        case Machine.Val.clo{+_t_836, +_e_837}:
          (9n, {==})
        case Machine.Val.lab{+_k_838}:
          (9n, {==})
        case Machine.Val.rfl{}:
          (12n, {==})
        case Machine.Val.tup{+_q_839, +_a_840, +_b_841}:
          (9n, {==})
        case Machine.Val.call{+_k_842, +_xs_843}:
          (9n, {==})
    case Machine.Fr.min1{+b_844, +e_845}:
      (13n, {==})
    case Machine.Fr.min2{+a_846}:
      FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ret.frame(), [FM.Enc.fr(Machine.Fr.min2{a_846}), FM.Enc.val(v_812), FM.Enc.frs(fs_813), FM.Enc.book(bk_814)], ks}}, Fun.F.iter(9n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ret.frame(), [FM.Enc.fr(Machine.Fr.min2{a_846}), FM.Enc.val(v_812), FM.Enc.frs(fs_813), FM.Enc.book(bk_814)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Ret.frame(Machine.Fr.min2{a_846}, v_812, fs_813, bk_814)), ks}},
        FP.Reach.steps(9n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ret.frame(), [FM.Enc.fr(Machine.Fr.min2{a_846}), FM.Enc.val(v_812), FM.Enc.frs(fs_813), FM.Enc.book(bk_814)], ks}}),
        L.Ret.meet(a_846, v_812, fs_813, ks))

def L.Ret.go(+v_847: Machine.Val, +fs_848: List<&2, Machine.Fr>, +bk_849: List<&2, Source.Def>, +ks: List<&2, Fun.Fr>) ->
  Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ret.go(), [FM.Enc.val(v_847), FM.Enc.frs(fs_848), FM.Enc.book(bk_849)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Ret.go(v_847, fs_848, bk_849)), ks}}):
  match fs_848:
    case Nil{}:
      (3n, {==})
    case Con{+fr_850, +rest_851}:
      FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ret.go(), [FM.Enc.val(v_847), FM.Enc.frs(Con{fr_850, rest_851}), FM.Enc.book(bk_849)], ks}}, Fun.F.iter(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ret.go(), [FM.Enc.val(v_847), FM.Enc.frs(Con{fr_850, rest_851}), FM.Enc.book(bk_849)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Ret.go(v_847, Con{fr_850, rest_851}, bk_849)), ks}},
        FP.Reach.steps(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ret.go(), [FM.Enc.val(v_847), FM.Enc.frs(Con{fr_850, rest_851}), FM.Enc.book(bk_849)], ks}}),
        L.Ret.frame(fr_850, v_847, rest_851, bk_849, ks))

def L.Machine.step(+s_852: Machine.St, +bk_853: List<&2, Source.Def>, +ks: List<&2, Fun.Fr>) ->
  Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Machine.step(), [FM.Enc.st(s_852), FM.Enc.book(bk_853)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Machine.step(s_852, bk_853)), ks}}):
  match s_852:
    case Machine.St.eval{+t_854, +e_855, +fs_856}:
      FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Machine.step(), [FM.Enc.st(Machine.St.eval{t_854, e_855, fs_856}), FM.Enc.book(bk_853)], ks}}, Fun.F.iter(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Machine.step(), [FM.Enc.st(Machine.St.eval{t_854, e_855, fs_856}), FM.Enc.book(bk_853)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Machine.step(Machine.St.eval{t_854, e_855, fs_856}, bk_853)), ks}},
        FP.Reach.steps(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Machine.step(), [FM.Enc.st(Machine.St.eval{t_854, e_855, fs_856}), FM.Enc.book(bk_853)], ks}}),
        L.Eval.go(t_854, e_855, fs_856, bk_853, ks))
    case Machine.St.ret{+v_857, +fs_858}:
      FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Machine.step(), [FM.Enc.st(Machine.St.ret{v_857, fs_858}), FM.Enc.book(bk_853)], ks}}, Fun.F.iter(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Machine.step(), [FM.Enc.st(Machine.St.ret{v_857, fs_858}), FM.Enc.book(bk_853)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Machine.step(Machine.St.ret{v_857, fs_858}, bk_853)), ks}},
        FP.Reach.steps(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Machine.step(), [FM.Enc.st(Machine.St.ret{v_857, fs_858}), FM.Enc.book(bk_853)], ks}}),
        L.Ret.go(v_857, fs_858, bk_853, ks))

def L.Ctor.is.Zero(+k_859: List<&2, Nat>, +u_860: List<&2, Nat>, +ks: List<&2, Fun.Fr>) ->
  Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ctor.is.Zero(), [FM.Enc.name(k_859), FM.Enc.name(u_860)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(Contract.Ctor.is(k_859, u_860, "Zero")), ks}}):
  FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ctor.is.Zero(), [FM.Enc.name(k_859), FM.Enc.name(u_860)], ks}}, Fun.F.iter(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ctor.is.Zero(), [FM.Enc.name(k_859), FM.Enc.name(u_860)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Contract.Ctor.is(k_859, u_860, "Zero")), ks}},
    FP.Reach.steps(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ctor.is.Zero(), [FM.Enc.name(k_859), FM.Enc.name(u_860)], ks}}),
    FP.Reach.trans(Code.prog(), Fun.F.iter(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ctor.is.Zero(), [FM.Enc.name(k_859), FM.Enc.name(u_860)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(k_859, Source.Name.of("Zero"))), Con{Fun.Fr{Code.F.Ctor.is.Zero.k1(), [FM.Enc.name(Source.Name.of("Zero")), FM.Enc.name(Source.Name.of("ero")), FM.Enc.name(Source.Name.of("ro")), FM.Enc.name(Source.Name.of("o")), FM.Enc.name(k_859), FM.Enc.name(u_860)]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(Contract.Ctor.is(k_859, u_860, "Zero")), ks}},
    L.Name.is_eq(k_859, Source.Name.of("Zero"), Con{Fun.Fr{Code.F.Ctor.is.Zero.k1(), [FM.Enc.name(Source.Name.of("Zero")), FM.Enc.name(Source.Name.of("ero")), FM.Enc.name(Source.Name.of("ro")), FM.Enc.name(Source.Name.of("o")), FM.Enc.name(k_859), FM.Enc.name(u_860)]}, ks}),
    FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(k_859, Source.Name.of("Zero"))), Con{Fun.Fr{Code.F.Ctor.is.Zero.k1(), [FM.Enc.name(Source.Name.of("Zero")), FM.Enc.name(Source.Name.of("ero")), FM.Enc.name(Source.Name.of("ro")), FM.Enc.name(Source.Name.of("o")), FM.Enc.name(k_859), FM.Enc.name(u_860)]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(k_859, Source.Name.of("Zero"))), Con{Fun.Fr{Code.F.Ctor.is.Zero.k1(), [FM.Enc.name(Source.Name.of("Zero")), FM.Enc.name(Source.Name.of("ero")), FM.Enc.name(Source.Name.of("ro")), FM.Enc.name(Source.Name.of("o")), FM.Enc.name(k_859), FM.Enc.name(u_860)]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Contract.Ctor.is(k_859, u_860, "Zero")), ks}},
    FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(k_859, Source.Name.of("Zero"))), Con{Fun.Fr{Code.F.Ctor.is.Zero.k1(), [FM.Enc.name(Source.Name.of("Zero")), FM.Enc.name(Source.Name.of("ero")), FM.Enc.name(Source.Name.of("ro")), FM.Enc.name(Source.Name.of("o")), FM.Enc.name(k_859), FM.Enc.name(u_860)]}, ks}}}),
    Elim.Bool(Source.Name.is_eq(k_859, Source.Name.of("Zero")), m38 => Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ctor.is.Zero.k1(), [FM.Enc.bool(m38), FM.Enc.name(Source.Name.of("Zero")), FM.Enc.name(Source.Name.of("ero")), FM.Enc.name(Source.Name.of("ro")), FM.Enc.name(Source.Name.of("o")), FM.Enc.name(k_859), FM.Enc.name(u_860)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(m38 && Source.Name.is_eq(u_860, Source.Name.of("()"))), ks}}),
    (2n, {==}),
    FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ctor.is.Zero.k1(), [FM.Enc.bool(True{}), FM.Enc.name(Source.Name.of("Zero")), FM.Enc.name(Source.Name.of("ero")), FM.Enc.name(Source.Name.of("ro")), FM.Enc.name(Source.Name.of("o")), FM.Enc.name(k_859), FM.Enc.name(u_860)], ks}}, Fun.F.iter(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ctor.is.Zero.k1(), [FM.Enc.bool(True{}), FM.Enc.name(Source.Name.of("Zero")), FM.Enc.name(Source.Name.of("ero")), FM.Enc.name(Source.Name.of("ro")), FM.Enc.name(Source.Name.of("o")), FM.Enc.name(k_859), FM.Enc.name(u_860)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(True{} && Source.Name.is_eq(u_860, Source.Name.of("()"))), ks}},
    FP.Reach.steps(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ctor.is.Zero.k1(), [FM.Enc.bool(True{}), FM.Enc.name(Source.Name.of("Zero")), FM.Enc.name(Source.Name.of("ero")), FM.Enc.name(Source.Name.of("ro")), FM.Enc.name(Source.Name.of("o")), FM.Enc.name(k_859), FM.Enc.name(u_860)], ks}}),
    L.Name.is_eq(u_860, Source.Name.of("()"), ks))))))

def L.Ctor.is.Succ(+k_862: List<&2, Nat>, +u_863: List<&2, Nat>, +ks: List<&2, Fun.Fr>) ->
  Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ctor.is.Succ(), [FM.Enc.name(k_862), FM.Enc.name(u_863)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(Contract.Ctor.is(k_862, u_863, "Succ")), ks}}):
  FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ctor.is.Succ(), [FM.Enc.name(k_862), FM.Enc.name(u_863)], ks}}, Fun.F.iter(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ctor.is.Succ(), [FM.Enc.name(k_862), FM.Enc.name(u_863)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Contract.Ctor.is(k_862, u_863, "Succ")), ks}},
    FP.Reach.steps(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ctor.is.Succ(), [FM.Enc.name(k_862), FM.Enc.name(u_863)], ks}}),
    FP.Reach.trans(Code.prog(), Fun.F.iter(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ctor.is.Succ(), [FM.Enc.name(k_862), FM.Enc.name(u_863)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(k_862, Source.Name.of("Succ"))), Con{Fun.Fr{Code.F.Ctor.is.Succ.k1(), [FM.Enc.name(Source.Name.of("Succ")), FM.Enc.name(Source.Name.of("ucc")), FM.Enc.name(Source.Name.of("cc")), FM.Enc.name(Source.Name.of("c")), FM.Enc.name(k_862), FM.Enc.name(u_863)]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(Contract.Ctor.is(k_862, u_863, "Succ")), ks}},
    L.Name.is_eq(k_862, Source.Name.of("Succ"), Con{Fun.Fr{Code.F.Ctor.is.Succ.k1(), [FM.Enc.name(Source.Name.of("Succ")), FM.Enc.name(Source.Name.of("ucc")), FM.Enc.name(Source.Name.of("cc")), FM.Enc.name(Source.Name.of("c")), FM.Enc.name(k_862), FM.Enc.name(u_863)]}, ks}),
    FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(k_862, Source.Name.of("Succ"))), Con{Fun.Fr{Code.F.Ctor.is.Succ.k1(), [FM.Enc.name(Source.Name.of("Succ")), FM.Enc.name(Source.Name.of("ucc")), FM.Enc.name(Source.Name.of("cc")), FM.Enc.name(Source.Name.of("c")), FM.Enc.name(k_862), FM.Enc.name(u_863)]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(k_862, Source.Name.of("Succ"))), Con{Fun.Fr{Code.F.Ctor.is.Succ.k1(), [FM.Enc.name(Source.Name.of("Succ")), FM.Enc.name(Source.Name.of("ucc")), FM.Enc.name(Source.Name.of("cc")), FM.Enc.name(Source.Name.of("c")), FM.Enc.name(k_862), FM.Enc.name(u_863)]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Contract.Ctor.is(k_862, u_863, "Succ")), ks}},
    FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(k_862, Source.Name.of("Succ"))), Con{Fun.Fr{Code.F.Ctor.is.Succ.k1(), [FM.Enc.name(Source.Name.of("Succ")), FM.Enc.name(Source.Name.of("ucc")), FM.Enc.name(Source.Name.of("cc")), FM.Enc.name(Source.Name.of("c")), FM.Enc.name(k_862), FM.Enc.name(u_863)]}, ks}}}),
    Elim.Bool(Source.Name.is_eq(k_862, Source.Name.of("Succ")), m39 => Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ctor.is.Succ.k1(), [FM.Enc.bool(m39), FM.Enc.name(Source.Name.of("Succ")), FM.Enc.name(Source.Name.of("ucc")), FM.Enc.name(Source.Name.of("cc")), FM.Enc.name(Source.Name.of("c")), FM.Enc.name(k_862), FM.Enc.name(u_863)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(m39 && Source.Name.is_eq(u_863, Source.Name.of("()"))), ks}}),
    (2n, {==}),
    FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ctor.is.Succ.k1(), [FM.Enc.bool(True{}), FM.Enc.name(Source.Name.of("Succ")), FM.Enc.name(Source.Name.of("ucc")), FM.Enc.name(Source.Name.of("cc")), FM.Enc.name(Source.Name.of("c")), FM.Enc.name(k_862), FM.Enc.name(u_863)], ks}}, Fun.F.iter(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ctor.is.Succ.k1(), [FM.Enc.bool(True{}), FM.Enc.name(Source.Name.of("Succ")), FM.Enc.name(Source.Name.of("ucc")), FM.Enc.name(Source.Name.of("cc")), FM.Enc.name(Source.Name.of("c")), FM.Enc.name(k_862), FM.Enc.name(u_863)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(True{} && Source.Name.is_eq(u_863, Source.Name.of("()"))), ks}},
    FP.Reach.steps(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ctor.is.Succ.k1(), [FM.Enc.bool(True{}), FM.Enc.name(Source.Name.of("Succ")), FM.Enc.name(Source.Name.of("ucc")), FM.Enc.name(Source.Name.of("cc")), FM.Enc.name(Source.Name.of("c")), FM.Enc.name(k_862), FM.Enc.name(u_863)], ks}}),
    L.Name.is_eq(u_863, Source.Name.of("()"), ks))))))

def L.Ctor.is.Nil(+k_865: List<&2, Nat>, +u_866: List<&2, Nat>, +ks: List<&2, Fun.Fr>) ->
  Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ctor.is.Nil(), [FM.Enc.name(k_865), FM.Enc.name(u_866)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(Contract.Ctor.is(k_865, u_866, "Nil")), ks}}):
  FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ctor.is.Nil(), [FM.Enc.name(k_865), FM.Enc.name(u_866)], ks}}, Fun.F.iter(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ctor.is.Nil(), [FM.Enc.name(k_865), FM.Enc.name(u_866)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Contract.Ctor.is(k_865, u_866, "Nil")), ks}},
    FP.Reach.steps(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ctor.is.Nil(), [FM.Enc.name(k_865), FM.Enc.name(u_866)], ks}}),
    FP.Reach.trans(Code.prog(), Fun.F.iter(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ctor.is.Nil(), [FM.Enc.name(k_865), FM.Enc.name(u_866)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(k_865, Source.Name.of("Nil"))), Con{Fun.Fr{Code.F.Ctor.is.Nil.k1(), [FM.Enc.name(Source.Name.of("Nil")), FM.Enc.name(Source.Name.of("il")), FM.Enc.name(Source.Name.of("l")), FM.Enc.name(k_865), FM.Enc.name(u_866)]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(Contract.Ctor.is(k_865, u_866, "Nil")), ks}},
    L.Name.is_eq(k_865, Source.Name.of("Nil"), Con{Fun.Fr{Code.F.Ctor.is.Nil.k1(), [FM.Enc.name(Source.Name.of("Nil")), FM.Enc.name(Source.Name.of("il")), FM.Enc.name(Source.Name.of("l")), FM.Enc.name(k_865), FM.Enc.name(u_866)]}, ks}),
    FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(k_865, Source.Name.of("Nil"))), Con{Fun.Fr{Code.F.Ctor.is.Nil.k1(), [FM.Enc.name(Source.Name.of("Nil")), FM.Enc.name(Source.Name.of("il")), FM.Enc.name(Source.Name.of("l")), FM.Enc.name(k_865), FM.Enc.name(u_866)]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(k_865, Source.Name.of("Nil"))), Con{Fun.Fr{Code.F.Ctor.is.Nil.k1(), [FM.Enc.name(Source.Name.of("Nil")), FM.Enc.name(Source.Name.of("il")), FM.Enc.name(Source.Name.of("l")), FM.Enc.name(k_865), FM.Enc.name(u_866)]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Contract.Ctor.is(k_865, u_866, "Nil")), ks}},
    FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(k_865, Source.Name.of("Nil"))), Con{Fun.Fr{Code.F.Ctor.is.Nil.k1(), [FM.Enc.name(Source.Name.of("Nil")), FM.Enc.name(Source.Name.of("il")), FM.Enc.name(Source.Name.of("l")), FM.Enc.name(k_865), FM.Enc.name(u_866)]}, ks}}}),
    Elim.Bool(Source.Name.is_eq(k_865, Source.Name.of("Nil")), m40 => Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ctor.is.Nil.k1(), [FM.Enc.bool(m40), FM.Enc.name(Source.Name.of("Nil")), FM.Enc.name(Source.Name.of("il")), FM.Enc.name(Source.Name.of("l")), FM.Enc.name(k_865), FM.Enc.name(u_866)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(m40 && Source.Name.is_eq(u_866, Source.Name.of("()"))), ks}}),
    (2n, {==}),
    FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ctor.is.Nil.k1(), [FM.Enc.bool(True{}), FM.Enc.name(Source.Name.of("Nil")), FM.Enc.name(Source.Name.of("il")), FM.Enc.name(Source.Name.of("l")), FM.Enc.name(k_865), FM.Enc.name(u_866)], ks}}, Fun.F.iter(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ctor.is.Nil.k1(), [FM.Enc.bool(True{}), FM.Enc.name(Source.Name.of("Nil")), FM.Enc.name(Source.Name.of("il")), FM.Enc.name(Source.Name.of("l")), FM.Enc.name(k_865), FM.Enc.name(u_866)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(True{} && Source.Name.is_eq(u_866, Source.Name.of("()"))), ks}},
    FP.Reach.steps(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ctor.is.Nil.k1(), [FM.Enc.bool(True{}), FM.Enc.name(Source.Name.of("Nil")), FM.Enc.name(Source.Name.of("il")), FM.Enc.name(Source.Name.of("l")), FM.Enc.name(k_865), FM.Enc.name(u_866)], ks}}),
    L.Name.is_eq(u_866, Source.Name.of("()"), ks))))))

def L.Ctor.is.Con(+k_868: List<&2, Nat>, +u_869: List<&2, Nat>, +ks: List<&2, Fun.Fr>) ->
  Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ctor.is.Con(), [FM.Enc.name(k_868), FM.Enc.name(u_869)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(Contract.Ctor.is(k_868, u_869, "Con")), ks}}):
  FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ctor.is.Con(), [FM.Enc.name(k_868), FM.Enc.name(u_869)], ks}}, Fun.F.iter(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ctor.is.Con(), [FM.Enc.name(k_868), FM.Enc.name(u_869)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Contract.Ctor.is(k_868, u_869, "Con")), ks}},
    FP.Reach.steps(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ctor.is.Con(), [FM.Enc.name(k_868), FM.Enc.name(u_869)], ks}}),
    FP.Reach.trans(Code.prog(), Fun.F.iter(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ctor.is.Con(), [FM.Enc.name(k_868), FM.Enc.name(u_869)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(k_868, Source.Name.of("Con"))), Con{Fun.Fr{Code.F.Ctor.is.Con.k1(), [FM.Enc.name(Source.Name.of("Con")), FM.Enc.name(Source.Name.of("on")), FM.Enc.name(Source.Name.of("n")), FM.Enc.name(k_868), FM.Enc.name(u_869)]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(Contract.Ctor.is(k_868, u_869, "Con")), ks}},
    L.Name.is_eq(k_868, Source.Name.of("Con"), Con{Fun.Fr{Code.F.Ctor.is.Con.k1(), [FM.Enc.name(Source.Name.of("Con")), FM.Enc.name(Source.Name.of("on")), FM.Enc.name(Source.Name.of("n")), FM.Enc.name(k_868), FM.Enc.name(u_869)]}, ks}),
    FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(k_868, Source.Name.of("Con"))), Con{Fun.Fr{Code.F.Ctor.is.Con.k1(), [FM.Enc.name(Source.Name.of("Con")), FM.Enc.name(Source.Name.of("on")), FM.Enc.name(Source.Name.of("n")), FM.Enc.name(k_868), FM.Enc.name(u_869)]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(k_868, Source.Name.of("Con"))), Con{Fun.Fr{Code.F.Ctor.is.Con.k1(), [FM.Enc.name(Source.Name.of("Con")), FM.Enc.name(Source.Name.of("on")), FM.Enc.name(Source.Name.of("n")), FM.Enc.name(k_868), FM.Enc.name(u_869)]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Contract.Ctor.is(k_868, u_869, "Con")), ks}},
    FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(k_868, Source.Name.of("Con"))), Con{Fun.Fr{Code.F.Ctor.is.Con.k1(), [FM.Enc.name(Source.Name.of("Con")), FM.Enc.name(Source.Name.of("on")), FM.Enc.name(Source.Name.of("n")), FM.Enc.name(k_868), FM.Enc.name(u_869)]}, ks}}}),
    Elim.Bool(Source.Name.is_eq(k_868, Source.Name.of("Con")), m41 => Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ctor.is.Con.k1(), [FM.Enc.bool(m41), FM.Enc.name(Source.Name.of("Con")), FM.Enc.name(Source.Name.of("on")), FM.Enc.name(Source.Name.of("n")), FM.Enc.name(k_868), FM.Enc.name(u_869)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(m41 && Source.Name.is_eq(u_869, Source.Name.of("()"))), ks}}),
    (2n, {==}),
    FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ctor.is.Con.k1(), [FM.Enc.bool(True{}), FM.Enc.name(Source.Name.of("Con")), FM.Enc.name(Source.Name.of("on")), FM.Enc.name(Source.Name.of("n")), FM.Enc.name(k_868), FM.Enc.name(u_869)], ks}}, Fun.F.iter(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ctor.is.Con.k1(), [FM.Enc.bool(True{}), FM.Enc.name(Source.Name.of("Con")), FM.Enc.name(Source.Name.of("on")), FM.Enc.name(Source.Name.of("n")), FM.Enc.name(k_868), FM.Enc.name(u_869)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(True{} && Source.Name.is_eq(u_869, Source.Name.of("()"))), ks}},
    FP.Reach.steps(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ctor.is.Con.k1(), [FM.Enc.bool(True{}), FM.Enc.name(Source.Name.of("Con")), FM.Enc.name(Source.Name.of("on")), FM.Enc.name(Source.Name.of("n")), FM.Enc.name(k_868), FM.Enc.name(u_869)], ks}}),
    L.Name.is_eq(u_869, Source.Name.of("()"), ks))))))

def L.Obs.nat(+o_871: Source.Obs, +ks: List<&2, Fun.Fr>) ->
  Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.nat(), [FM.Enc.obs(o_871)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.mnat(Contract.Obs.nat(o_871)), ks}}):
  match o_871:
    case Source.Obs.lab{+_k_872}:
      (2n, {==})
    case Source.Obs.rfl{}:
      (2n, {==})
    case Source.Obs.tup{+o1_873, +o2_874}:
      match o1_873:
        case Source.Obs.lab{+k_875}:
          match o2_874:
            case Source.Obs.lab{+u_876}:
              FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.nat(), [FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_875}, Source.Obs.lab{u_876}})], ks}}, Fun.F.iter(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.nat(), [FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_875}, Source.Obs.lab{u_876}})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.mnat(Contract.Obs.nat(Source.Obs.tup{Source.Obs.lab{k_875}, Source.Obs.lab{u_876}})), ks}},
                FP.Reach.steps(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.nat(), [FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_875}, Source.Obs.lab{u_876}})], ks}}),
                FP.Reach.trans(Code.prog(), Fun.F.iter(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.nat(), [FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_875}, Source.Obs.lab{u_876}})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Contract.Ctor.is(k_875, u_876, "Zero")), Con{Fun.Fr{Code.F.Obs.nat.k1(), [Fun.V.z{}, FM.Enc.name(u_876), Fun.V.z{}, FM.Enc.name(k_875), FM.Enc.obs(Source.Obs.lab{u_876}), FM.Enc.obs(Source.Obs.lab{k_875}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_875}, Source.Obs.lab{u_876}})]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.mnat(Contract.Obs.nat(Source.Obs.tup{Source.Obs.lab{k_875}, Source.Obs.lab{u_876}})), ks}},
                L.Ctor.is.Zero(k_875, u_876, Con{Fun.Fr{Code.F.Obs.nat.k1(), [Fun.V.z{}, FM.Enc.name(u_876), Fun.V.z{}, FM.Enc.name(k_875), FM.Enc.obs(Source.Obs.lab{u_876}), FM.Enc.obs(Source.Obs.lab{k_875}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_875}, Source.Obs.lab{u_876}})]}, ks}),
                FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Contract.Ctor.is(k_875, u_876, "Zero")), Con{Fun.Fr{Code.F.Obs.nat.k1(), [Fun.V.z{}, FM.Enc.name(u_876), Fun.V.z{}, FM.Enc.name(k_875), FM.Enc.obs(Source.Obs.lab{u_876}), FM.Enc.obs(Source.Obs.lab{k_875}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_875}, Source.Obs.lab{u_876}})]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Contract.Ctor.is(k_875, u_876, "Zero")), Con{Fun.Fr{Code.F.Obs.nat.k1(), [Fun.V.z{}, FM.Enc.name(u_876), Fun.V.z{}, FM.Enc.name(k_875), FM.Enc.obs(Source.Obs.lab{u_876}), FM.Enc.obs(Source.Obs.lab{k_875}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_875}, Source.Obs.lab{u_876}})]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.mnat(Contract.Obs.nat(Source.Obs.tup{Source.Obs.lab{k_875}, Source.Obs.lab{u_876}})), ks}},
                FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Contract.Ctor.is(k_875, u_876, "Zero")), Con{Fun.Fr{Code.F.Obs.nat.k1(), [Fun.V.z{}, FM.Enc.name(u_876), Fun.V.z{}, FM.Enc.name(k_875), FM.Enc.obs(Source.Obs.lab{u_876}), FM.Enc.obs(Source.Obs.lab{k_875}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_875}, Source.Obs.lab{u_876}})]}, ks}}}),
                Elim.Bool(Contract.Ctor.is(k_875, u_876, "Zero"), m42 => Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.nat.k1(), [FM.Enc.bool(m42), Fun.V.z{}, FM.Enc.name(u_876), Fun.V.z{}, FM.Enc.name(k_875), FM.Enc.obs(Source.Obs.lab{u_876}), FM.Enc.obs(Source.Obs.lab{k_875}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_875}, Source.Obs.lab{u_876}})], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.mnat(Bool.pick(Maybe<&2, Nat>, m42, Some{0n}, None{})), ks}}),
                (2n, {==}),
                (3n, {==})))))
            case Source.Obs.rfl{}:
              (5n, {==})
            case Source.Obs.tup{+h_878, +o3_879}:
              match o3_879:
                case Source.Obs.lab{+u_880}:
                  FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.nat(), [FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_875}, Source.Obs.tup{h_878, Source.Obs.lab{u_880}}})], ks}}, Fun.F.iter(6n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.nat(), [FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_875}, Source.Obs.tup{h_878, Source.Obs.lab{u_880}}})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.mnat(Contract.Obs.nat(Source.Obs.tup{Source.Obs.lab{k_875}, Source.Obs.tup{h_878, Source.Obs.lab{u_880}}})), ks}},
                    FP.Reach.steps(6n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.nat(), [FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_875}, Source.Obs.tup{h_878, Source.Obs.lab{u_880}}})], ks}}),
                    FP.Reach.trans(Code.prog(), Fun.F.iter(6n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.nat(), [FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_875}, Source.Obs.tup{h_878, Source.Obs.lab{u_880}}})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Contract.Ctor.is(k_875, u_880, "Succ")), Con{Fun.Fr{Code.F.Obs.nat.k2(), [Fun.V.z{}, FM.Enc.name(u_880), FM.Enc.obs(Source.Obs.lab{u_880}), FM.Enc.obs(h_878), Fun.V.z{}, FM.Enc.name(k_875), FM.Enc.obs(Source.Obs.tup{h_878, Source.Obs.lab{u_880}}), FM.Enc.obs(Source.Obs.lab{k_875}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_875}, Source.Obs.tup{h_878, Source.Obs.lab{u_880}}})]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.mnat(Contract.Obs.nat(Source.Obs.tup{Source.Obs.lab{k_875}, Source.Obs.tup{h_878, Source.Obs.lab{u_880}}})), ks}},
                    L.Ctor.is.Succ(k_875, u_880, Con{Fun.Fr{Code.F.Obs.nat.k2(), [Fun.V.z{}, FM.Enc.name(u_880), FM.Enc.obs(Source.Obs.lab{u_880}), FM.Enc.obs(h_878), Fun.V.z{}, FM.Enc.name(k_875), FM.Enc.obs(Source.Obs.tup{h_878, Source.Obs.lab{u_880}}), FM.Enc.obs(Source.Obs.lab{k_875}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_875}, Source.Obs.tup{h_878, Source.Obs.lab{u_880}}})]}, ks}),
                    FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Contract.Ctor.is(k_875, u_880, "Succ")), Con{Fun.Fr{Code.F.Obs.nat.k2(), [Fun.V.z{}, FM.Enc.name(u_880), FM.Enc.obs(Source.Obs.lab{u_880}), FM.Enc.obs(h_878), Fun.V.z{}, FM.Enc.name(k_875), FM.Enc.obs(Source.Obs.tup{h_878, Source.Obs.lab{u_880}}), FM.Enc.obs(Source.Obs.lab{k_875}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_875}, Source.Obs.tup{h_878, Source.Obs.lab{u_880}}})]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Contract.Ctor.is(k_875, u_880, "Succ")), Con{Fun.Fr{Code.F.Obs.nat.k2(), [Fun.V.z{}, FM.Enc.name(u_880), FM.Enc.obs(Source.Obs.lab{u_880}), FM.Enc.obs(h_878), Fun.V.z{}, FM.Enc.name(k_875), FM.Enc.obs(Source.Obs.tup{h_878, Source.Obs.lab{u_880}}), FM.Enc.obs(Source.Obs.lab{k_875}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_875}, Source.Obs.tup{h_878, Source.Obs.lab{u_880}}})]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.mnat(Contract.Obs.nat(Source.Obs.tup{Source.Obs.lab{k_875}, Source.Obs.tup{h_878, Source.Obs.lab{u_880}}})), ks}},
                    FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Contract.Ctor.is(k_875, u_880, "Succ")), Con{Fun.Fr{Code.F.Obs.nat.k2(), [Fun.V.z{}, FM.Enc.name(u_880), FM.Enc.obs(Source.Obs.lab{u_880}), FM.Enc.obs(h_878), Fun.V.z{}, FM.Enc.name(k_875), FM.Enc.obs(Source.Obs.tup{h_878, Source.Obs.lab{u_880}}), FM.Enc.obs(Source.Obs.lab{k_875}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_875}, Source.Obs.tup{h_878, Source.Obs.lab{u_880}}})]}, ks}}}),
                    Elim.Bool(Contract.Ctor.is(k_875, u_880, "Succ"), m43 => Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.nat.k2(), [FM.Enc.bool(m43), Fun.V.z{}, FM.Enc.name(u_880), FM.Enc.obs(Source.Obs.lab{u_880}), FM.Enc.obs(h_878), Fun.V.z{}, FM.Enc.name(k_875), FM.Enc.obs(Source.Obs.tup{h_878, Source.Obs.lab{u_880}}), FM.Enc.obs(Source.Obs.lab{k_875}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_875}, Source.Obs.tup{h_878, Source.Obs.lab{u_880}}})], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.mnat(Bool.pick(Maybe<&2, Nat>, m43, Contract.Obs.nat.succ(Contract.Obs.nat(h_878)), None{})), ks}}),
                    (2n, {==}),
                    FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.nat.k2(), [FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(u_880), FM.Enc.obs(Source.Obs.lab{u_880}), FM.Enc.obs(h_878), Fun.V.z{}, FM.Enc.name(k_875), FM.Enc.obs(Source.Obs.tup{h_878, Source.Obs.lab{u_880}}), FM.Enc.obs(Source.Obs.lab{k_875}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_875}, Source.Obs.tup{h_878, Source.Obs.lab{u_880}}})], ks}}, Fun.F.iter(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.nat.k2(), [FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(u_880), FM.Enc.obs(Source.Obs.lab{u_880}), FM.Enc.obs(h_878), Fun.V.z{}, FM.Enc.name(k_875), FM.Enc.obs(Source.Obs.tup{h_878, Source.Obs.lab{u_880}}), FM.Enc.obs(Source.Obs.lab{k_875}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_875}, Source.Obs.tup{h_878, Source.Obs.lab{u_880}}})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.mnat(Bool.pick(Maybe<&2, Nat>, True{}, Contract.Obs.nat.succ(Contract.Obs.nat(h_878)), None{})), ks}},
                    FP.Reach.steps(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.nat.k2(), [FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(u_880), FM.Enc.obs(Source.Obs.lab{u_880}), FM.Enc.obs(h_878), Fun.V.z{}, FM.Enc.name(k_875), FM.Enc.obs(Source.Obs.tup{h_878, Source.Obs.lab{u_880}}), FM.Enc.obs(Source.Obs.lab{k_875}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_875}, Source.Obs.tup{h_878, Source.Obs.lab{u_880}}})], ks}}),
                    FP.Reach.trans(Code.prog(), Fun.F.iter(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.nat.k2(), [FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(u_880), FM.Enc.obs(Source.Obs.lab{u_880}), FM.Enc.obs(h_878), Fun.V.z{}, FM.Enc.name(k_875), FM.Enc.obs(Source.Obs.tup{h_878, Source.Obs.lab{u_880}}), FM.Enc.obs(Source.Obs.lab{k_875}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_875}, Source.Obs.tup{h_878, Source.Obs.lab{u_880}}})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.mnat(Contract.Obs.nat(h_878)), Con{Fun.Fr{Code.F.Obs.nat.k3(), [Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(u_880), FM.Enc.obs(Source.Obs.lab{u_880}), FM.Enc.obs(h_878), Fun.V.z{}, FM.Enc.name(k_875), FM.Enc.obs(Source.Obs.tup{h_878, Source.Obs.lab{u_880}}), FM.Enc.obs(Source.Obs.lab{k_875}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_875}, Source.Obs.tup{h_878, Source.Obs.lab{u_880}}})]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.mnat(Bool.pick(Maybe<&2, Nat>, True{}, Contract.Obs.nat.succ(Contract.Obs.nat(h_878)), None{})), ks}},
                    L.Obs.nat(h_878, Con{Fun.Fr{Code.F.Obs.nat.k3(), [Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(u_880), FM.Enc.obs(Source.Obs.lab{u_880}), FM.Enc.obs(h_878), Fun.V.z{}, FM.Enc.name(k_875), FM.Enc.obs(Source.Obs.tup{h_878, Source.Obs.lab{u_880}}), FM.Enc.obs(Source.Obs.lab{k_875}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_875}, Source.Obs.tup{h_878, Source.Obs.lab{u_880}}})]}, ks}),
                    FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.mnat(Contract.Obs.nat(h_878)), Con{Fun.Fr{Code.F.Obs.nat.k3(), [Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(u_880), FM.Enc.obs(Source.Obs.lab{u_880}), FM.Enc.obs(h_878), Fun.V.z{}, FM.Enc.name(k_875), FM.Enc.obs(Source.Obs.tup{h_878, Source.Obs.lab{u_880}}), FM.Enc.obs(Source.Obs.lab{k_875}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_875}, Source.Obs.tup{h_878, Source.Obs.lab{u_880}}})]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.mnat(Contract.Obs.nat(h_878)), Con{Fun.Fr{Code.F.Obs.nat.k3(), [Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(u_880), FM.Enc.obs(Source.Obs.lab{u_880}), FM.Enc.obs(h_878), Fun.V.z{}, FM.Enc.name(k_875), FM.Enc.obs(Source.Obs.tup{h_878, Source.Obs.lab{u_880}}), FM.Enc.obs(Source.Obs.lab{k_875}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_875}, Source.Obs.tup{h_878, Source.Obs.lab{u_880}}})]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.mnat(Bool.pick(Maybe<&2, Nat>, True{}, Contract.Obs.nat.succ(Contract.Obs.nat(h_878)), None{})), ks}},
                    FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.mnat(Contract.Obs.nat(h_878)), Con{Fun.Fr{Code.F.Obs.nat.k3(), [Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(u_880), FM.Enc.obs(Source.Obs.lab{u_880}), FM.Enc.obs(h_878), Fun.V.z{}, FM.Enc.name(k_875), FM.Enc.obs(Source.Obs.tup{h_878, Source.Obs.lab{u_880}}), FM.Enc.obs(Source.Obs.lab{k_875}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_875}, Source.Obs.tup{h_878, Source.Obs.lab{u_880}}})]}, ks}}}),
                    Elim.MNat(Contract.Obs.nat(h_878), m44 => Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.nat.k3(), [FM.Enc.mnat(m44), Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(u_880), FM.Enc.obs(Source.Obs.lab{u_880}), FM.Enc.obs(h_878), Fun.V.z{}, FM.Enc.name(k_875), FM.Enc.obs(Source.Obs.tup{h_878, Source.Obs.lab{u_880}}), FM.Enc.obs(Source.Obs.lab{k_875}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_875}, Source.Obs.tup{h_878, Source.Obs.lab{u_880}}})], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.mnat(Contract.Obs.nat.succ(m44)), ks}}),
                    (2n, {==}),
                    +n_883 => (4n, {==})))))))))
                case Source.Obs.rfl{}:
                  (6n, {==})
                case Source.Obs.tup{+_a_885, +_b_886}:
                  (6n, {==})
                case Source.Obs.tup0{+_b_887}:
                  (6n, {==})
            case Source.Obs.tup0{+_b_888}:
              (5n, {==})
        case Source.Obs.rfl{}:
          (3n, {==})
        case Source.Obs.tup{+_a_889, +_b_890}:
          (3n, {==})
        case Source.Obs.tup0{+_b_891}:
          (3n, {==})
    case Source.Obs.tup0{+_b_892}:
      (2n, {==})

def L.Nat.le(+n_893: Nat, +c_894: Nat, +ks: List<&2, Fun.Fr>) ->
  Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Nat.le(), [FM.Enc.nat(n_893), FM.Enc.nat(c_894)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(Nat.is_le(n_893, c_894)), ks}}):
  match n_893:
    case 0n:
      match c_894:
        case 0n:
          (2n, {==})
        case 1n+_p_895:
          (2n, {==})
    case 1n+p_896:
      match c_894:
        case 0n:
          (3n, {==})
        case 1n+d_897:
          FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Nat.le(), [FM.Enc.nat(1n+p_896), FM.Enc.nat(1n+d_897)], ks}}, Fun.F.iter(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Nat.le(), [FM.Enc.nat(1n+p_896), FM.Enc.nat(1n+d_897)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Nat.is_le(1n+p_896, 1n+d_897)), ks}},
            FP.Reach.steps(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Nat.le(), [FM.Enc.nat(1n+p_896), FM.Enc.nat(1n+d_897)], ks}}),
            L.Nat.le(p_896, d_897, ks))

def L.AtMost255(+x_898: Nat, +ks: List<&2, Fun.Fr>) ->
  Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.AtMost255(), [FM.Enc.nat(x_898)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(Wasm.Nat.at_most(x_898, 255)), ks}}):
  FP.Reach.end(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.AtMost255(), [FM.Enc.nat(x_898)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(Nat.is_le(x_898, 255n)), ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(Wasm.Nat.at_most(x_898, 255)), ks}},
    Equal.cong(Bool, Fun.Step, b => Fun.Step.go{Fun.S.ret{FM.Enc.bool(b), ks}}, Nat.is_le(x_898, 255n), Wasm.Nat.at_most(x_898, 255), Equal.sym(Bool, Wasm.Nat.at_most(x_898, 255), Nat.is_le(x_898, 255n), AtMost.k255(x_898))),
    FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.AtMost255(), [FM.Enc.nat(x_898)], ks}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.AtMost255(), [FM.Enc.nat(x_898)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Nat.is_le(x_898, 255n)), ks}},
      FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.AtMost255(), [FM.Enc.nat(x_898)], ks}}), L.Nat.le(x_898, 255n, ks)))

def L.Obs.bytes.con(+n_899: Maybe<&2, Nat>, +bs_900: Maybe<&2, List<&2, Nat>>, +ks: List<&2, Fun.Fr>) ->
  Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.bytes.con(), [FM.Enc.mnat(n_899), FM.Enc.mname(bs_900)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.mname(Contract.Obs.bytes.con(n_899, bs_900)), ks}}):
  match n_899:
    case None{}:
      (2n, {==})
    case Some{+x_901}:
      match bs_900:
        case None{}:
          (3n, {==})
        case Some{+ys_902}:
          FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.bytes.con(), [FM.Enc.mnat(Some{x_901}), FM.Enc.mname(Some{ys_902})], ks}}, Fun.F.iter(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.bytes.con(), [FM.Enc.mnat(Some{x_901}), FM.Enc.mname(Some{ys_902})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.mname(Contract.Obs.bytes.con(Some{x_901}, Some{ys_902})), ks}},
            FP.Reach.steps(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.bytes.con(), [FM.Enc.mnat(Some{x_901}), FM.Enc.mname(Some{ys_902})], ks}}),
            FP.Reach.trans(Code.prog(), Fun.F.iter(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.bytes.con(), [FM.Enc.mnat(Some{x_901}), FM.Enc.mname(Some{ys_902})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Wasm.Nat.at_most(x_901, 255)), Con{Fun.Fr{Code.F.Obs.bytes.con.k1(), [Fun.V.z{}, FM.Enc.name(ys_902), Fun.V.z{}, FM.Enc.nat(x_901), FM.Enc.mnat(Some{x_901}), FM.Enc.mname(Some{ys_902})]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.mname(Contract.Obs.bytes.con(Some{x_901}, Some{ys_902})), ks}},
            L.AtMost255(x_901, Con{Fun.Fr{Code.F.Obs.bytes.con.k1(), [Fun.V.z{}, FM.Enc.name(ys_902), Fun.V.z{}, FM.Enc.nat(x_901), FM.Enc.mnat(Some{x_901}), FM.Enc.mname(Some{ys_902})]}, ks}),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Wasm.Nat.at_most(x_901, 255)), Con{Fun.Fr{Code.F.Obs.bytes.con.k1(), [Fun.V.z{}, FM.Enc.name(ys_902), Fun.V.z{}, FM.Enc.nat(x_901), FM.Enc.mnat(Some{x_901}), FM.Enc.mname(Some{ys_902})]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Wasm.Nat.at_most(x_901, 255)), Con{Fun.Fr{Code.F.Obs.bytes.con.k1(), [Fun.V.z{}, FM.Enc.name(ys_902), Fun.V.z{}, FM.Enc.nat(x_901), FM.Enc.mnat(Some{x_901}), FM.Enc.mname(Some{ys_902})]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.mname(Contract.Obs.bytes.con(Some{x_901}, Some{ys_902})), ks}},
            FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Wasm.Nat.at_most(x_901, 255)), Con{Fun.Fr{Code.F.Obs.bytes.con.k1(), [Fun.V.z{}, FM.Enc.name(ys_902), Fun.V.z{}, FM.Enc.nat(x_901), FM.Enc.mnat(Some{x_901}), FM.Enc.mname(Some{ys_902})]}, ks}}}),
            Elim.Bool(Wasm.Nat.at_most(x_901, 255), m45 => Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.bytes.con.k1(), [FM.Enc.bool(m45), Fun.V.z{}, FM.Enc.name(ys_902), Fun.V.z{}, FM.Enc.nat(x_901), FM.Enc.mnat(Some{x_901}), FM.Enc.mname(Some{ys_902})], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.mname(Bool.pick(Maybe<&2, List<&2, Nat>>, m45, Some{Con{x_901, ys_902}}, None{})), ks}}),
            (2n, {==}),
            (4n, {==})))))

def L.Obs.bytes(+o_904: Source.Obs, +ks: List<&2, Fun.Fr>) ->
  Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.bytes(), [FM.Enc.obs(o_904)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.mname(Contract.Obs.bytes(o_904)), ks}}):
  match o_904:
    case Source.Obs.lab{+_k_905}:
      (2n, {==})
    case Source.Obs.rfl{}:
      (2n, {==})
    case Source.Obs.tup{+o1_906, +o2_907}:
      match o1_906:
        case Source.Obs.lab{+k_908}:
          match o2_907:
            case Source.Obs.lab{+u_909}:
              FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.bytes(), [FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_908}, Source.Obs.lab{u_909}})], ks}}, Fun.F.iter(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.bytes(), [FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_908}, Source.Obs.lab{u_909}})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.mname(Contract.Obs.bytes(Source.Obs.tup{Source.Obs.lab{k_908}, Source.Obs.lab{u_909}})), ks}},
                FP.Reach.steps(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.bytes(), [FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_908}, Source.Obs.lab{u_909}})], ks}}),
                FP.Reach.trans(Code.prog(), Fun.F.iter(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.bytes(), [FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_908}, Source.Obs.lab{u_909}})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Contract.Ctor.is(k_908, u_909, "Nil")), Con{Fun.Fr{Code.F.Obs.bytes.k1(), [Fun.V.z{}, FM.Enc.name(u_909), Fun.V.z{}, FM.Enc.name(k_908), FM.Enc.obs(Source.Obs.lab{u_909}), FM.Enc.obs(Source.Obs.lab{k_908}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_908}, Source.Obs.lab{u_909}})]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.mname(Contract.Obs.bytes(Source.Obs.tup{Source.Obs.lab{k_908}, Source.Obs.lab{u_909}})), ks}},
                L.Ctor.is.Nil(k_908, u_909, Con{Fun.Fr{Code.F.Obs.bytes.k1(), [Fun.V.z{}, FM.Enc.name(u_909), Fun.V.z{}, FM.Enc.name(k_908), FM.Enc.obs(Source.Obs.lab{u_909}), FM.Enc.obs(Source.Obs.lab{k_908}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_908}, Source.Obs.lab{u_909}})]}, ks}),
                FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Contract.Ctor.is(k_908, u_909, "Nil")), Con{Fun.Fr{Code.F.Obs.bytes.k1(), [Fun.V.z{}, FM.Enc.name(u_909), Fun.V.z{}, FM.Enc.name(k_908), FM.Enc.obs(Source.Obs.lab{u_909}), FM.Enc.obs(Source.Obs.lab{k_908}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_908}, Source.Obs.lab{u_909}})]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Contract.Ctor.is(k_908, u_909, "Nil")), Con{Fun.Fr{Code.F.Obs.bytes.k1(), [Fun.V.z{}, FM.Enc.name(u_909), Fun.V.z{}, FM.Enc.name(k_908), FM.Enc.obs(Source.Obs.lab{u_909}), FM.Enc.obs(Source.Obs.lab{k_908}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_908}, Source.Obs.lab{u_909}})]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.mname(Contract.Obs.bytes(Source.Obs.tup{Source.Obs.lab{k_908}, Source.Obs.lab{u_909}})), ks}},
                FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Contract.Ctor.is(k_908, u_909, "Nil")), Con{Fun.Fr{Code.F.Obs.bytes.k1(), [Fun.V.z{}, FM.Enc.name(u_909), Fun.V.z{}, FM.Enc.name(k_908), FM.Enc.obs(Source.Obs.lab{u_909}), FM.Enc.obs(Source.Obs.lab{k_908}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_908}, Source.Obs.lab{u_909}})]}, ks}}}),
                Elim.Bool(Contract.Ctor.is(k_908, u_909, "Nil"), m46 => Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.bytes.k1(), [FM.Enc.bool(m46), Fun.V.z{}, FM.Enc.name(u_909), Fun.V.z{}, FM.Enc.name(k_908), FM.Enc.obs(Source.Obs.lab{u_909}), FM.Enc.obs(Source.Obs.lab{k_908}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_908}, Source.Obs.lab{u_909}})], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.mname(Bool.pick(Maybe<&2, List<&2, Nat>>, m46, Some{[]}, None{})), ks}}),
                (2n, {==}),
                (3n, {==})))))
            case Source.Obs.rfl{}:
              (5n, {==})
            case Source.Obs.tup{+h_911, +o3_912}:
              match o3_912:
                case Source.Obs.lab{+_k_913}:
                  (6n, {==})
                case Source.Obs.rfl{}:
                  (6n, {==})
                case Source.Obs.tup{+t_914, +o4_915}:
                  match o4_915:
                    case Source.Obs.lab{+u_916}:
                      FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.bytes(), [FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_908}, Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}})], ks}}, Fun.F.iter(7n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.bytes(), [FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_908}, Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.mname(Contract.Obs.bytes(Source.Obs.tup{Source.Obs.lab{k_908}, Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}})), ks}},
                        FP.Reach.steps(7n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.bytes(), [FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_908}, Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}})], ks}}),
                        FP.Reach.trans(Code.prog(), Fun.F.iter(7n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.bytes(), [FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_908}, Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Contract.Ctor.is(k_908, u_916, "Con")), Con{Fun.Fr{Code.F.Obs.bytes.k2(), [Fun.V.z{}, FM.Enc.name(u_916), FM.Enc.obs(Source.Obs.lab{u_916}), FM.Enc.obs(t_914), FM.Enc.obs(Source.Obs.tup{t_914, Source.Obs.lab{u_916}}), FM.Enc.obs(h_911), Fun.V.z{}, FM.Enc.name(k_908), FM.Enc.obs(Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}), FM.Enc.obs(Source.Obs.lab{k_908}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_908}, Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}})]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.mname(Contract.Obs.bytes(Source.Obs.tup{Source.Obs.lab{k_908}, Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}})), ks}},
                        L.Ctor.is.Con(k_908, u_916, Con{Fun.Fr{Code.F.Obs.bytes.k2(), [Fun.V.z{}, FM.Enc.name(u_916), FM.Enc.obs(Source.Obs.lab{u_916}), FM.Enc.obs(t_914), FM.Enc.obs(Source.Obs.tup{t_914, Source.Obs.lab{u_916}}), FM.Enc.obs(h_911), Fun.V.z{}, FM.Enc.name(k_908), FM.Enc.obs(Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}), FM.Enc.obs(Source.Obs.lab{k_908}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_908}, Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}})]}, ks}),
                        FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Contract.Ctor.is(k_908, u_916, "Con")), Con{Fun.Fr{Code.F.Obs.bytes.k2(), [Fun.V.z{}, FM.Enc.name(u_916), FM.Enc.obs(Source.Obs.lab{u_916}), FM.Enc.obs(t_914), FM.Enc.obs(Source.Obs.tup{t_914, Source.Obs.lab{u_916}}), FM.Enc.obs(h_911), Fun.V.z{}, FM.Enc.name(k_908), FM.Enc.obs(Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}), FM.Enc.obs(Source.Obs.lab{k_908}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_908}, Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}})]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Contract.Ctor.is(k_908, u_916, "Con")), Con{Fun.Fr{Code.F.Obs.bytes.k2(), [Fun.V.z{}, FM.Enc.name(u_916), FM.Enc.obs(Source.Obs.lab{u_916}), FM.Enc.obs(t_914), FM.Enc.obs(Source.Obs.tup{t_914, Source.Obs.lab{u_916}}), FM.Enc.obs(h_911), Fun.V.z{}, FM.Enc.name(k_908), FM.Enc.obs(Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}), FM.Enc.obs(Source.Obs.lab{k_908}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_908}, Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}})]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.mname(Contract.Obs.bytes(Source.Obs.tup{Source.Obs.lab{k_908}, Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}})), ks}},
                        FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Contract.Ctor.is(k_908, u_916, "Con")), Con{Fun.Fr{Code.F.Obs.bytes.k2(), [Fun.V.z{}, FM.Enc.name(u_916), FM.Enc.obs(Source.Obs.lab{u_916}), FM.Enc.obs(t_914), FM.Enc.obs(Source.Obs.tup{t_914, Source.Obs.lab{u_916}}), FM.Enc.obs(h_911), Fun.V.z{}, FM.Enc.name(k_908), FM.Enc.obs(Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}), FM.Enc.obs(Source.Obs.lab{k_908}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_908}, Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}})]}, ks}}}),
                        Elim.Bool(Contract.Ctor.is(k_908, u_916, "Con"), m47 => Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.bytes.k2(), [FM.Enc.bool(m47), Fun.V.z{}, FM.Enc.name(u_916), FM.Enc.obs(Source.Obs.lab{u_916}), FM.Enc.obs(t_914), FM.Enc.obs(Source.Obs.tup{t_914, Source.Obs.lab{u_916}}), FM.Enc.obs(h_911), Fun.V.z{}, FM.Enc.name(k_908), FM.Enc.obs(Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}), FM.Enc.obs(Source.Obs.lab{k_908}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_908}, Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}})], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.mname(Bool.pick(Maybe<&2, List<&2, Nat>>, m47, Contract.Obs.bytes.con(Contract.Obs.nat(h_911), Contract.Obs.bytes(t_914)), None{})), ks}}),
                        (2n, {==}),
                        FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.bytes.k2(), [FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(u_916), FM.Enc.obs(Source.Obs.lab{u_916}), FM.Enc.obs(t_914), FM.Enc.obs(Source.Obs.tup{t_914, Source.Obs.lab{u_916}}), FM.Enc.obs(h_911), Fun.V.z{}, FM.Enc.name(k_908), FM.Enc.obs(Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}), FM.Enc.obs(Source.Obs.lab{k_908}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_908}, Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}})], ks}}, Fun.F.iter(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.bytes.k2(), [FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(u_916), FM.Enc.obs(Source.Obs.lab{u_916}), FM.Enc.obs(t_914), FM.Enc.obs(Source.Obs.tup{t_914, Source.Obs.lab{u_916}}), FM.Enc.obs(h_911), Fun.V.z{}, FM.Enc.name(k_908), FM.Enc.obs(Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}), FM.Enc.obs(Source.Obs.lab{k_908}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_908}, Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.mname(Bool.pick(Maybe<&2, List<&2, Nat>>, True{}, Contract.Obs.bytes.con(Contract.Obs.nat(h_911), Contract.Obs.bytes(t_914)), None{})), ks}},
                        FP.Reach.steps(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.bytes.k2(), [FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(u_916), FM.Enc.obs(Source.Obs.lab{u_916}), FM.Enc.obs(t_914), FM.Enc.obs(Source.Obs.tup{t_914, Source.Obs.lab{u_916}}), FM.Enc.obs(h_911), Fun.V.z{}, FM.Enc.name(k_908), FM.Enc.obs(Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}), FM.Enc.obs(Source.Obs.lab{k_908}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_908}, Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}})], ks}}),
                        FP.Reach.trans(Code.prog(), Fun.F.iter(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.bytes.k2(), [FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(u_916), FM.Enc.obs(Source.Obs.lab{u_916}), FM.Enc.obs(t_914), FM.Enc.obs(Source.Obs.tup{t_914, Source.Obs.lab{u_916}}), FM.Enc.obs(h_911), Fun.V.z{}, FM.Enc.name(k_908), FM.Enc.obs(Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}), FM.Enc.obs(Source.Obs.lab{k_908}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_908}, Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.mnat(Contract.Obs.nat(h_911)), Con{Fun.Fr{Code.F.Obs.bytes.k3(), [Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(u_916), FM.Enc.obs(Source.Obs.lab{u_916}), FM.Enc.obs(t_914), FM.Enc.obs(Source.Obs.tup{t_914, Source.Obs.lab{u_916}}), FM.Enc.obs(h_911), Fun.V.z{}, FM.Enc.name(k_908), FM.Enc.obs(Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}), FM.Enc.obs(Source.Obs.lab{k_908}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_908}, Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}})]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.mname(Bool.pick(Maybe<&2, List<&2, Nat>>, True{}, Contract.Obs.bytes.con(Contract.Obs.nat(h_911), Contract.Obs.bytes(t_914)), None{})), ks}},
                        L.Obs.nat(h_911, Con{Fun.Fr{Code.F.Obs.bytes.k3(), [Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(u_916), FM.Enc.obs(Source.Obs.lab{u_916}), FM.Enc.obs(t_914), FM.Enc.obs(Source.Obs.tup{t_914, Source.Obs.lab{u_916}}), FM.Enc.obs(h_911), Fun.V.z{}, FM.Enc.name(k_908), FM.Enc.obs(Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}), FM.Enc.obs(Source.Obs.lab{k_908}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_908}, Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}})]}, ks}),
                        FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.mnat(Contract.Obs.nat(h_911)), Con{Fun.Fr{Code.F.Obs.bytes.k3(), [Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(u_916), FM.Enc.obs(Source.Obs.lab{u_916}), FM.Enc.obs(t_914), FM.Enc.obs(Source.Obs.tup{t_914, Source.Obs.lab{u_916}}), FM.Enc.obs(h_911), Fun.V.z{}, FM.Enc.name(k_908), FM.Enc.obs(Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}), FM.Enc.obs(Source.Obs.lab{k_908}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_908}, Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}})]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.mnat(Contract.Obs.nat(h_911)), Con{Fun.Fr{Code.F.Obs.bytes.k3(), [Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(u_916), FM.Enc.obs(Source.Obs.lab{u_916}), FM.Enc.obs(t_914), FM.Enc.obs(Source.Obs.tup{t_914, Source.Obs.lab{u_916}}), FM.Enc.obs(h_911), Fun.V.z{}, FM.Enc.name(k_908), FM.Enc.obs(Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}), FM.Enc.obs(Source.Obs.lab{k_908}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_908}, Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}})]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.mname(Bool.pick(Maybe<&2, List<&2, Nat>>, True{}, Contract.Obs.bytes.con(Contract.Obs.nat(h_911), Contract.Obs.bytes(t_914)), None{})), ks}},
                        FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.mnat(Contract.Obs.nat(h_911)), Con{Fun.Fr{Code.F.Obs.bytes.k3(), [Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(u_916), FM.Enc.obs(Source.Obs.lab{u_916}), FM.Enc.obs(t_914), FM.Enc.obs(Source.Obs.tup{t_914, Source.Obs.lab{u_916}}), FM.Enc.obs(h_911), Fun.V.z{}, FM.Enc.name(k_908), FM.Enc.obs(Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}), FM.Enc.obs(Source.Obs.lab{k_908}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_908}, Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}})]}, ks}}}),
                        FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.bytes.k3(), [FM.Enc.mnat(Contract.Obs.nat(h_911)), Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(u_916), FM.Enc.obs(Source.Obs.lab{u_916}), FM.Enc.obs(t_914), FM.Enc.obs(Source.Obs.tup{t_914, Source.Obs.lab{u_916}}), FM.Enc.obs(h_911), Fun.V.z{}, FM.Enc.name(k_908), FM.Enc.obs(Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}), FM.Enc.obs(Source.Obs.lab{k_908}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_908}, Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}})], ks}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.bytes.k3(), [FM.Enc.mnat(Contract.Obs.nat(h_911)), Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(u_916), FM.Enc.obs(Source.Obs.lab{u_916}), FM.Enc.obs(t_914), FM.Enc.obs(Source.Obs.tup{t_914, Source.Obs.lab{u_916}}), FM.Enc.obs(h_911), Fun.V.z{}, FM.Enc.name(k_908), FM.Enc.obs(Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}), FM.Enc.obs(Source.Obs.lab{k_908}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_908}, Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.mname(Contract.Obs.bytes.con(Contract.Obs.nat(h_911), Contract.Obs.bytes(t_914))), ks}},
                        FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.bytes.k3(), [FM.Enc.mnat(Contract.Obs.nat(h_911)), Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(u_916), FM.Enc.obs(Source.Obs.lab{u_916}), FM.Enc.obs(t_914), FM.Enc.obs(Source.Obs.tup{t_914, Source.Obs.lab{u_916}}), FM.Enc.obs(h_911), Fun.V.z{}, FM.Enc.name(k_908), FM.Enc.obs(Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}), FM.Enc.obs(Source.Obs.lab{k_908}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_908}, Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}})], ks}}),
                        FP.Reach.trans(Code.prog(), Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.bytes.k3(), [FM.Enc.mnat(Contract.Obs.nat(h_911)), Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(u_916), FM.Enc.obs(Source.Obs.lab{u_916}), FM.Enc.obs(t_914), FM.Enc.obs(Source.Obs.tup{t_914, Source.Obs.lab{u_916}}), FM.Enc.obs(h_911), Fun.V.z{}, FM.Enc.name(k_908), FM.Enc.obs(Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}), FM.Enc.obs(Source.Obs.lab{k_908}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_908}, Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.mname(Contract.Obs.bytes(t_914)), Con{Fun.Fr{Code.F.Obs.bytes.k4(), [FM.Enc.mnat(Contract.Obs.nat(h_911)), Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(u_916), FM.Enc.obs(Source.Obs.lab{u_916}), FM.Enc.obs(t_914), FM.Enc.obs(Source.Obs.tup{t_914, Source.Obs.lab{u_916}}), FM.Enc.obs(h_911), Fun.V.z{}, FM.Enc.name(k_908), FM.Enc.obs(Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}), FM.Enc.obs(Source.Obs.lab{k_908}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_908}, Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}})]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.mname(Contract.Obs.bytes.con(Contract.Obs.nat(h_911), Contract.Obs.bytes(t_914))), ks}},
                        L.Obs.bytes(t_914, Con{Fun.Fr{Code.F.Obs.bytes.k4(), [FM.Enc.mnat(Contract.Obs.nat(h_911)), Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(u_916), FM.Enc.obs(Source.Obs.lab{u_916}), FM.Enc.obs(t_914), FM.Enc.obs(Source.Obs.tup{t_914, Source.Obs.lab{u_916}}), FM.Enc.obs(h_911), Fun.V.z{}, FM.Enc.name(k_908), FM.Enc.obs(Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}), FM.Enc.obs(Source.Obs.lab{k_908}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_908}, Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}})]}, ks}),
                        FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.mname(Contract.Obs.bytes(t_914)), Con{Fun.Fr{Code.F.Obs.bytes.k4(), [FM.Enc.mnat(Contract.Obs.nat(h_911)), Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(u_916), FM.Enc.obs(Source.Obs.lab{u_916}), FM.Enc.obs(t_914), FM.Enc.obs(Source.Obs.tup{t_914, Source.Obs.lab{u_916}}), FM.Enc.obs(h_911), Fun.V.z{}, FM.Enc.name(k_908), FM.Enc.obs(Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}), FM.Enc.obs(Source.Obs.lab{k_908}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_908}, Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}})]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.mname(Contract.Obs.bytes(t_914)), Con{Fun.Fr{Code.F.Obs.bytes.k4(), [FM.Enc.mnat(Contract.Obs.nat(h_911)), Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(u_916), FM.Enc.obs(Source.Obs.lab{u_916}), FM.Enc.obs(t_914), FM.Enc.obs(Source.Obs.tup{t_914, Source.Obs.lab{u_916}}), FM.Enc.obs(h_911), Fun.V.z{}, FM.Enc.name(k_908), FM.Enc.obs(Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}), FM.Enc.obs(Source.Obs.lab{k_908}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_908}, Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}})]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.mname(Contract.Obs.bytes.con(Contract.Obs.nat(h_911), Contract.Obs.bytes(t_914))), ks}},
                        FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.mname(Contract.Obs.bytes(t_914)), Con{Fun.Fr{Code.F.Obs.bytes.k4(), [FM.Enc.mnat(Contract.Obs.nat(h_911)), Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(u_916), FM.Enc.obs(Source.Obs.lab{u_916}), FM.Enc.obs(t_914), FM.Enc.obs(Source.Obs.tup{t_914, Source.Obs.lab{u_916}}), FM.Enc.obs(h_911), Fun.V.z{}, FM.Enc.name(k_908), FM.Enc.obs(Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}), FM.Enc.obs(Source.Obs.lab{k_908}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_908}, Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}})]}, ks}}}),
                        FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.bytes.k4(), [FM.Enc.mname(Contract.Obs.bytes(t_914)), FM.Enc.mnat(Contract.Obs.nat(h_911)), Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(u_916), FM.Enc.obs(Source.Obs.lab{u_916}), FM.Enc.obs(t_914), FM.Enc.obs(Source.Obs.tup{t_914, Source.Obs.lab{u_916}}), FM.Enc.obs(h_911), Fun.V.z{}, FM.Enc.name(k_908), FM.Enc.obs(Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}), FM.Enc.obs(Source.Obs.lab{k_908}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_908}, Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}})], ks}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.bytes.k4(), [FM.Enc.mname(Contract.Obs.bytes(t_914)), FM.Enc.mnat(Contract.Obs.nat(h_911)), Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(u_916), FM.Enc.obs(Source.Obs.lab{u_916}), FM.Enc.obs(t_914), FM.Enc.obs(Source.Obs.tup{t_914, Source.Obs.lab{u_916}}), FM.Enc.obs(h_911), Fun.V.z{}, FM.Enc.name(k_908), FM.Enc.obs(Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}), FM.Enc.obs(Source.Obs.lab{k_908}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_908}, Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.mname(Contract.Obs.bytes.con(Contract.Obs.nat(h_911), Contract.Obs.bytes(t_914))), ks}},
                        FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.bytes.k4(), [FM.Enc.mname(Contract.Obs.bytes(t_914)), FM.Enc.mnat(Contract.Obs.nat(h_911)), Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(u_916), FM.Enc.obs(Source.Obs.lab{u_916}), FM.Enc.obs(t_914), FM.Enc.obs(Source.Obs.tup{t_914, Source.Obs.lab{u_916}}), FM.Enc.obs(h_911), Fun.V.z{}, FM.Enc.name(k_908), FM.Enc.obs(Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}), FM.Enc.obs(Source.Obs.lab{k_908}), FM.Enc.obs(Source.Obs.tup{Source.Obs.lab{k_908}, Source.Obs.tup{h_911, Source.Obs.tup{t_914, Source.Obs.lab{u_916}}}})], ks}}),
                        L.Obs.bytes.con(Contract.Obs.nat(h_911), Contract.Obs.bytes(t_914), ks))))))))))))
                    case Source.Obs.rfl{}:
                      (7n, {==})
                    case Source.Obs.tup{+_a_920, +_b_921}:
                      (7n, {==})
                    case Source.Obs.tup0{+_b_922}:
                      (7n, {==})
                case Source.Obs.tup0{+_b_923}:
                  (6n, {==})
            case Source.Obs.tup0{+_b_924}:
              (5n, {==})
        case Source.Obs.rfl{}:
          (3n, {==})
        case Source.Obs.tup{+_a_925, +_b_926}:
          (3n, {==})
        case Source.Obs.tup0{+_b_927}:
          (3n, {==})
    case Source.Obs.tup0{+_b_928}:
      (2n, {==})

def L.List.length(+k_929: List<&2, Nat>, +ks: List<&2, Fun.Fr>) ->
  Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.List.length(), [FM.Enc.name(k_929)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.nat(List.length(&2, Nat, k_929)), ks}}):
  match k_929:
    case Nil{}:
      (2n, {==})
    case Con{+x_930, +xs_931}:
      FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.List.length(), [FM.Enc.name(Con{x_930, xs_931})], ks}}, Fun.F.iter(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.List.length(), [FM.Enc.name(Con{x_930, xs_931})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.nat(List.length(&2, Nat, Con{x_930, xs_931})), ks}},
        FP.Reach.steps(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.List.length(), [FM.Enc.name(Con{x_930, xs_931})], ks}}),
        FP.Reach.trans(Code.prog(), Fun.F.iter(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.List.length(), [FM.Enc.name(Con{x_930, xs_931})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.nat(List.length(&2, Nat, xs_931)), Con{Fun.Fr{Code.F.List.length.k1(), [FM.Enc.name(xs_931), FM.Enc.nat(x_930), FM.Enc.name(Con{x_930, xs_931})]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.nat(List.length(&2, Nat, Con{x_930, xs_931})), ks}},
        L.List.length(xs_931, Con{Fun.Fr{Code.F.List.length.k1(), [FM.Enc.name(xs_931), FM.Enc.nat(x_930), FM.Enc.name(Con{x_930, xs_931})]}, ks}),
        FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.nat(List.length(&2, Nat, xs_931)), Con{Fun.Fr{Code.F.List.length.k1(), [FM.Enc.name(xs_931), FM.Enc.nat(x_930), FM.Enc.name(Con{x_930, xs_931})]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.nat(List.length(&2, Nat, xs_931)), Con{Fun.Fr{Code.F.List.length.k1(), [FM.Enc.name(xs_931), FM.Enc.nat(x_930), FM.Enc.name(Con{x_930, xs_931})]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.nat(List.length(&2, Nat, Con{x_930, xs_931})), ks}},
        FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.nat(List.length(&2, Nat, xs_931)), Con{Fun.Fr{Code.F.List.length.k1(), [FM.Enc.name(xs_931), FM.Enc.nat(x_930), FM.Enc.name(Con{x_930, xs_931})]}, ks}}}),
        (2n, {==}))))

def L.List.append(+xs_934: List<&2, Nat>, +ys_935: List<&2, Nat>, +ks: List<&2, Fun.Fr>) ->
  Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.List.append(), [FM.Enc.name(xs_934), FM.Enc.name(ys_935)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.name(List.append(&2, Nat, xs_934, ys_935)), ks}}):
  match xs_934:
    case Nil{}:
      (2n, {==})
    case Con{+h_936, +t_937}:
      FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.List.append(), [FM.Enc.name(Con{h_936, t_937}), FM.Enc.name(ys_935)], ks}}, Fun.F.iter(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.List.append(), [FM.Enc.name(Con{h_936, t_937}), FM.Enc.name(ys_935)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.name(List.append(&2, Nat, Con{h_936, t_937}, ys_935)), ks}},
        FP.Reach.steps(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.List.append(), [FM.Enc.name(Con{h_936, t_937}), FM.Enc.name(ys_935)], ks}}),
        FP.Reach.trans(Code.prog(), Fun.F.iter(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.List.append(), [FM.Enc.name(Con{h_936, t_937}), FM.Enc.name(ys_935)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.name(List.append(&2, Nat, t_937, ys_935)), Con{Fun.Fr{Code.F.List.append.k1(), [FM.Enc.name(t_937), FM.Enc.nat(h_936), FM.Enc.name(Con{h_936, t_937}), FM.Enc.name(ys_935)]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.name(List.append(&2, Nat, Con{h_936, t_937}, ys_935)), ks}},
        L.List.append(t_937, ys_935, Con{Fun.Fr{Code.F.List.append.k1(), [FM.Enc.name(t_937), FM.Enc.nat(h_936), FM.Enc.name(Con{h_936, t_937}), FM.Enc.name(ys_935)]}, ks}),
        FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.name(List.append(&2, Nat, t_937, ys_935)), Con{Fun.Fr{Code.F.List.append.k1(), [FM.Enc.name(t_937), FM.Enc.nat(h_936), FM.Enc.name(Con{h_936, t_937}), FM.Enc.name(ys_935)]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.name(List.append(&2, Nat, t_937, ys_935)), Con{Fun.Fr{Code.F.List.append.k1(), [FM.Enc.name(t_937), FM.Enc.nat(h_936), FM.Enc.name(Con{h_936, t_937}), FM.Enc.name(ys_935)]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.name(List.append(&2, Nat, Con{h_936, t_937}, ys_935)), ks}},
        FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.name(List.append(&2, Nat, t_937, ys_935)), Con{Fun.Fr{Code.F.List.append.k1(), [FM.Enc.name(t_937), FM.Enc.nat(h_936), FM.Enc.name(Con{h_936, t_937}), FM.Enc.name(ys_935)]}, ks}}}),
        (2n, {==}))))

def L.Nat.add(+a_939: Nat, +b_940: Nat, +ks: List<&2, Fun.Fr>) ->
  Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Nat.add(), [FM.Enc.nat(a_939), FM.Enc.nat(b_940)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.nat(Nat.add(a_939, b_940)), ks}}):
  match a_939:
    case 0n:
      (2n, {==})
    case 1n+p_941:
      FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Nat.add(), [FM.Enc.nat(1n+p_941), FM.Enc.nat(b_940)], ks}}, Fun.F.iter(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Nat.add(), [FM.Enc.nat(1n+p_941), FM.Enc.nat(b_940)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.nat(Nat.add(1n+p_941, b_940)), ks}},
        FP.Reach.steps(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Nat.add(), [FM.Enc.nat(1n+p_941), FM.Enc.nat(b_940)], ks}}),
        FP.Reach.trans(Code.prog(), Fun.F.iter(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Nat.add(), [FM.Enc.nat(1n+p_941), FM.Enc.nat(b_940)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.nat(Nat.add(p_941, b_940)), Con{Fun.Fr{Code.F.Nat.add.k1(), [Fun.V.num(p_941), FM.Enc.nat(1n+p_941), FM.Enc.nat(b_940)]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.nat(Nat.add(1n+p_941, b_940)), ks}},
        L.Nat.add(p_941, b_940, Con{Fun.Fr{Code.F.Nat.add.k1(), [Fun.V.num(p_941), FM.Enc.nat(1n+p_941), FM.Enc.nat(b_940)]}, ks}),
        FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.nat(Nat.add(p_941, b_940)), Con{Fun.Fr{Code.F.Nat.add.k1(), [Fun.V.num(p_941), FM.Enc.nat(1n+p_941), FM.Enc.nat(b_940)]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.nat(Nat.add(p_941, b_940)), Con{Fun.Fr{Code.F.Nat.add.k1(), [Fun.V.num(p_941), FM.Enc.nat(1n+p_941), FM.Enc.nat(b_940)]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.nat(Nat.add(1n+p_941, b_940)), ks}},
        FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.nat(Nat.add(p_941, b_940)), Con{Fun.Fr{Code.F.Nat.add.k1(), [Fun.V.num(p_941), FM.Enc.nat(1n+p_941), FM.Enc.nat(b_940)]}, ks}}}),
        (2n, {==}))))

def L.DM.div(+n_944: Nat, +m_945: Nat, +d_946: Nat, +r_947: Nat, +ks: List<&2, Fun.Fr>) ->
  Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.DM.div(), [FM.Enc.nat(n_944), FM.Enc.nat(m_945), FM.Enc.nat(d_946), FM.Enc.nat(r_947)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.nat(Pair.fst(Nat, Nat, Nat.divmod.go(n_944, m_945, d_946, r_947))), ks}}):
  match n_944:
    case 0n:
      (2n, {==})
    case 1n+np_948:
      match m_945:
        case 0n:
          FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.DM.div(), [FM.Enc.nat(1n+np_948), FM.Enc.nat(0n), FM.Enc.nat(d_946), FM.Enc.nat(r_947)], ks}}, Fun.F.iter(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.DM.div(), [FM.Enc.nat(1n+np_948), FM.Enc.nat(0n), FM.Enc.nat(d_946), FM.Enc.nat(r_947)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.nat(Pair.fst(Nat, Nat, Nat.divmod.go(1n+np_948, 0n, d_946, r_947))), ks}},
            FP.Reach.steps(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.DM.div(), [FM.Enc.nat(1n+np_948), FM.Enc.nat(0n), FM.Enc.nat(d_946), FM.Enc.nat(r_947)], ks}}),
            L.DM.div(np_948, r_947, 1n+d_946, 0n, ks))
        case 1n+mp_950:
          FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.DM.div(), [FM.Enc.nat(1n+np_948), FM.Enc.nat(1n+mp_950), FM.Enc.nat(d_946), FM.Enc.nat(r_947)], ks}}, Fun.F.iter(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.DM.div(), [FM.Enc.nat(1n+np_948), FM.Enc.nat(1n+mp_950), FM.Enc.nat(d_946), FM.Enc.nat(r_947)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.nat(Pair.fst(Nat, Nat, Nat.divmod.go(1n+np_948, 1n+mp_950, d_946, r_947))), ks}},
            FP.Reach.steps(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.DM.div(), [FM.Enc.nat(1n+np_948), FM.Enc.nat(1n+mp_950), FM.Enc.nat(d_946), FM.Enc.nat(r_947)], ks}}),
            L.DM.div(np_948, mp_950, d_946, 1n+r_947, ks))

def L.Nat.div128(+n_952: Nat, +ks: List<&2, Fun.Fr>) ->
  Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Nat.div128(), [FM.Enc.nat(n_952)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.nat(Nat.div(n_952, 128n)), ks}}):
  FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Nat.div128(), [FM.Enc.nat(n_952)], ks}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Nat.div128(), [FM.Enc.nat(n_952)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.nat(Nat.div(n_952, 128n)), ks}},
    FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Nat.div128(), [FM.Enc.nat(n_952)], ks}}),
    L.DM.div(n_952, 127n, 0n, 0n, ks))

def L.DM.mod(+n_953: Nat, +m_954: Nat, +d_955: Nat, +r_956: Nat, +ks: List<&2, Fun.Fr>) ->
  Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.DM.mod(), [FM.Enc.nat(n_953), FM.Enc.nat(m_954), FM.Enc.nat(d_955), FM.Enc.nat(r_956)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.nat(Pair.snd(Nat, Nat, Nat.divmod.go(n_953, m_954, d_955, r_956))), ks}}):
  match n_953:
    case 0n:
      (2n, {==})
    case 1n+np_957:
      match m_954:
        case 0n:
          FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.DM.mod(), [FM.Enc.nat(1n+np_957), FM.Enc.nat(0n), FM.Enc.nat(d_955), FM.Enc.nat(r_956)], ks}}, Fun.F.iter(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.DM.mod(), [FM.Enc.nat(1n+np_957), FM.Enc.nat(0n), FM.Enc.nat(d_955), FM.Enc.nat(r_956)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.nat(Pair.snd(Nat, Nat, Nat.divmod.go(1n+np_957, 0n, d_955, r_956))), ks}},
            FP.Reach.steps(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.DM.mod(), [FM.Enc.nat(1n+np_957), FM.Enc.nat(0n), FM.Enc.nat(d_955), FM.Enc.nat(r_956)], ks}}),
            L.DM.mod(np_957, r_956, 1n+d_955, 0n, ks))
        case 1n+mp_959:
          FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.DM.mod(), [FM.Enc.nat(1n+np_957), FM.Enc.nat(1n+mp_959), FM.Enc.nat(d_955), FM.Enc.nat(r_956)], ks}}, Fun.F.iter(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.DM.mod(), [FM.Enc.nat(1n+np_957), FM.Enc.nat(1n+mp_959), FM.Enc.nat(d_955), FM.Enc.nat(r_956)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.nat(Pair.snd(Nat, Nat, Nat.divmod.go(1n+np_957, 1n+mp_959, d_955, r_956))), ks}},
            FP.Reach.steps(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.DM.mod(), [FM.Enc.nat(1n+np_957), FM.Enc.nat(1n+mp_959), FM.Enc.nat(d_955), FM.Enc.nat(r_956)], ks}}),
            L.DM.mod(np_957, mp_959, d_955, 1n+r_956, ks))

def L.Nat.mod128(+n_961: Nat, +ks: List<&2, Fun.Fr>) ->
  Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Nat.mod128(), [FM.Enc.nat(n_961)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.nat(Nat.mod(n_961, 128n)), ks}}):
  FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Nat.mod128(), [FM.Enc.nat(n_961)], ks}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Nat.mod128(), [FM.Enc.nat(n_961)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.nat(Nat.mod(n_961, 128n)), ks}},
    FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Nat.mod128(), [FM.Enc.nat(n_961)], ks}}),
    L.DM.mod(n_961, 127n, 0n, 0n, ks))

def L.Leb.go(+f_962: Nat, +n_963: Nat, +ks: List<&2, Fun.Fr>) ->
  Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Leb.go(), [FM.Enc.nat(f_962), FM.Enc.nat(n_963)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.name(Wasm.Leb.nat.go(f_962, n_963)), ks}}):
  match f_962:
    case 0n:
      (2n, {==})
    case 1n+g_964:
      FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Leb.go(), [FM.Enc.nat(1n+g_964), FM.Enc.nat(n_963)], ks}}, Fun.F.iter(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Leb.go(), [FM.Enc.nat(1n+g_964), FM.Enc.nat(n_963)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.name(Wasm.Leb.nat.go(1n+g_964, n_963)), ks}},
        FP.Reach.steps(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Leb.go(), [FM.Enc.nat(1n+g_964), FM.Enc.nat(n_963)], ks}}),
        FP.Reach.trans(Code.prog(), Fun.F.iter(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Leb.go(), [FM.Enc.nat(1n+g_964), FM.Enc.nat(n_963)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.nat(Nat.div(n_963, 128n)), Con{Fun.Fr{Code.F.Leb.go.k1(), [Fun.V.num(g_964), FM.Enc.nat(1n+g_964), FM.Enc.nat(n_963)]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.name(Wasm.Leb.nat.go(1n+g_964, n_963)), ks}},
        L.Nat.div128(n_963, Con{Fun.Fr{Code.F.Leb.go.k1(), [Fun.V.num(g_964), FM.Enc.nat(1n+g_964), FM.Enc.nat(n_963)]}, ks}),
        FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.nat(Nat.div(n_963, 128n)), Con{Fun.Fr{Code.F.Leb.go.k1(), [Fun.V.num(g_964), FM.Enc.nat(1n+g_964), FM.Enc.nat(n_963)]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.nat(Nat.div(n_963, 128n)), Con{Fun.Fr{Code.F.Leb.go.k1(), [Fun.V.num(g_964), FM.Enc.nat(1n+g_964), FM.Enc.nat(n_963)]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.name(Wasm.Leb.nat.go(1n+g_964, n_963)), ks}},
        FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.nat(Nat.div(n_963, 128n)), Con{Fun.Fr{Code.F.Leb.go.k1(), [Fun.V.num(g_964), FM.Enc.nat(1n+g_964), FM.Enc.nat(n_963)]}, ks}}}),
        FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Leb.go.k1(), [FM.Enc.nat(Nat.div(n_963, 128n)), Fun.V.num(g_964), FM.Enc.nat(1n+g_964), FM.Enc.nat(n_963)], ks}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Leb.go.k1(), [FM.Enc.nat(Nat.div(n_963, 128n)), Fun.V.num(g_964), FM.Enc.nat(1n+g_964), FM.Enc.nat(n_963)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.name(Wasm.Leb.nat.of(Nat.div(n_963, 128n), Nat.mod(n_963, 128n), m => Wasm.Leb.nat.go(g_964, m))), ks}},
        FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Leb.go.k1(), [FM.Enc.nat(Nat.div(n_963, 128n)), Fun.V.num(g_964), FM.Enc.nat(1n+g_964), FM.Enc.nat(n_963)], ks}}),
        FP.Reach.trans(Code.prog(), Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Leb.go.k1(), [FM.Enc.nat(Nat.div(n_963, 128n)), Fun.V.num(g_964), FM.Enc.nat(1n+g_964), FM.Enc.nat(n_963)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.nat(Nat.mod(n_963, 128n)), Con{Fun.Fr{Code.F.Leb.go.k2(), [FM.Enc.nat(Nat.div(n_963, 128n)), Fun.V.num(g_964), FM.Enc.nat(1n+g_964), FM.Enc.nat(n_963)]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.name(Wasm.Leb.nat.of(Nat.div(n_963, 128n), Nat.mod(n_963, 128n), m => Wasm.Leb.nat.go(g_964, m))), ks}},
        L.Nat.mod128(n_963, Con{Fun.Fr{Code.F.Leb.go.k2(), [FM.Enc.nat(Nat.div(n_963, 128n)), Fun.V.num(g_964), FM.Enc.nat(1n+g_964), FM.Enc.nat(n_963)]}, ks}),
        FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.nat(Nat.mod(n_963, 128n)), Con{Fun.Fr{Code.F.Leb.go.k2(), [FM.Enc.nat(Nat.div(n_963, 128n)), Fun.V.num(g_964), FM.Enc.nat(1n+g_964), FM.Enc.nat(n_963)]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.nat(Nat.mod(n_963, 128n)), Con{Fun.Fr{Code.F.Leb.go.k2(), [FM.Enc.nat(Nat.div(n_963, 128n)), Fun.V.num(g_964), FM.Enc.nat(1n+g_964), FM.Enc.nat(n_963)]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.name(Wasm.Leb.nat.of(Nat.div(n_963, 128n), Nat.mod(n_963, 128n), m => Wasm.Leb.nat.go(g_964, m))), ks}},
        FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.nat(Nat.mod(n_963, 128n)), Con{Fun.Fr{Code.F.Leb.go.k2(), [FM.Enc.nat(Nat.div(n_963, 128n)), Fun.V.num(g_964), FM.Enc.nat(1n+g_964), FM.Enc.nat(n_963)]}, ks}}}),
        Elim.Nat(Nat.div(n_963, 128n), m48 => Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Leb.go.k2(), [FM.Enc.nat(Nat.mod(n_963, 128n)), FM.Enc.nat(m48), Fun.V.num(g_964), FM.Enc.nat(1n+g_964), FM.Enc.nat(n_963)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.name(Wasm.Leb.nat.of(m48, Nat.mod(n_963, 128n), m => Wasm.Leb.nat.go(g_964, m))), ks}}),
        (3n, {==}),
        +p_967 => FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Leb.go.k2(), [FM.Enc.nat(Nat.mod(n_963, 128n)), FM.Enc.nat(1n+p_967), Fun.V.num(g_964), FM.Enc.nat(1n+g_964), FM.Enc.nat(n_963)], ks}}, Fun.F.iter(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Leb.go.k2(), [FM.Enc.nat(Nat.mod(n_963, 128n)), FM.Enc.nat(1n+p_967), Fun.V.num(g_964), FM.Enc.nat(1n+g_964), FM.Enc.nat(n_963)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.name(Wasm.Leb.nat.of(1n+p_967, Nat.mod(n_963, 128n), m => Wasm.Leb.nat.go(g_964, m))), ks}},
        FP.Reach.steps(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Leb.go.k2(), [FM.Enc.nat(Nat.mod(n_963, 128n)), FM.Enc.nat(1n+p_967), Fun.V.num(g_964), FM.Enc.nat(1n+g_964), FM.Enc.nat(n_963)], ks}}),
        FP.Reach.trans(Code.prog(), Fun.F.iter(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Leb.go.k2(), [FM.Enc.nat(Nat.mod(n_963, 128n)), FM.Enc.nat(1n+p_967), Fun.V.num(g_964), FM.Enc.nat(1n+g_964), FM.Enc.nat(n_963)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.nat(Nat.add(Nat.mod(n_963, 128n), 128n)), Con{Fun.Fr{Code.F.Leb.go.k3(), [Fun.V.num(p_967), FM.Enc.nat(Nat.mod(n_963, 128n)), FM.Enc.nat(1n+p_967), Fun.V.num(g_964), FM.Enc.nat(1n+g_964), FM.Enc.nat(n_963)]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.name(Wasm.Leb.nat.of(1n+p_967, Nat.mod(n_963, 128n), m => Wasm.Leb.nat.go(g_964, m))), ks}},
        L.Nat.add(Nat.mod(n_963, 128n), 128n, Con{Fun.Fr{Code.F.Leb.go.k3(), [Fun.V.num(p_967), FM.Enc.nat(Nat.mod(n_963, 128n)), FM.Enc.nat(1n+p_967), Fun.V.num(g_964), FM.Enc.nat(1n+g_964), FM.Enc.nat(n_963)]}, ks}),
        FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.nat(Nat.add(Nat.mod(n_963, 128n), 128n)), Con{Fun.Fr{Code.F.Leb.go.k3(), [Fun.V.num(p_967), FM.Enc.nat(Nat.mod(n_963, 128n)), FM.Enc.nat(1n+p_967), Fun.V.num(g_964), FM.Enc.nat(1n+g_964), FM.Enc.nat(n_963)]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.nat(Nat.add(Nat.mod(n_963, 128n), 128n)), Con{Fun.Fr{Code.F.Leb.go.k3(), [Fun.V.num(p_967), FM.Enc.nat(Nat.mod(n_963, 128n)), FM.Enc.nat(1n+p_967), Fun.V.num(g_964), FM.Enc.nat(1n+g_964), FM.Enc.nat(n_963)]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.name(Wasm.Leb.nat.of(1n+p_967, Nat.mod(n_963, 128n), m => Wasm.Leb.nat.go(g_964, m))), ks}},
        FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.nat(Nat.add(Nat.mod(n_963, 128n), 128n)), Con{Fun.Fr{Code.F.Leb.go.k3(), [Fun.V.num(p_967), FM.Enc.nat(Nat.mod(n_963, 128n)), FM.Enc.nat(1n+p_967), Fun.V.num(g_964), FM.Enc.nat(1n+g_964), FM.Enc.nat(n_963)]}, ks}}}),
        FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Leb.go.k3(), [FM.Enc.nat(Nat.add(Nat.mod(n_963, 128n), 128n)), Fun.V.num(p_967), FM.Enc.nat(Nat.mod(n_963, 128n)), FM.Enc.nat(1n+p_967), Fun.V.num(g_964), FM.Enc.nat(1n+g_964), FM.Enc.nat(n_963)], ks}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Leb.go.k3(), [FM.Enc.nat(Nat.add(Nat.mod(n_963, 128n), 128n)), Fun.V.num(p_967), FM.Enc.nat(Nat.mod(n_963, 128n)), FM.Enc.nat(1n+p_967), Fun.V.num(g_964), FM.Enc.nat(1n+g_964), FM.Enc.nat(n_963)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.name(Con{Nat.add(Nat.mod(n_963, 128n), 128n), Wasm.Leb.nat.go(g_964, 1n+p_967)}), ks}},
        FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Leb.go.k3(), [FM.Enc.nat(Nat.add(Nat.mod(n_963, 128n), 128n)), Fun.V.num(p_967), FM.Enc.nat(Nat.mod(n_963, 128n)), FM.Enc.nat(1n+p_967), Fun.V.num(g_964), FM.Enc.nat(1n+g_964), FM.Enc.nat(n_963)], ks}}),
        FP.Reach.trans(Code.prog(), Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Leb.go.k3(), [FM.Enc.nat(Nat.add(Nat.mod(n_963, 128n), 128n)), Fun.V.num(p_967), FM.Enc.nat(Nat.mod(n_963, 128n)), FM.Enc.nat(1n+p_967), Fun.V.num(g_964), FM.Enc.nat(1n+g_964), FM.Enc.nat(n_963)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.name(Wasm.Leb.nat.go(g_964, 1n+p_967)), Con{Fun.Fr{Code.F.Leb.go.k4(), [FM.Enc.nat(Nat.add(Nat.mod(n_963, 128n), 128n)), Fun.V.num(p_967), FM.Enc.nat(Nat.mod(n_963, 128n)), FM.Enc.nat(1n+p_967), Fun.V.num(g_964), FM.Enc.nat(1n+g_964), FM.Enc.nat(n_963)]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.name(Con{Nat.add(Nat.mod(n_963, 128n), 128n), Wasm.Leb.nat.go(g_964, 1n+p_967)}), ks}},
        L.Leb.go(g_964, 1n+p_967, Con{Fun.Fr{Code.F.Leb.go.k4(), [FM.Enc.nat(Nat.add(Nat.mod(n_963, 128n), 128n)), Fun.V.num(p_967), FM.Enc.nat(Nat.mod(n_963, 128n)), FM.Enc.nat(1n+p_967), Fun.V.num(g_964), FM.Enc.nat(1n+g_964), FM.Enc.nat(n_963)]}, ks}),
        FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.name(Wasm.Leb.nat.go(g_964, 1n+p_967)), Con{Fun.Fr{Code.F.Leb.go.k4(), [FM.Enc.nat(Nat.add(Nat.mod(n_963, 128n), 128n)), Fun.V.num(p_967), FM.Enc.nat(Nat.mod(n_963, 128n)), FM.Enc.nat(1n+p_967), Fun.V.num(g_964), FM.Enc.nat(1n+g_964), FM.Enc.nat(n_963)]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.name(Wasm.Leb.nat.go(g_964, 1n+p_967)), Con{Fun.Fr{Code.F.Leb.go.k4(), [FM.Enc.nat(Nat.add(Nat.mod(n_963, 128n), 128n)), Fun.V.num(p_967), FM.Enc.nat(Nat.mod(n_963, 128n)), FM.Enc.nat(1n+p_967), Fun.V.num(g_964), FM.Enc.nat(1n+g_964), FM.Enc.nat(n_963)]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.name(Con{Nat.add(Nat.mod(n_963, 128n), 128n), Wasm.Leb.nat.go(g_964, 1n+p_967)}), ks}},
        FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.name(Wasm.Leb.nat.go(g_964, 1n+p_967)), Con{Fun.Fr{Code.F.Leb.go.k4(), [FM.Enc.nat(Nat.add(Nat.mod(n_963, 128n), 128n)), Fun.V.num(p_967), FM.Enc.nat(Nat.mod(n_963, 128n)), FM.Enc.nat(1n+p_967), Fun.V.num(g_964), FM.Enc.nat(1n+g_964), FM.Enc.nat(n_963)]}, ks}}}),
        (2n, {==}))))))))))))))

def L.Leb.nat(+n_970: Nat, +ks: List<&2, Fun.Fr>) ->
  Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Leb.nat(), [FM.Enc.nat(n_970)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.name(Wasm.Leb.nat(n_970)), ks}}):
  FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Leb.nat(), [FM.Enc.nat(n_970)], ks}}, Fun.F.iter(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Leb.nat(), [FM.Enc.nat(n_970)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.name(Wasm.Leb.nat(n_970)), ks}},
    FP.Reach.steps(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Leb.nat(), [FM.Enc.nat(n_970)], ks}}),
    L.Leb.go(1n+n_970, n_970, ks))

def L.Obs.write(+o_972: Source.Obs, +ks: List<&2, Fun.Fr>) ->
  Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.write(), [FM.Enc.obs(o_972)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.name(Contract.Obs.write(o_972)), ks}}):
  match o_972:
    case Source.Obs.lab{+k_973}:
      FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.write(), [FM.Enc.obs(Source.Obs.lab{k_973})], ks}}, Fun.F.iter(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.write(), [FM.Enc.obs(Source.Obs.lab{k_973})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.name(Contract.Obs.write(Source.Obs.lab{k_973})), ks}},
        FP.Reach.steps(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.write(), [FM.Enc.obs(Source.Obs.lab{k_973})], ks}}),
        FP.Reach.trans(Code.prog(), Fun.F.iter(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.write(), [FM.Enc.obs(Source.Obs.lab{k_973})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.nat(List.length(&2, Nat, k_973)), Con{Fun.Fr{Code.F.Obs.write.k1(), [Fun.V.z{}, FM.Enc.name(k_973), FM.Enc.obs(Source.Obs.lab{k_973})]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.name(Contract.Obs.write(Source.Obs.lab{k_973})), ks}},
        L.List.length(k_973, Con{Fun.Fr{Code.F.Obs.write.k1(), [Fun.V.z{}, FM.Enc.name(k_973), FM.Enc.obs(Source.Obs.lab{k_973})]}, ks}),
        FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.nat(List.length(&2, Nat, k_973)), Con{Fun.Fr{Code.F.Obs.write.k1(), [Fun.V.z{}, FM.Enc.name(k_973), FM.Enc.obs(Source.Obs.lab{k_973})]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.nat(List.length(&2, Nat, k_973)), Con{Fun.Fr{Code.F.Obs.write.k1(), [Fun.V.z{}, FM.Enc.name(k_973), FM.Enc.obs(Source.Obs.lab{k_973})]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.name(Contract.Obs.write(Source.Obs.lab{k_973})), ks}},
        FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.nat(List.length(&2, Nat, k_973)), Con{Fun.Fr{Code.F.Obs.write.k1(), [Fun.V.z{}, FM.Enc.name(k_973), FM.Enc.obs(Source.Obs.lab{k_973})]}, ks}}}),
        FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.write.k1(), [FM.Enc.nat(List.length(&2, Nat, k_973)), Fun.V.z{}, FM.Enc.name(k_973), FM.Enc.obs(Source.Obs.lab{k_973})], ks}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.write.k1(), [FM.Enc.nat(List.length(&2, Nat, k_973)), Fun.V.z{}, FM.Enc.name(k_973), FM.Enc.obs(Source.Obs.lab{k_973})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.name(Con{0n, List.append(&2, Nat, Wasm.Leb.nat(List.length(&2, Nat, k_973)), k_973)}), ks}},
        FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.write.k1(), [FM.Enc.nat(List.length(&2, Nat, k_973)), Fun.V.z{}, FM.Enc.name(k_973), FM.Enc.obs(Source.Obs.lab{k_973})], ks}}),
        FP.Reach.trans(Code.prog(), Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.write.k1(), [FM.Enc.nat(List.length(&2, Nat, k_973)), Fun.V.z{}, FM.Enc.name(k_973), FM.Enc.obs(Source.Obs.lab{k_973})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.name(Wasm.Leb.nat(List.length(&2, Nat, k_973))), Con{Fun.Fr{Code.F.Obs.write.k2(), [FM.Enc.nat(List.length(&2, Nat, k_973)), Fun.V.z{}, FM.Enc.name(k_973), FM.Enc.obs(Source.Obs.lab{k_973})]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.name(Con{0n, List.append(&2, Nat, Wasm.Leb.nat(List.length(&2, Nat, k_973)), k_973)}), ks}},
        L.Leb.nat(List.length(&2, Nat, k_973), Con{Fun.Fr{Code.F.Obs.write.k2(), [FM.Enc.nat(List.length(&2, Nat, k_973)), Fun.V.z{}, FM.Enc.name(k_973), FM.Enc.obs(Source.Obs.lab{k_973})]}, ks}),
        FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.name(Wasm.Leb.nat(List.length(&2, Nat, k_973))), Con{Fun.Fr{Code.F.Obs.write.k2(), [FM.Enc.nat(List.length(&2, Nat, k_973)), Fun.V.z{}, FM.Enc.name(k_973), FM.Enc.obs(Source.Obs.lab{k_973})]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.name(Wasm.Leb.nat(List.length(&2, Nat, k_973))), Con{Fun.Fr{Code.F.Obs.write.k2(), [FM.Enc.nat(List.length(&2, Nat, k_973)), Fun.V.z{}, FM.Enc.name(k_973), FM.Enc.obs(Source.Obs.lab{k_973})]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.name(Con{0n, List.append(&2, Nat, Wasm.Leb.nat(List.length(&2, Nat, k_973)), k_973)}), ks}},
        FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.name(Wasm.Leb.nat(List.length(&2, Nat, k_973))), Con{Fun.Fr{Code.F.Obs.write.k2(), [FM.Enc.nat(List.length(&2, Nat, k_973)), Fun.V.z{}, FM.Enc.name(k_973), FM.Enc.obs(Source.Obs.lab{k_973})]}, ks}}}),
        FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.write.k2(), [FM.Enc.name(Wasm.Leb.nat(List.length(&2, Nat, k_973))), FM.Enc.nat(List.length(&2, Nat, k_973)), Fun.V.z{}, FM.Enc.name(k_973), FM.Enc.obs(Source.Obs.lab{k_973})], ks}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.write.k2(), [FM.Enc.name(Wasm.Leb.nat(List.length(&2, Nat, k_973))), FM.Enc.nat(List.length(&2, Nat, k_973)), Fun.V.z{}, FM.Enc.name(k_973), FM.Enc.obs(Source.Obs.lab{k_973})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.name(Con{0n, List.append(&2, Nat, Wasm.Leb.nat(List.length(&2, Nat, k_973)), k_973)}), ks}},
        FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.write.k2(), [FM.Enc.name(Wasm.Leb.nat(List.length(&2, Nat, k_973))), FM.Enc.nat(List.length(&2, Nat, k_973)), Fun.V.z{}, FM.Enc.name(k_973), FM.Enc.obs(Source.Obs.lab{k_973})], ks}}),
        FP.Reach.trans(Code.prog(), Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.write.k2(), [FM.Enc.name(Wasm.Leb.nat(List.length(&2, Nat, k_973))), FM.Enc.nat(List.length(&2, Nat, k_973)), Fun.V.z{}, FM.Enc.name(k_973), FM.Enc.obs(Source.Obs.lab{k_973})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.name(List.append(&2, Nat, Wasm.Leb.nat(List.length(&2, Nat, k_973)), k_973)), Con{Fun.Fr{Code.F.Obs.write.k3(), [FM.Enc.name(Wasm.Leb.nat(List.length(&2, Nat, k_973))), FM.Enc.nat(List.length(&2, Nat, k_973)), Fun.V.z{}, FM.Enc.name(k_973), FM.Enc.obs(Source.Obs.lab{k_973})]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.name(Con{0n, List.append(&2, Nat, Wasm.Leb.nat(List.length(&2, Nat, k_973)), k_973)}), ks}},
        L.List.append(Wasm.Leb.nat(List.length(&2, Nat, k_973)), k_973, Con{Fun.Fr{Code.F.Obs.write.k3(), [FM.Enc.name(Wasm.Leb.nat(List.length(&2, Nat, k_973))), FM.Enc.nat(List.length(&2, Nat, k_973)), Fun.V.z{}, FM.Enc.name(k_973), FM.Enc.obs(Source.Obs.lab{k_973})]}, ks}),
        FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.name(List.append(&2, Nat, Wasm.Leb.nat(List.length(&2, Nat, k_973)), k_973)), Con{Fun.Fr{Code.F.Obs.write.k3(), [FM.Enc.name(Wasm.Leb.nat(List.length(&2, Nat, k_973))), FM.Enc.nat(List.length(&2, Nat, k_973)), Fun.V.z{}, FM.Enc.name(k_973), FM.Enc.obs(Source.Obs.lab{k_973})]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.name(List.append(&2, Nat, Wasm.Leb.nat(List.length(&2, Nat, k_973)), k_973)), Con{Fun.Fr{Code.F.Obs.write.k3(), [FM.Enc.name(Wasm.Leb.nat(List.length(&2, Nat, k_973))), FM.Enc.nat(List.length(&2, Nat, k_973)), Fun.V.z{}, FM.Enc.name(k_973), FM.Enc.obs(Source.Obs.lab{k_973})]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.name(Con{0n, List.append(&2, Nat, Wasm.Leb.nat(List.length(&2, Nat, k_973)), k_973)}), ks}},
        FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.name(List.append(&2, Nat, Wasm.Leb.nat(List.length(&2, Nat, k_973)), k_973)), Con{Fun.Fr{Code.F.Obs.write.k3(), [FM.Enc.name(Wasm.Leb.nat(List.length(&2, Nat, k_973))), FM.Enc.nat(List.length(&2, Nat, k_973)), Fun.V.z{}, FM.Enc.name(k_973), FM.Enc.obs(Source.Obs.lab{k_973})]}, ks}}}),
        (2n, {==}))))))))))
    case Source.Obs.rfl{}:
      (4n, {==})
    case Source.Obs.tup{+a_977, +b_978}:
      FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.write(), [FM.Enc.obs(Source.Obs.tup{a_977, b_978})], ks}}, Fun.F.iter(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.write(), [FM.Enc.obs(Source.Obs.tup{a_977, b_978})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.name(Contract.Obs.write(Source.Obs.tup{a_977, b_978})), ks}},
        FP.Reach.steps(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.write(), [FM.Enc.obs(Source.Obs.tup{a_977, b_978})], ks}}),
        FP.Reach.trans(Code.prog(), Fun.F.iter(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.write(), [FM.Enc.obs(Source.Obs.tup{a_977, b_978})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.name(Contract.Obs.write(a_977)), Con{Fun.Fr{Code.F.Obs.write.k4(), [FM.Enc.obs(b_978), FM.Enc.obs(a_977), FM.Enc.obs(Source.Obs.tup{a_977, b_978})]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.name(Contract.Obs.write(Source.Obs.tup{a_977, b_978})), ks}},
        L.Obs.write(a_977, Con{Fun.Fr{Code.F.Obs.write.k4(), [FM.Enc.obs(b_978), FM.Enc.obs(a_977), FM.Enc.obs(Source.Obs.tup{a_977, b_978})]}, ks}),
        FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.name(Contract.Obs.write(a_977)), Con{Fun.Fr{Code.F.Obs.write.k4(), [FM.Enc.obs(b_978), FM.Enc.obs(a_977), FM.Enc.obs(Source.Obs.tup{a_977, b_978})]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.name(Contract.Obs.write(a_977)), Con{Fun.Fr{Code.F.Obs.write.k4(), [FM.Enc.obs(b_978), FM.Enc.obs(a_977), FM.Enc.obs(Source.Obs.tup{a_977, b_978})]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.name(Contract.Obs.write(Source.Obs.tup{a_977, b_978})), ks}},
        FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.name(Contract.Obs.write(a_977)), Con{Fun.Fr{Code.F.Obs.write.k4(), [FM.Enc.obs(b_978), FM.Enc.obs(a_977), FM.Enc.obs(Source.Obs.tup{a_977, b_978})]}, ks}}}),
        FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.write.k4(), [FM.Enc.name(Contract.Obs.write(a_977)), FM.Enc.obs(b_978), FM.Enc.obs(a_977), FM.Enc.obs(Source.Obs.tup{a_977, b_978})], ks}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.write.k4(), [FM.Enc.name(Contract.Obs.write(a_977)), FM.Enc.obs(b_978), FM.Enc.obs(a_977), FM.Enc.obs(Source.Obs.tup{a_977, b_978})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.name(Con{2n, List.append(&2, Nat, Contract.Obs.write(a_977), Contract.Obs.write(b_978))}), ks}},
        FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.write.k4(), [FM.Enc.name(Contract.Obs.write(a_977)), FM.Enc.obs(b_978), FM.Enc.obs(a_977), FM.Enc.obs(Source.Obs.tup{a_977, b_978})], ks}}),
        FP.Reach.trans(Code.prog(), Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.write.k4(), [FM.Enc.name(Contract.Obs.write(a_977)), FM.Enc.obs(b_978), FM.Enc.obs(a_977), FM.Enc.obs(Source.Obs.tup{a_977, b_978})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.name(Contract.Obs.write(b_978)), Con{Fun.Fr{Code.F.Obs.write.k5(), [FM.Enc.name(Contract.Obs.write(a_977)), FM.Enc.obs(b_978), FM.Enc.obs(a_977), FM.Enc.obs(Source.Obs.tup{a_977, b_978})]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.name(Con{2n, List.append(&2, Nat, Contract.Obs.write(a_977), Contract.Obs.write(b_978))}), ks}},
        L.Obs.write(b_978, Con{Fun.Fr{Code.F.Obs.write.k5(), [FM.Enc.name(Contract.Obs.write(a_977)), FM.Enc.obs(b_978), FM.Enc.obs(a_977), FM.Enc.obs(Source.Obs.tup{a_977, b_978})]}, ks}),
        FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.name(Contract.Obs.write(b_978)), Con{Fun.Fr{Code.F.Obs.write.k5(), [FM.Enc.name(Contract.Obs.write(a_977)), FM.Enc.obs(b_978), FM.Enc.obs(a_977), FM.Enc.obs(Source.Obs.tup{a_977, b_978})]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.name(Contract.Obs.write(b_978)), Con{Fun.Fr{Code.F.Obs.write.k5(), [FM.Enc.name(Contract.Obs.write(a_977)), FM.Enc.obs(b_978), FM.Enc.obs(a_977), FM.Enc.obs(Source.Obs.tup{a_977, b_978})]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.name(Con{2n, List.append(&2, Nat, Contract.Obs.write(a_977), Contract.Obs.write(b_978))}), ks}},
        FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.name(Contract.Obs.write(b_978)), Con{Fun.Fr{Code.F.Obs.write.k5(), [FM.Enc.name(Contract.Obs.write(a_977)), FM.Enc.obs(b_978), FM.Enc.obs(a_977), FM.Enc.obs(Source.Obs.tup{a_977, b_978})]}, ks}}}),
        FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.write.k5(), [FM.Enc.name(Contract.Obs.write(b_978)), FM.Enc.name(Contract.Obs.write(a_977)), FM.Enc.obs(b_978), FM.Enc.obs(a_977), FM.Enc.obs(Source.Obs.tup{a_977, b_978})], ks}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.write.k5(), [FM.Enc.name(Contract.Obs.write(b_978)), FM.Enc.name(Contract.Obs.write(a_977)), FM.Enc.obs(b_978), FM.Enc.obs(a_977), FM.Enc.obs(Source.Obs.tup{a_977, b_978})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.name(Con{2n, List.append(&2, Nat, Contract.Obs.write(a_977), Contract.Obs.write(b_978))}), ks}},
        FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.write.k5(), [FM.Enc.name(Contract.Obs.write(b_978)), FM.Enc.name(Contract.Obs.write(a_977)), FM.Enc.obs(b_978), FM.Enc.obs(a_977), FM.Enc.obs(Source.Obs.tup{a_977, b_978})], ks}}),
        FP.Reach.trans(Code.prog(), Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.write.k5(), [FM.Enc.name(Contract.Obs.write(b_978)), FM.Enc.name(Contract.Obs.write(a_977)), FM.Enc.obs(b_978), FM.Enc.obs(a_977), FM.Enc.obs(Source.Obs.tup{a_977, b_978})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.name(List.append(&2, Nat, Contract.Obs.write(a_977), Contract.Obs.write(b_978))), Con{Fun.Fr{Code.F.Obs.write.k6(), [FM.Enc.name(Contract.Obs.write(b_978)), FM.Enc.name(Contract.Obs.write(a_977)), FM.Enc.obs(b_978), FM.Enc.obs(a_977), FM.Enc.obs(Source.Obs.tup{a_977, b_978})]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.name(Con{2n, List.append(&2, Nat, Contract.Obs.write(a_977), Contract.Obs.write(b_978))}), ks}},
        L.List.append(Contract.Obs.write(a_977), Contract.Obs.write(b_978), Con{Fun.Fr{Code.F.Obs.write.k6(), [FM.Enc.name(Contract.Obs.write(b_978)), FM.Enc.name(Contract.Obs.write(a_977)), FM.Enc.obs(b_978), FM.Enc.obs(a_977), FM.Enc.obs(Source.Obs.tup{a_977, b_978})]}, ks}),
        FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.name(List.append(&2, Nat, Contract.Obs.write(a_977), Contract.Obs.write(b_978))), Con{Fun.Fr{Code.F.Obs.write.k6(), [FM.Enc.name(Contract.Obs.write(b_978)), FM.Enc.name(Contract.Obs.write(a_977)), FM.Enc.obs(b_978), FM.Enc.obs(a_977), FM.Enc.obs(Source.Obs.tup{a_977, b_978})]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.name(List.append(&2, Nat, Contract.Obs.write(a_977), Contract.Obs.write(b_978))), Con{Fun.Fr{Code.F.Obs.write.k6(), [FM.Enc.name(Contract.Obs.write(b_978)), FM.Enc.name(Contract.Obs.write(a_977)), FM.Enc.obs(b_978), FM.Enc.obs(a_977), FM.Enc.obs(Source.Obs.tup{a_977, b_978})]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.name(Con{2n, List.append(&2, Nat, Contract.Obs.write(a_977), Contract.Obs.write(b_978))}), ks}},
        FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.name(List.append(&2, Nat, Contract.Obs.write(a_977), Contract.Obs.write(b_978))), Con{Fun.Fr{Code.F.Obs.write.k6(), [FM.Enc.name(Contract.Obs.write(b_978)), FM.Enc.name(Contract.Obs.write(a_977)), FM.Enc.obs(b_978), FM.Enc.obs(a_977), FM.Enc.obs(Source.Obs.tup{a_977, b_978})]}, ks}}}),
        (2n, {==}))))))))))
    case Source.Obs.tup0{+b_982}:
      FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.write(), [FM.Enc.obs(Source.Obs.tup0{b_982})], ks}}, Fun.F.iter(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.write(), [FM.Enc.obs(Source.Obs.tup0{b_982})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.name(Contract.Obs.write(Source.Obs.tup0{b_982})), ks}},
        FP.Reach.steps(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.write(), [FM.Enc.obs(Source.Obs.tup0{b_982})], ks}}),
        FP.Reach.trans(Code.prog(), Fun.F.iter(5n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Obs.write(), [FM.Enc.obs(Source.Obs.tup0{b_982})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.name(Contract.Obs.write(b_982)), Con{Fun.Fr{Code.F.Obs.write.k7(), [Fun.V.z{}, FM.Enc.obs(b_982), FM.Enc.obs(Source.Obs.tup0{b_982})]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.name(Contract.Obs.write(Source.Obs.tup0{b_982})), ks}},
        L.Obs.write(b_982, Con{Fun.Fr{Code.F.Obs.write.k7(), [Fun.V.z{}, FM.Enc.obs(b_982), FM.Enc.obs(Source.Obs.tup0{b_982})]}, ks}),
        FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.name(Contract.Obs.write(b_982)), Con{Fun.Fr{Code.F.Obs.write.k7(), [Fun.V.z{}, FM.Enc.obs(b_982), FM.Enc.obs(Source.Obs.tup0{b_982})]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.name(Contract.Obs.write(b_982)), Con{Fun.Fr{Code.F.Obs.write.k7(), [Fun.V.z{}, FM.Enc.obs(b_982), FM.Enc.obs(Source.Obs.tup0{b_982})]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.name(Contract.Obs.write(Source.Obs.tup0{b_982})), ks}},
        FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.name(Contract.Obs.write(b_982)), Con{Fun.Fr{Code.F.Obs.write.k7(), [Fun.V.z{}, FM.Enc.obs(b_982), FM.Enc.obs(Source.Obs.tup0{b_982})]}, ks}}}),
        (2n, {==}))))

def L.Out.of(+o_984: Source.Obs, +ks: List<&2, Fun.Fr>) ->
  Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Out.of(), [FM.Enc.obs(o_984)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.name(Contract.Out.of(o_984)), ks}}):
  FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Out.of(), [FM.Enc.obs(o_984)], ks}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Out.of(), [FM.Enc.obs(o_984)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.name(Contract.Out.of(o_984)), ks}},
    FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Out.of(), [FM.Enc.obs(o_984)], ks}}),
    FP.Reach.trans(Code.prog(), Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Out.of(), [FM.Enc.obs(o_984)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.mname(Contract.Obs.bytes(o_984)), Con{Fun.Fr{Code.F.Out.of.k1(), [FM.Enc.obs(o_984)]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.name(Contract.Out.of(o_984)), ks}},
    L.Obs.bytes(o_984, Con{Fun.Fr{Code.F.Out.of.k1(), [FM.Enc.obs(o_984)]}, ks}),
    FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.mname(Contract.Obs.bytes(o_984)), Con{Fun.Fr{Code.F.Out.of.k1(), [FM.Enc.obs(o_984)]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.mname(Contract.Obs.bytes(o_984)), Con{Fun.Fr{Code.F.Out.of.k1(), [FM.Enc.obs(o_984)]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.name(Contract.Out.of(o_984)), ks}},
    FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.mname(Contract.Obs.bytes(o_984)), Con{Fun.Fr{Code.F.Out.of.k1(), [FM.Enc.obs(o_984)]}, ks}}}),
    Elim.MName(Contract.Obs.bytes(o_984), m49 => Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Out.of.k1(), [FM.Enc.mname(m49), FM.Enc.obs(o_984)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.name(Contract.Out.of.bytes(m49, o_984)), ks}}),
    FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Out.of.k1(), [FM.Enc.mname(None{}), FM.Enc.obs(o_984)], ks}}, Fun.F.iter(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Out.of.k1(), [FM.Enc.mname(None{}), FM.Enc.obs(o_984)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.name(Contract.Out.of.bytes(None{}, o_984)), ks}},
    FP.Reach.steps(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Out.of.k1(), [FM.Enc.mname(None{}), FM.Enc.obs(o_984)], ks}}),
    FP.Reach.trans(Code.prog(), Fun.F.iter(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Out.of.k1(), [FM.Enc.mname(None{}), FM.Enc.obs(o_984)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.name(Contract.Obs.write(o_984)), Con{Fun.Fr{Code.F.Out.of.k2(), [FM.Enc.mname(None{}), FM.Enc.obs(o_984)]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.name(Contract.Out.of.bytes(None{}, o_984)), ks}},
    L.Obs.write(o_984, Con{Fun.Fr{Code.F.Out.of.k2(), [FM.Enc.mname(None{}), FM.Enc.obs(o_984)]}, ks}),
    FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.name(Contract.Obs.write(o_984)), Con{Fun.Fr{Code.F.Out.of.k2(), [FM.Enc.mname(None{}), FM.Enc.obs(o_984)]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.name(Contract.Obs.write(o_984)), Con{Fun.Fr{Code.F.Out.of.k2(), [FM.Enc.mname(None{}), FM.Enc.obs(o_984)]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.name(Contract.Out.of.bytes(None{}, o_984)), ks}},
    FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.name(Contract.Obs.write(o_984)), Con{Fun.Fr{Code.F.Out.of.k2(), [FM.Enc.mname(None{}), FM.Enc.obs(o_984)]}, ks}}}),
    (2n, {==})))),
    +bs_987 => (3n, {==})))))

def L.Nats.from(+c_989: Nat, +i_992: Nat, +ks: List<&2, Fun.Fr>) ->
  Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Nats.from(), [FM.Enc.term(Source.Bytes.nat(i_992)), FM.Enc.nat(c_989), FM.Enc.name(Source.Name.of("Succ")), FM.Enc.name(Source.Name.of("()"))], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.terms(FM.Nats.from(c_989, i_992)), ks}}):
  match c_989:
    case 0n:
      (3n, {==})
    case 1n+d_993:
      FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Nats.from(), [FM.Enc.term(Source.Bytes.nat(i_992)), FM.Enc.nat(1n+d_993), FM.Enc.name(Source.Name.of("Succ")), FM.Enc.name(Source.Name.of("()"))], ks}}, Fun.F.iter(8n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Nats.from(), [FM.Enc.term(Source.Bytes.nat(i_992)), FM.Enc.nat(1n+d_993), FM.Enc.name(Source.Name.of("Succ")), FM.Enc.name(Source.Name.of("()"))], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.terms(FM.Nats.from(1n+d_993, i_992)), ks}},
        FP.Reach.steps(8n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Nats.from(), [FM.Enc.term(Source.Bytes.nat(i_992)), FM.Enc.nat(1n+d_993), FM.Enc.name(Source.Name.of("Succ")), FM.Enc.name(Source.Name.of("()"))], ks}}),
        FP.Reach.trans(Code.prog(), Fun.F.iter(8n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Nats.from(), [FM.Enc.term(Source.Bytes.nat(i_992)), FM.Enc.nat(1n+d_993), FM.Enc.name(Source.Name.of("Succ")), FM.Enc.name(Source.Name.of("()"))], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.terms(FM.Nats.from(d_993, 1n+i_992)), Con{Fun.Fr{Code.F.Nats.from.k1(), [FM.Enc.term(Source.Term.Tup{Source.Q1{}, Source.Term.Lab{Source.Name.of("Succ")}, Source.Term.Tup{Source.Q1{}, Source.Bytes.nat(i_992), Source.Term.Lab{Source.Name.of("()")}}}), FM.Enc.p(FM.Enc.term(Source.Term.Lab{Source.Name.of("Succ")}), FM.Enc.term(Source.Term.Tup{Source.Q1{}, Source.Bytes.nat(i_992), Source.Term.Lab{Source.Name.of("()")}})), FM.Enc.term(Source.Term.Tup{Source.Q1{}, Source.Bytes.nat(i_992), Source.Term.Lab{Source.Name.of("()")}}), FM.Enc.p(FM.Enc.term(Source.Bytes.nat(i_992)), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")})), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")}), FM.Enc.term(Source.Term.Lab{Source.Name.of("Succ")}), Fun.V.num(d_993), FM.Enc.term(Source.Bytes.nat(i_992)), FM.Enc.nat(1n+d_993), FM.Enc.name(Source.Name.of("Succ")), FM.Enc.name(Source.Name.of("()"))]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.terms(FM.Nats.from(1n+d_993, i_992)), ks}},
        L.Nats.from(d_993, 1n+i_992, Con{Fun.Fr{Code.F.Nats.from.k1(), [FM.Enc.term(Source.Term.Tup{Source.Q1{}, Source.Term.Lab{Source.Name.of("Succ")}, Source.Term.Tup{Source.Q1{}, Source.Bytes.nat(i_992), Source.Term.Lab{Source.Name.of("()")}}}), FM.Enc.p(FM.Enc.term(Source.Term.Lab{Source.Name.of("Succ")}), FM.Enc.term(Source.Term.Tup{Source.Q1{}, Source.Bytes.nat(i_992), Source.Term.Lab{Source.Name.of("()")}})), FM.Enc.term(Source.Term.Tup{Source.Q1{}, Source.Bytes.nat(i_992), Source.Term.Lab{Source.Name.of("()")}}), FM.Enc.p(FM.Enc.term(Source.Bytes.nat(i_992)), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")})), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")}), FM.Enc.term(Source.Term.Lab{Source.Name.of("Succ")}), Fun.V.num(d_993), FM.Enc.term(Source.Bytes.nat(i_992)), FM.Enc.nat(1n+d_993), FM.Enc.name(Source.Name.of("Succ")), FM.Enc.name(Source.Name.of("()"))]}, ks}),
        FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.terms(FM.Nats.from(d_993, 1n+i_992)), Con{Fun.Fr{Code.F.Nats.from.k1(), [FM.Enc.term(Source.Term.Tup{Source.Q1{}, Source.Term.Lab{Source.Name.of("Succ")}, Source.Term.Tup{Source.Q1{}, Source.Bytes.nat(i_992), Source.Term.Lab{Source.Name.of("()")}}}), FM.Enc.p(FM.Enc.term(Source.Term.Lab{Source.Name.of("Succ")}), FM.Enc.term(Source.Term.Tup{Source.Q1{}, Source.Bytes.nat(i_992), Source.Term.Lab{Source.Name.of("()")}})), FM.Enc.term(Source.Term.Tup{Source.Q1{}, Source.Bytes.nat(i_992), Source.Term.Lab{Source.Name.of("()")}}), FM.Enc.p(FM.Enc.term(Source.Bytes.nat(i_992)), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")})), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")}), FM.Enc.term(Source.Term.Lab{Source.Name.of("Succ")}), Fun.V.num(d_993), FM.Enc.term(Source.Bytes.nat(i_992)), FM.Enc.nat(1n+d_993), FM.Enc.name(Source.Name.of("Succ")), FM.Enc.name(Source.Name.of("()"))]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.terms(FM.Nats.from(d_993, 1n+i_992)), Con{Fun.Fr{Code.F.Nats.from.k1(), [FM.Enc.term(Source.Term.Tup{Source.Q1{}, Source.Term.Lab{Source.Name.of("Succ")}, Source.Term.Tup{Source.Q1{}, Source.Bytes.nat(i_992), Source.Term.Lab{Source.Name.of("()")}}}), FM.Enc.p(FM.Enc.term(Source.Term.Lab{Source.Name.of("Succ")}), FM.Enc.term(Source.Term.Tup{Source.Q1{}, Source.Bytes.nat(i_992), Source.Term.Lab{Source.Name.of("()")}})), FM.Enc.term(Source.Term.Tup{Source.Q1{}, Source.Bytes.nat(i_992), Source.Term.Lab{Source.Name.of("()")}}), FM.Enc.p(FM.Enc.term(Source.Bytes.nat(i_992)), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")})), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")}), FM.Enc.term(Source.Term.Lab{Source.Name.of("Succ")}), Fun.V.num(d_993), FM.Enc.term(Source.Bytes.nat(i_992)), FM.Enc.nat(1n+d_993), FM.Enc.name(Source.Name.of("Succ")), FM.Enc.name(Source.Name.of("()"))]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.terms(FM.Nats.from(1n+d_993, i_992)), ks}},
        FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.terms(FM.Nats.from(d_993, 1n+i_992)), Con{Fun.Fr{Code.F.Nats.from.k1(), [FM.Enc.term(Source.Term.Tup{Source.Q1{}, Source.Term.Lab{Source.Name.of("Succ")}, Source.Term.Tup{Source.Q1{}, Source.Bytes.nat(i_992), Source.Term.Lab{Source.Name.of("()")}}}), FM.Enc.p(FM.Enc.term(Source.Term.Lab{Source.Name.of("Succ")}), FM.Enc.term(Source.Term.Tup{Source.Q1{}, Source.Bytes.nat(i_992), Source.Term.Lab{Source.Name.of("()")}})), FM.Enc.term(Source.Term.Tup{Source.Q1{}, Source.Bytes.nat(i_992), Source.Term.Lab{Source.Name.of("()")}}), FM.Enc.p(FM.Enc.term(Source.Bytes.nat(i_992)), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")})), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")}), FM.Enc.term(Source.Term.Lab{Source.Name.of("Succ")}), Fun.V.num(d_993), FM.Enc.term(Source.Bytes.nat(i_992)), FM.Enc.nat(1n+d_993), FM.Enc.name(Source.Name.of("Succ")), FM.Enc.name(Source.Name.of("()"))]}, ks}}}),
        (2n, {==}))))

def L.Terms.at(+ts_995: List<&2, Source.Term>, +b_996: Nat, +ks: List<&2, Fun.Fr>) ->
  Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Terms.at(), [FM.Enc.terms(ts_995), FM.Enc.nat(b_996)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.term(FM.Terms.at(ts_995, b_996)), ks}}):
  match ts_995:
    case Nil{}:
      match b_996:
        case 0n:
          (2n, {==})
        case 1n+_p_997:
          (2n, {==})
    case Con{+t_998, +rest_999}:
      match b_996:
        case 0n:
          (3n, {==})
        case 1n+p_1000:
          FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Terms.at(), [FM.Enc.terms(Con{t_998, rest_999}), FM.Enc.nat(1n+p_1000)], ks}}, Fun.F.iter(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Terms.at(), [FM.Enc.terms(Con{t_998, rest_999}), FM.Enc.nat(1n+p_1000)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.term(FM.Terms.at(Con{t_998, rest_999}, 1n+p_1000)), ks}},
            FP.Reach.steps(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Terms.at(), [FM.Enc.terms(Con{t_998, rest_999}), FM.Enc.nat(1n+p_1000)], ks}}),
            L.Terms.at(rest_999, p_1000, ks))

def L.Input.term(+bs_1001: List<&2, Nat>, +ts_1002: List<&2, Source.Term>, +ks: List<&2, Fun.Fr>) ->
  Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Input.term(), [FM.Enc.name(bs_1001), FM.Enc.terms(ts_1002), FM.Enc.name(Source.Name.of("Con")), FM.Enc.name(Source.Name.of("Nil")), FM.Enc.name(Source.Name.of("()"))], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.term(FM.Input.term(bs_1001, ts_1002)), ks}}):
  match bs_1001:
    case Nil{}:
      (6n, {==})
    case Con{+b_1006, +rest_1007}:
      FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Input.term(), [FM.Enc.name(Con{b_1006, rest_1007}), FM.Enc.terms(ts_1002), FM.Enc.name(Source.Name.of("Con")), FM.Enc.name(Source.Name.of("Nil")), FM.Enc.name(Source.Name.of("()"))], ks}}, Fun.F.iter(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Input.term(), [FM.Enc.name(Con{b_1006, rest_1007}), FM.Enc.terms(ts_1002), FM.Enc.name(Source.Name.of("Con")), FM.Enc.name(Source.Name.of("Nil")), FM.Enc.name(Source.Name.of("()"))], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.term(FM.Input.term(Con{b_1006, rest_1007}, ts_1002)), ks}},
        FP.Reach.steps(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Input.term(), [FM.Enc.name(Con{b_1006, rest_1007}), FM.Enc.terms(ts_1002), FM.Enc.name(Source.Name.of("Con")), FM.Enc.name(Source.Name.of("Nil")), FM.Enc.name(Source.Name.of("()"))], ks}}),
        FP.Reach.trans(Code.prog(), Fun.F.iter(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Input.term(), [FM.Enc.name(Con{b_1006, rest_1007}), FM.Enc.terms(ts_1002), FM.Enc.name(Source.Name.of("Con")), FM.Enc.name(Source.Name.of("Nil")), FM.Enc.name(Source.Name.of("()"))], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.term(FM.Terms.at(ts_1002, b_1006)), Con{Fun.Fr{Code.F.Input.term.k1(), [FM.Enc.name(rest_1007), FM.Enc.nat(b_1006), FM.Enc.name(Con{b_1006, rest_1007}), FM.Enc.terms(ts_1002), FM.Enc.name(Source.Name.of("Con")), FM.Enc.name(Source.Name.of("Nil")), FM.Enc.name(Source.Name.of("()"))]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.term(FM.Input.term(Con{b_1006, rest_1007}, ts_1002)), ks}},
        L.Terms.at(ts_1002, b_1006, Con{Fun.Fr{Code.F.Input.term.k1(), [FM.Enc.name(rest_1007), FM.Enc.nat(b_1006), FM.Enc.name(Con{b_1006, rest_1007}), FM.Enc.terms(ts_1002), FM.Enc.name(Source.Name.of("Con")), FM.Enc.name(Source.Name.of("Nil")), FM.Enc.name(Source.Name.of("()"))]}, ks}),
        FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.term(FM.Terms.at(ts_1002, b_1006)), Con{Fun.Fr{Code.F.Input.term.k1(), [FM.Enc.name(rest_1007), FM.Enc.nat(b_1006), FM.Enc.name(Con{b_1006, rest_1007}), FM.Enc.terms(ts_1002), FM.Enc.name(Source.Name.of("Con")), FM.Enc.name(Source.Name.of("Nil")), FM.Enc.name(Source.Name.of("()"))]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.term(FM.Terms.at(ts_1002, b_1006)), Con{Fun.Fr{Code.F.Input.term.k1(), [FM.Enc.name(rest_1007), FM.Enc.nat(b_1006), FM.Enc.name(Con{b_1006, rest_1007}), FM.Enc.terms(ts_1002), FM.Enc.name(Source.Name.of("Con")), FM.Enc.name(Source.Name.of("Nil")), FM.Enc.name(Source.Name.of("()"))]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.term(FM.Input.term(Con{b_1006, rest_1007}, ts_1002)), ks}},
        FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.term(FM.Terms.at(ts_1002, b_1006)), Con{Fun.Fr{Code.F.Input.term.k1(), [FM.Enc.name(rest_1007), FM.Enc.nat(b_1006), FM.Enc.name(Con{b_1006, rest_1007}), FM.Enc.terms(ts_1002), FM.Enc.name(Source.Name.of("Con")), FM.Enc.name(Source.Name.of("Nil")), FM.Enc.name(Source.Name.of("()"))]}, ks}}}),
        FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Input.term.k1(), [FM.Enc.term(FM.Terms.at(ts_1002, b_1006)), FM.Enc.name(rest_1007), FM.Enc.nat(b_1006), FM.Enc.name(Con{b_1006, rest_1007}), FM.Enc.terms(ts_1002), FM.Enc.name(Source.Name.of("Con")), FM.Enc.name(Source.Name.of("Nil")), FM.Enc.name(Source.Name.of("()"))], ks}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Input.term.k1(), [FM.Enc.term(FM.Terms.at(ts_1002, b_1006)), FM.Enc.name(rest_1007), FM.Enc.nat(b_1006), FM.Enc.name(Con{b_1006, rest_1007}), FM.Enc.terms(ts_1002), FM.Enc.name(Source.Name.of("Con")), FM.Enc.name(Source.Name.of("Nil")), FM.Enc.name(Source.Name.of("()"))], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.term(Source.Term.Tup{Source.Q1{}, Source.Term.Lab{Source.Name.of("Con")}, Source.Term.Tup{Source.Q1{}, FM.Terms.at(ts_1002, b_1006), Source.Term.Tup{Source.Q1{}, FM.Input.term(rest_1007, ts_1002), Source.Term.Lab{Source.Name.of("()")}}}}), ks}},
        FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Input.term.k1(), [FM.Enc.term(FM.Terms.at(ts_1002, b_1006)), FM.Enc.name(rest_1007), FM.Enc.nat(b_1006), FM.Enc.name(Con{b_1006, rest_1007}), FM.Enc.terms(ts_1002), FM.Enc.name(Source.Name.of("Con")), FM.Enc.name(Source.Name.of("Nil")), FM.Enc.name(Source.Name.of("()"))], ks}}),
        FP.Reach.trans(Code.prog(), Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Input.term.k1(), [FM.Enc.term(FM.Terms.at(ts_1002, b_1006)), FM.Enc.name(rest_1007), FM.Enc.nat(b_1006), FM.Enc.name(Con{b_1006, rest_1007}), FM.Enc.terms(ts_1002), FM.Enc.name(Source.Name.of("Con")), FM.Enc.name(Source.Name.of("Nil")), FM.Enc.name(Source.Name.of("()"))], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.term(FM.Input.term(rest_1007, ts_1002)), Con{Fun.Fr{Code.F.Input.term.k2(), [FM.Enc.term(FM.Terms.at(ts_1002, b_1006)), FM.Enc.name(rest_1007), FM.Enc.nat(b_1006), FM.Enc.name(Con{b_1006, rest_1007}), FM.Enc.terms(ts_1002), FM.Enc.name(Source.Name.of("Con")), FM.Enc.name(Source.Name.of("Nil")), FM.Enc.name(Source.Name.of("()"))]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.term(Source.Term.Tup{Source.Q1{}, Source.Term.Lab{Source.Name.of("Con")}, Source.Term.Tup{Source.Q1{}, FM.Terms.at(ts_1002, b_1006), Source.Term.Tup{Source.Q1{}, FM.Input.term(rest_1007, ts_1002), Source.Term.Lab{Source.Name.of("()")}}}}), ks}},
        L.Input.term(rest_1007, ts_1002, Con{Fun.Fr{Code.F.Input.term.k2(), [FM.Enc.term(FM.Terms.at(ts_1002, b_1006)), FM.Enc.name(rest_1007), FM.Enc.nat(b_1006), FM.Enc.name(Con{b_1006, rest_1007}), FM.Enc.terms(ts_1002), FM.Enc.name(Source.Name.of("Con")), FM.Enc.name(Source.Name.of("Nil")), FM.Enc.name(Source.Name.of("()"))]}, ks}),
        FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.term(FM.Input.term(rest_1007, ts_1002)), Con{Fun.Fr{Code.F.Input.term.k2(), [FM.Enc.term(FM.Terms.at(ts_1002, b_1006)), FM.Enc.name(rest_1007), FM.Enc.nat(b_1006), FM.Enc.name(Con{b_1006, rest_1007}), FM.Enc.terms(ts_1002), FM.Enc.name(Source.Name.of("Con")), FM.Enc.name(Source.Name.of("Nil")), FM.Enc.name(Source.Name.of("()"))]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.term(FM.Input.term(rest_1007, ts_1002)), Con{Fun.Fr{Code.F.Input.term.k2(), [FM.Enc.term(FM.Terms.at(ts_1002, b_1006)), FM.Enc.name(rest_1007), FM.Enc.nat(b_1006), FM.Enc.name(Con{b_1006, rest_1007}), FM.Enc.terms(ts_1002), FM.Enc.name(Source.Name.of("Con")), FM.Enc.name(Source.Name.of("Nil")), FM.Enc.name(Source.Name.of("()"))]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.term(Source.Term.Tup{Source.Q1{}, Source.Term.Lab{Source.Name.of("Con")}, Source.Term.Tup{Source.Q1{}, FM.Terms.at(ts_1002, b_1006), Source.Term.Tup{Source.Q1{}, FM.Input.term(rest_1007, ts_1002), Source.Term.Lab{Source.Name.of("()")}}}}), ks}},
        FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.term(FM.Input.term(rest_1007, ts_1002)), Con{Fun.Fr{Code.F.Input.term.k2(), [FM.Enc.term(FM.Terms.at(ts_1002, b_1006)), FM.Enc.name(rest_1007), FM.Enc.nat(b_1006), FM.Enc.name(Con{b_1006, rest_1007}), FM.Enc.terms(ts_1002), FM.Enc.name(Source.Name.of("Con")), FM.Enc.name(Source.Name.of("Nil")), FM.Enc.name(Source.Name.of("()"))]}, ks}}}),
        (9n, {==})))))))

def L.Book.append(+xs_1010: List<&2, Source.Def>, +ys_1011: List<&2, Source.Def>, +ks: List<&2, Fun.Fr>) ->
  Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Book.append(), [FM.Enc.book(xs_1010), FM.Enc.book(ys_1011)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.book(List.append(&2, Source.Def, xs_1010, ys_1011)), ks}}):
  match xs_1010:
    case Nil{}:
      (2n, {==})
    case Con{+h_1012, +t_1013}:
      FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Book.append(), [FM.Enc.book(Con{h_1012, t_1013}), FM.Enc.book(ys_1011)], ks}}, Fun.F.iter(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Book.append(), [FM.Enc.book(Con{h_1012, t_1013}), FM.Enc.book(ys_1011)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.book(List.append(&2, Source.Def, Con{h_1012, t_1013}, ys_1011)), ks}},
        FP.Reach.steps(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Book.append(), [FM.Enc.book(Con{h_1012, t_1013}), FM.Enc.book(ys_1011)], ks}}),
        FP.Reach.trans(Code.prog(), Fun.F.iter(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Book.append(), [FM.Enc.book(Con{h_1012, t_1013}), FM.Enc.book(ys_1011)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.book(List.append(&2, Source.Def, t_1013, ys_1011)), Con{Fun.Fr{Code.F.Book.append.k1(), [FM.Enc.book(t_1013), FM.Enc.def(h_1012), FM.Enc.book(Con{h_1012, t_1013}), FM.Enc.book(ys_1011)]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.book(List.append(&2, Source.Def, Con{h_1012, t_1013}, ys_1011)), ks}},
        L.Book.append(t_1013, ys_1011, Con{Fun.Fr{Code.F.Book.append.k1(), [FM.Enc.book(t_1013), FM.Enc.def(h_1012), FM.Enc.book(Con{h_1012, t_1013}), FM.Enc.book(ys_1011)]}, ks}),
        FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.book(List.append(&2, Source.Def, t_1013, ys_1011)), Con{Fun.Fr{Code.F.Book.append.k1(), [FM.Enc.book(t_1013), FM.Enc.def(h_1012), FM.Enc.book(Con{h_1012, t_1013}), FM.Enc.book(ys_1011)]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.book(List.append(&2, Source.Def, t_1013, ys_1011)), Con{Fun.Fr{Code.F.Book.append.k1(), [FM.Enc.book(t_1013), FM.Enc.def(h_1012), FM.Enc.book(Con{h_1012, t_1013}), FM.Enc.book(ys_1011)]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.book(List.append(&2, Source.Def, Con{h_1012, t_1013}, ys_1011)), ks}},
        FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.book(List.append(&2, Source.Def, t_1013, ys_1011)), Con{Fun.Fr{Code.F.Book.append.k1(), [FM.Enc.book(t_1013), FM.Enc.def(h_1012), FM.Enc.book(Con{h_1012, t_1013}), FM.Enc.book(ys_1011)]}, ks}}}),
        (2n, {==}))))

def L.Entry(+inp_1023: Maybe<&2, List<&2, Nat>>, +bk_1022: List<&2, Source.Def>, +d2_1024: Maybe<&2, Source.Def>, +c_1025: Nat, +ty_1026: Source.Term, +ks: List<&2, Fun.Fr>) ->
  Fun.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Entry(), [FM.Enc.book(bk_1022), FM.Enc.mname(inp_1023), FM.Enc.mdef(d2_1024), FM.Enc.nat(c_1025)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.mstart(FM.Start.of(bk_1022, inp_1023, ty_1026, c_1025, d2_1024)), ks}}):
  match inp_1023:
    case None{}:
      (11n, {==})
    case Some{+bs_1027}:
      match d2_1024:
        case None{}:
          (4n, {==})
        case Some{+dr_1028}:
          FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Entry(), [FM.Enc.book(bk_1022), FM.Enc.mname(Some{bs_1027}), FM.Enc.mdef(Some{dr_1028}), FM.Enc.nat(c_1025)], ks}}, Fun.F.iter(20n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Entry(), [FM.Enc.book(bk_1022), FM.Enc.mname(Some{bs_1027}), FM.Enc.mdef(Some{dr_1028}), FM.Enc.nat(c_1025)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.mstart(FM.Start.of(bk_1022, Some{bs_1027}, ty_1026, c_1025, Some{dr_1028})), ks}},
            FP.Reach.steps(20n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Entry(), [FM.Enc.book(bk_1022), FM.Enc.mname(Some{bs_1027}), FM.Enc.mdef(Some{dr_1028}), FM.Enc.nat(c_1025)], ks}}),
            FP.Reach.trans(Code.prog(), Fun.F.iter(20n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Entry(), [FM.Enc.book(bk_1022), FM.Enc.mname(Some{bs_1027}), FM.Enc.mdef(Some{dr_1028}), FM.Enc.nat(c_1025)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.terms(FM.Nats.from(c_1025, 0n)), Con{Fun.Fr{Code.F.Entry.k1(), [FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.name(Source.Name.of("Succ")), FM.Enc.name(Source.Name.of("ucc")), FM.Enc.name(Source.Name.of("cc")), FM.Enc.name(Source.Name.of("c")), FM.Enc.term(Source.Term.Tup{Source.Q1{}, Source.Term.Lab{Source.Name.of("Zero")}, Source.Term.Lab{Source.Name.of("()")}}), FM.Enc.p(FM.Enc.term(Source.Term.Lab{Source.Name.of("Zero")}), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")})), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")}), FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.term(Source.Term.Lab{Source.Name.of("Zero")}), FM.Enc.name(Source.Name.of("Zero")), FM.Enc.name(Source.Name.of("ero")), FM.Enc.name(Source.Name.of("ro")), FM.Enc.name(Source.Name.of("o")), Fun.V.z{}, FM.Enc.def(dr_1028), Fun.V.z{}, FM.Enc.name(bs_1027), FM.Enc.book(bk_1022), FM.Enc.mname(Some{bs_1027}), FM.Enc.mdef(Some{dr_1028}), FM.Enc.nat(c_1025)]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.mstart(FM.Start.of(bk_1022, Some{bs_1027}, ty_1026, c_1025, Some{dr_1028})), ks}},
            L.Nats.from(c_1025, 0n, Con{Fun.Fr{Code.F.Entry.k1(), [FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.name(Source.Name.of("Succ")), FM.Enc.name(Source.Name.of("ucc")), FM.Enc.name(Source.Name.of("cc")), FM.Enc.name(Source.Name.of("c")), FM.Enc.term(Source.Term.Tup{Source.Q1{}, Source.Term.Lab{Source.Name.of("Zero")}, Source.Term.Lab{Source.Name.of("()")}}), FM.Enc.p(FM.Enc.term(Source.Term.Lab{Source.Name.of("Zero")}), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")})), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")}), FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.term(Source.Term.Lab{Source.Name.of("Zero")}), FM.Enc.name(Source.Name.of("Zero")), FM.Enc.name(Source.Name.of("ero")), FM.Enc.name(Source.Name.of("ro")), FM.Enc.name(Source.Name.of("o")), Fun.V.z{}, FM.Enc.def(dr_1028), Fun.V.z{}, FM.Enc.name(bs_1027), FM.Enc.book(bk_1022), FM.Enc.mname(Some{bs_1027}), FM.Enc.mdef(Some{dr_1028}), FM.Enc.nat(c_1025)]}, ks}),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.terms(FM.Nats.from(c_1025, 0n)), Con{Fun.Fr{Code.F.Entry.k1(), [FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.name(Source.Name.of("Succ")), FM.Enc.name(Source.Name.of("ucc")), FM.Enc.name(Source.Name.of("cc")), FM.Enc.name(Source.Name.of("c")), FM.Enc.term(Source.Term.Tup{Source.Q1{}, Source.Term.Lab{Source.Name.of("Zero")}, Source.Term.Lab{Source.Name.of("()")}}), FM.Enc.p(FM.Enc.term(Source.Term.Lab{Source.Name.of("Zero")}), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")})), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")}), FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.term(Source.Term.Lab{Source.Name.of("Zero")}), FM.Enc.name(Source.Name.of("Zero")), FM.Enc.name(Source.Name.of("ero")), FM.Enc.name(Source.Name.of("ro")), FM.Enc.name(Source.Name.of("o")), Fun.V.z{}, FM.Enc.def(dr_1028), Fun.V.z{}, FM.Enc.name(bs_1027), FM.Enc.book(bk_1022), FM.Enc.mname(Some{bs_1027}), FM.Enc.mdef(Some{dr_1028}), FM.Enc.nat(c_1025)]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.terms(FM.Nats.from(c_1025, 0n)), Con{Fun.Fr{Code.F.Entry.k1(), [FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.name(Source.Name.of("Succ")), FM.Enc.name(Source.Name.of("ucc")), FM.Enc.name(Source.Name.of("cc")), FM.Enc.name(Source.Name.of("c")), FM.Enc.term(Source.Term.Tup{Source.Q1{}, Source.Term.Lab{Source.Name.of("Zero")}, Source.Term.Lab{Source.Name.of("()")}}), FM.Enc.p(FM.Enc.term(Source.Term.Lab{Source.Name.of("Zero")}), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")})), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")}), FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.term(Source.Term.Lab{Source.Name.of("Zero")}), FM.Enc.name(Source.Name.of("Zero")), FM.Enc.name(Source.Name.of("ero")), FM.Enc.name(Source.Name.of("ro")), FM.Enc.name(Source.Name.of("o")), Fun.V.z{}, FM.Enc.def(dr_1028), Fun.V.z{}, FM.Enc.name(bs_1027), FM.Enc.book(bk_1022), FM.Enc.mname(Some{bs_1027}), FM.Enc.mdef(Some{dr_1028}), FM.Enc.nat(c_1025)]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.mstart(FM.Start.of(bk_1022, Some{bs_1027}, ty_1026, c_1025, Some{dr_1028})), ks}},
            FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.terms(FM.Nats.from(c_1025, 0n)), Con{Fun.Fr{Code.F.Entry.k1(), [FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.name(Source.Name.of("Succ")), FM.Enc.name(Source.Name.of("ucc")), FM.Enc.name(Source.Name.of("cc")), FM.Enc.name(Source.Name.of("c")), FM.Enc.term(Source.Term.Tup{Source.Q1{}, Source.Term.Lab{Source.Name.of("Zero")}, Source.Term.Lab{Source.Name.of("()")}}), FM.Enc.p(FM.Enc.term(Source.Term.Lab{Source.Name.of("Zero")}), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")})), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")}), FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.term(Source.Term.Lab{Source.Name.of("Zero")}), FM.Enc.name(Source.Name.of("Zero")), FM.Enc.name(Source.Name.of("ero")), FM.Enc.name(Source.Name.of("ro")), FM.Enc.name(Source.Name.of("o")), Fun.V.z{}, FM.Enc.def(dr_1028), Fun.V.z{}, FM.Enc.name(bs_1027), FM.Enc.book(bk_1022), FM.Enc.mname(Some{bs_1027}), FM.Enc.mdef(Some{dr_1028}), FM.Enc.nat(c_1025)]}, ks}}}),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Entry.k1(), [FM.Enc.terms(FM.Nats.from(c_1025, 0n)), FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.name(Source.Name.of("Succ")), FM.Enc.name(Source.Name.of("ucc")), FM.Enc.name(Source.Name.of("cc")), FM.Enc.name(Source.Name.of("c")), FM.Enc.term(Source.Term.Tup{Source.Q1{}, Source.Term.Lab{Source.Name.of("Zero")}, Source.Term.Lab{Source.Name.of("()")}}), FM.Enc.p(FM.Enc.term(Source.Term.Lab{Source.Name.of("Zero")}), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")})), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")}), FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.term(Source.Term.Lab{Source.Name.of("Zero")}), FM.Enc.name(Source.Name.of("Zero")), FM.Enc.name(Source.Name.of("ero")), FM.Enc.name(Source.Name.of("ro")), FM.Enc.name(Source.Name.of("o")), Fun.V.z{}, FM.Enc.def(dr_1028), Fun.V.z{}, FM.Enc.name(bs_1027), FM.Enc.book(bk_1022), FM.Enc.mname(Some{bs_1027}), FM.Enc.mdef(Some{dr_1028}), FM.Enc.nat(c_1025)], ks}}, Fun.F.iter(9n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Entry.k1(), [FM.Enc.terms(FM.Nats.from(c_1025, 0n)), FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.name(Source.Name.of("Succ")), FM.Enc.name(Source.Name.of("ucc")), FM.Enc.name(Source.Name.of("cc")), FM.Enc.name(Source.Name.of("c")), FM.Enc.term(Source.Term.Tup{Source.Q1{}, Source.Term.Lab{Source.Name.of("Zero")}, Source.Term.Lab{Source.Name.of("()")}}), FM.Enc.p(FM.Enc.term(Source.Term.Lab{Source.Name.of("Zero")}), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")})), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")}), FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.term(Source.Term.Lab{Source.Name.of("Zero")}), FM.Enc.name(Source.Name.of("Zero")), FM.Enc.name(Source.Name.of("ero")), FM.Enc.name(Source.Name.of("ro")), FM.Enc.name(Source.Name.of("o")), Fun.V.z{}, FM.Enc.def(dr_1028), Fun.V.z{}, FM.Enc.name(bs_1027), FM.Enc.book(bk_1022), FM.Enc.mname(Some{bs_1027}), FM.Enc.mdef(Some{dr_1028}), FM.Enc.nat(c_1025)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.mstart(Some{FM.Start{FM.Start.eval(Source.Name.of("bootstrap.run")), List.append(&2, Source.Def, bk_1022, [Source.Def{Source.Name.of("bootstrap.input"), ty_1026, FM.Input.term(bs_1027, FM.Nats.from(c_1025, 0n)), False{}}, dr_1028])}}), ks}},
            FP.Reach.steps(9n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Entry.k1(), [FM.Enc.terms(FM.Nats.from(c_1025, 0n)), FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.name(Source.Name.of("Succ")), FM.Enc.name(Source.Name.of("ucc")), FM.Enc.name(Source.Name.of("cc")), FM.Enc.name(Source.Name.of("c")), FM.Enc.term(Source.Term.Tup{Source.Q1{}, Source.Term.Lab{Source.Name.of("Zero")}, Source.Term.Lab{Source.Name.of("()")}}), FM.Enc.p(FM.Enc.term(Source.Term.Lab{Source.Name.of("Zero")}), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")})), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")}), FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.term(Source.Term.Lab{Source.Name.of("Zero")}), FM.Enc.name(Source.Name.of("Zero")), FM.Enc.name(Source.Name.of("ero")), FM.Enc.name(Source.Name.of("ro")), FM.Enc.name(Source.Name.of("o")), Fun.V.z{}, FM.Enc.def(dr_1028), Fun.V.z{}, FM.Enc.name(bs_1027), FM.Enc.book(bk_1022), FM.Enc.mname(Some{bs_1027}), FM.Enc.mdef(Some{dr_1028}), FM.Enc.nat(c_1025)], ks}}),
            FP.Reach.trans(Code.prog(), Fun.F.iter(9n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Entry.k1(), [FM.Enc.terms(FM.Nats.from(c_1025, 0n)), FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.name(Source.Name.of("Succ")), FM.Enc.name(Source.Name.of("ucc")), FM.Enc.name(Source.Name.of("cc")), FM.Enc.name(Source.Name.of("c")), FM.Enc.term(Source.Term.Tup{Source.Q1{}, Source.Term.Lab{Source.Name.of("Zero")}, Source.Term.Lab{Source.Name.of("()")}}), FM.Enc.p(FM.Enc.term(Source.Term.Lab{Source.Name.of("Zero")}), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")})), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")}), FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.term(Source.Term.Lab{Source.Name.of("Zero")}), FM.Enc.name(Source.Name.of("Zero")), FM.Enc.name(Source.Name.of("ero")), FM.Enc.name(Source.Name.of("ro")), FM.Enc.name(Source.Name.of("o")), Fun.V.z{}, FM.Enc.def(dr_1028), Fun.V.z{}, FM.Enc.name(bs_1027), FM.Enc.book(bk_1022), FM.Enc.mname(Some{bs_1027}), FM.Enc.mdef(Some{dr_1028}), FM.Enc.nat(c_1025)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.term(FM.Input.term(bs_1027, FM.Nats.from(c_1025, 0n))), Con{Fun.Fr{Code.F.Entry.k2(), [FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.name(Source.Name.of("Nil")), FM.Enc.name(Source.Name.of("il")), FM.Enc.name(Source.Name.of("l")), FM.Enc.name(Source.Name.of("Con")), FM.Enc.name(Source.Name.of("on")), FM.Enc.name(Source.Name.of("n")), FM.Enc.terms(FM.Nats.from(c_1025, 0n)), FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.name(Source.Name.of("Succ")), FM.Enc.name(Source.Name.of("ucc")), FM.Enc.name(Source.Name.of("cc")), FM.Enc.name(Source.Name.of("c")), FM.Enc.term(Source.Term.Tup{Source.Q1{}, Source.Term.Lab{Source.Name.of("Zero")}, Source.Term.Lab{Source.Name.of("()")}}), FM.Enc.p(FM.Enc.term(Source.Term.Lab{Source.Name.of("Zero")}), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")})), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")}), FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.term(Source.Term.Lab{Source.Name.of("Zero")}), FM.Enc.name(Source.Name.of("Zero")), FM.Enc.name(Source.Name.of("ero")), FM.Enc.name(Source.Name.of("ro")), FM.Enc.name(Source.Name.of("o")), Fun.V.z{}, FM.Enc.def(dr_1028), Fun.V.z{}, FM.Enc.name(bs_1027), FM.Enc.book(bk_1022), FM.Enc.mname(Some{bs_1027}), FM.Enc.mdef(Some{dr_1028}), FM.Enc.nat(c_1025)]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.mstart(Some{FM.Start{FM.Start.eval(Source.Name.of("bootstrap.run")), List.append(&2, Source.Def, bk_1022, [Source.Def{Source.Name.of("bootstrap.input"), ty_1026, FM.Input.term(bs_1027, FM.Nats.from(c_1025, 0n)), False{}}, dr_1028])}}), ks}},
            L.Input.term(bs_1027, FM.Nats.from(c_1025, 0n), Con{Fun.Fr{Code.F.Entry.k2(), [FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.name(Source.Name.of("Nil")), FM.Enc.name(Source.Name.of("il")), FM.Enc.name(Source.Name.of("l")), FM.Enc.name(Source.Name.of("Con")), FM.Enc.name(Source.Name.of("on")), FM.Enc.name(Source.Name.of("n")), FM.Enc.terms(FM.Nats.from(c_1025, 0n)), FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.name(Source.Name.of("Succ")), FM.Enc.name(Source.Name.of("ucc")), FM.Enc.name(Source.Name.of("cc")), FM.Enc.name(Source.Name.of("c")), FM.Enc.term(Source.Term.Tup{Source.Q1{}, Source.Term.Lab{Source.Name.of("Zero")}, Source.Term.Lab{Source.Name.of("()")}}), FM.Enc.p(FM.Enc.term(Source.Term.Lab{Source.Name.of("Zero")}), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")})), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")}), FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.term(Source.Term.Lab{Source.Name.of("Zero")}), FM.Enc.name(Source.Name.of("Zero")), FM.Enc.name(Source.Name.of("ero")), FM.Enc.name(Source.Name.of("ro")), FM.Enc.name(Source.Name.of("o")), Fun.V.z{}, FM.Enc.def(dr_1028), Fun.V.z{}, FM.Enc.name(bs_1027), FM.Enc.book(bk_1022), FM.Enc.mname(Some{bs_1027}), FM.Enc.mdef(Some{dr_1028}), FM.Enc.nat(c_1025)]}, ks}),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.term(FM.Input.term(bs_1027, FM.Nats.from(c_1025, 0n))), Con{Fun.Fr{Code.F.Entry.k2(), [FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.name(Source.Name.of("Nil")), FM.Enc.name(Source.Name.of("il")), FM.Enc.name(Source.Name.of("l")), FM.Enc.name(Source.Name.of("Con")), FM.Enc.name(Source.Name.of("on")), FM.Enc.name(Source.Name.of("n")), FM.Enc.terms(FM.Nats.from(c_1025, 0n)), FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.name(Source.Name.of("Succ")), FM.Enc.name(Source.Name.of("ucc")), FM.Enc.name(Source.Name.of("cc")), FM.Enc.name(Source.Name.of("c")), FM.Enc.term(Source.Term.Tup{Source.Q1{}, Source.Term.Lab{Source.Name.of("Zero")}, Source.Term.Lab{Source.Name.of("()")}}), FM.Enc.p(FM.Enc.term(Source.Term.Lab{Source.Name.of("Zero")}), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")})), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")}), FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.term(Source.Term.Lab{Source.Name.of("Zero")}), FM.Enc.name(Source.Name.of("Zero")), FM.Enc.name(Source.Name.of("ero")), FM.Enc.name(Source.Name.of("ro")), FM.Enc.name(Source.Name.of("o")), Fun.V.z{}, FM.Enc.def(dr_1028), Fun.V.z{}, FM.Enc.name(bs_1027), FM.Enc.book(bk_1022), FM.Enc.mname(Some{bs_1027}), FM.Enc.mdef(Some{dr_1028}), FM.Enc.nat(c_1025)]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.term(FM.Input.term(bs_1027, FM.Nats.from(c_1025, 0n))), Con{Fun.Fr{Code.F.Entry.k2(), [FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.name(Source.Name.of("Nil")), FM.Enc.name(Source.Name.of("il")), FM.Enc.name(Source.Name.of("l")), FM.Enc.name(Source.Name.of("Con")), FM.Enc.name(Source.Name.of("on")), FM.Enc.name(Source.Name.of("n")), FM.Enc.terms(FM.Nats.from(c_1025, 0n)), FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.name(Source.Name.of("Succ")), FM.Enc.name(Source.Name.of("ucc")), FM.Enc.name(Source.Name.of("cc")), FM.Enc.name(Source.Name.of("c")), FM.Enc.term(Source.Term.Tup{Source.Q1{}, Source.Term.Lab{Source.Name.of("Zero")}, Source.Term.Lab{Source.Name.of("()")}}), FM.Enc.p(FM.Enc.term(Source.Term.Lab{Source.Name.of("Zero")}), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")})), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")}), FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.term(Source.Term.Lab{Source.Name.of("Zero")}), FM.Enc.name(Source.Name.of("Zero")), FM.Enc.name(Source.Name.of("ero")), FM.Enc.name(Source.Name.of("ro")), FM.Enc.name(Source.Name.of("o")), Fun.V.z{}, FM.Enc.def(dr_1028), Fun.V.z{}, FM.Enc.name(bs_1027), FM.Enc.book(bk_1022), FM.Enc.mname(Some{bs_1027}), FM.Enc.mdef(Some{dr_1028}), FM.Enc.nat(c_1025)]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.mstart(Some{FM.Start{FM.Start.eval(Source.Name.of("bootstrap.run")), List.append(&2, Source.Def, bk_1022, [Source.Def{Source.Name.of("bootstrap.input"), ty_1026, FM.Input.term(bs_1027, FM.Nats.from(c_1025, 0n)), False{}}, dr_1028])}}), ks}},
            FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.term(FM.Input.term(bs_1027, FM.Nats.from(c_1025, 0n))), Con{Fun.Fr{Code.F.Entry.k2(), [FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.name(Source.Name.of("Nil")), FM.Enc.name(Source.Name.of("il")), FM.Enc.name(Source.Name.of("l")), FM.Enc.name(Source.Name.of("Con")), FM.Enc.name(Source.Name.of("on")), FM.Enc.name(Source.Name.of("n")), FM.Enc.terms(FM.Nats.from(c_1025, 0n)), FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.name(Source.Name.of("Succ")), FM.Enc.name(Source.Name.of("ucc")), FM.Enc.name(Source.Name.of("cc")), FM.Enc.name(Source.Name.of("c")), FM.Enc.term(Source.Term.Tup{Source.Q1{}, Source.Term.Lab{Source.Name.of("Zero")}, Source.Term.Lab{Source.Name.of("()")}}), FM.Enc.p(FM.Enc.term(Source.Term.Lab{Source.Name.of("Zero")}), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")})), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")}), FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.term(Source.Term.Lab{Source.Name.of("Zero")}), FM.Enc.name(Source.Name.of("Zero")), FM.Enc.name(Source.Name.of("ero")), FM.Enc.name(Source.Name.of("ro")), FM.Enc.name(Source.Name.of("o")), Fun.V.z{}, FM.Enc.def(dr_1028), Fun.V.z{}, FM.Enc.name(bs_1027), FM.Enc.book(bk_1022), FM.Enc.mname(Some{bs_1027}), FM.Enc.mdef(Some{dr_1028}), FM.Enc.nat(c_1025)]}, ks}}}),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Entry.k2(), [FM.Enc.term(FM.Input.term(bs_1027, FM.Nats.from(c_1025, 0n))), FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.name(Source.Name.of("Nil")), FM.Enc.name(Source.Name.of("il")), FM.Enc.name(Source.Name.of("l")), FM.Enc.name(Source.Name.of("Con")), FM.Enc.name(Source.Name.of("on")), FM.Enc.name(Source.Name.of("n")), FM.Enc.terms(FM.Nats.from(c_1025, 0n)), FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.name(Source.Name.of("Succ")), FM.Enc.name(Source.Name.of("ucc")), FM.Enc.name(Source.Name.of("cc")), FM.Enc.name(Source.Name.of("c")), FM.Enc.term(Source.Term.Tup{Source.Q1{}, Source.Term.Lab{Source.Name.of("Zero")}, Source.Term.Lab{Source.Name.of("()")}}), FM.Enc.p(FM.Enc.term(Source.Term.Lab{Source.Name.of("Zero")}), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")})), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")}), FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.term(Source.Term.Lab{Source.Name.of("Zero")}), FM.Enc.name(Source.Name.of("Zero")), FM.Enc.name(Source.Name.of("ero")), FM.Enc.name(Source.Name.of("ro")), FM.Enc.name(Source.Name.of("o")), Fun.V.z{}, FM.Enc.def(dr_1028), Fun.V.z{}, FM.Enc.name(bs_1027), FM.Enc.book(bk_1022), FM.Enc.mname(Some{bs_1027}), FM.Enc.mdef(Some{dr_1028}), FM.Enc.nat(c_1025)], ks}}, Fun.F.iter(19n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Entry.k2(), [FM.Enc.term(FM.Input.term(bs_1027, FM.Nats.from(c_1025, 0n))), FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.name(Source.Name.of("Nil")), FM.Enc.name(Source.Name.of("il")), FM.Enc.name(Source.Name.of("l")), FM.Enc.name(Source.Name.of("Con")), FM.Enc.name(Source.Name.of("on")), FM.Enc.name(Source.Name.of("n")), FM.Enc.terms(FM.Nats.from(c_1025, 0n)), FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.name(Source.Name.of("Succ")), FM.Enc.name(Source.Name.of("ucc")), FM.Enc.name(Source.Name.of("cc")), FM.Enc.name(Source.Name.of("c")), FM.Enc.term(Source.Term.Tup{Source.Q1{}, Source.Term.Lab{Source.Name.of("Zero")}, Source.Term.Lab{Source.Name.of("()")}}), FM.Enc.p(FM.Enc.term(Source.Term.Lab{Source.Name.of("Zero")}), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")})), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")}), FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.term(Source.Term.Lab{Source.Name.of("Zero")}), FM.Enc.name(Source.Name.of("Zero")), FM.Enc.name(Source.Name.of("ero")), FM.Enc.name(Source.Name.of("ro")), FM.Enc.name(Source.Name.of("o")), Fun.V.z{}, FM.Enc.def(dr_1028), Fun.V.z{}, FM.Enc.name(bs_1027), FM.Enc.book(bk_1022), FM.Enc.mname(Some{bs_1027}), FM.Enc.mdef(Some{dr_1028}), FM.Enc.nat(c_1025)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.mstart(Some{FM.Start{FM.Start.eval(Source.Name.of("bootstrap.run")), List.append(&2, Source.Def, bk_1022, [Source.Def{Source.Name.of("bootstrap.input"), ty_1026, FM.Input.term(bs_1027, FM.Nats.from(c_1025, 0n)), False{}}, dr_1028])}}), ks}},
            FP.Reach.steps(19n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Entry.k2(), [FM.Enc.term(FM.Input.term(bs_1027, FM.Nats.from(c_1025, 0n))), FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.name(Source.Name.of("Nil")), FM.Enc.name(Source.Name.of("il")), FM.Enc.name(Source.Name.of("l")), FM.Enc.name(Source.Name.of("Con")), FM.Enc.name(Source.Name.of("on")), FM.Enc.name(Source.Name.of("n")), FM.Enc.terms(FM.Nats.from(c_1025, 0n)), FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.name(Source.Name.of("Succ")), FM.Enc.name(Source.Name.of("ucc")), FM.Enc.name(Source.Name.of("cc")), FM.Enc.name(Source.Name.of("c")), FM.Enc.term(Source.Term.Tup{Source.Q1{}, Source.Term.Lab{Source.Name.of("Zero")}, Source.Term.Lab{Source.Name.of("()")}}), FM.Enc.p(FM.Enc.term(Source.Term.Lab{Source.Name.of("Zero")}), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")})), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")}), FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.term(Source.Term.Lab{Source.Name.of("Zero")}), FM.Enc.name(Source.Name.of("Zero")), FM.Enc.name(Source.Name.of("ero")), FM.Enc.name(Source.Name.of("ro")), FM.Enc.name(Source.Name.of("o")), Fun.V.z{}, FM.Enc.def(dr_1028), Fun.V.z{}, FM.Enc.name(bs_1027), FM.Enc.book(bk_1022), FM.Enc.mname(Some{bs_1027}), FM.Enc.mdef(Some{dr_1028}), FM.Enc.nat(c_1025)], ks}}),
            FP.Reach.trans(Code.prog(), Fun.F.iter(19n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Entry.k2(), [FM.Enc.term(FM.Input.term(bs_1027, FM.Nats.from(c_1025, 0n))), FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.name(Source.Name.of("Nil")), FM.Enc.name(Source.Name.of("il")), FM.Enc.name(Source.Name.of("l")), FM.Enc.name(Source.Name.of("Con")), FM.Enc.name(Source.Name.of("on")), FM.Enc.name(Source.Name.of("n")), FM.Enc.terms(FM.Nats.from(c_1025, 0n)), FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.name(Source.Name.of("Succ")), FM.Enc.name(Source.Name.of("ucc")), FM.Enc.name(Source.Name.of("cc")), FM.Enc.name(Source.Name.of("c")), FM.Enc.term(Source.Term.Tup{Source.Q1{}, Source.Term.Lab{Source.Name.of("Zero")}, Source.Term.Lab{Source.Name.of("()")}}), FM.Enc.p(FM.Enc.term(Source.Term.Lab{Source.Name.of("Zero")}), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")})), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")}), FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.term(Source.Term.Lab{Source.Name.of("Zero")}), FM.Enc.name(Source.Name.of("Zero")), FM.Enc.name(Source.Name.of("ero")), FM.Enc.name(Source.Name.of("ro")), FM.Enc.name(Source.Name.of("o")), Fun.V.z{}, FM.Enc.def(dr_1028), Fun.V.z{}, FM.Enc.name(bs_1027), FM.Enc.book(bk_1022), FM.Enc.mname(Some{bs_1027}), FM.Enc.mdef(Some{dr_1028}), FM.Enc.nat(c_1025)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.book(List.append(&2, Source.Def, bk_1022, Con{Source.Def{Source.Name.of("bootstrap.input"), ty_1026, FM.Input.term(bs_1027, FM.Nats.from(c_1025, 0n)), False{}}, Con{dr_1028, Nil{}}})), Con{Fun.Fr{Code.F.Entry.k3(), [FM.Enc.book(Con{Source.Def{Source.Name.of("bootstrap.input"), ty_1026, FM.Input.term(bs_1027, FM.Nats.from(c_1025, 0n)), False{}}, Con{dr_1028, Nil{}}}), FM.Enc.book(Con{dr_1028, Nil{}}), FM.Enc.def(Source.Def{Source.Name.of("bootstrap.input"), ty_1026, FM.Input.term(bs_1027, FM.Nats.from(c_1025, 0n)), False{}}), FM.Enc.name(Source.Name.of("bootstrap.input")), FM.Enc.name(Source.Name.of("ootstrap.input")), FM.Enc.name(Source.Name.of("otstrap.input")), FM.Enc.name(Source.Name.of("tstrap.input")), FM.Enc.name(Source.Name.of("strap.input")), FM.Enc.name(Source.Name.of("trap.input")), FM.Enc.name(Source.Name.of("rap.input")), FM.Enc.name(Source.Name.of("ap.input")), FM.Enc.name(Source.Name.of("p.input")), FM.Enc.name(Source.Name.of(".input")), FM.Enc.name(Source.Name.of("input")), FM.Enc.name(Source.Name.of("nput")), FM.Enc.name(Source.Name.of("put")), FM.Enc.name(Source.Name.of("ut")), FM.Enc.name(Source.Name.of("t")), FM.Enc.term(FM.Input.term(bs_1027, FM.Nats.from(c_1025, 0n))), FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.name(Source.Name.of("Nil")), FM.Enc.name(Source.Name.of("il")), FM.Enc.name(Source.Name.of("l")), FM.Enc.name(Source.Name.of("Con")), FM.Enc.name(Source.Name.of("on")), FM.Enc.name(Source.Name.of("n")), FM.Enc.terms(FM.Nats.from(c_1025, 0n)), FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.name(Source.Name.of("Succ")), FM.Enc.name(Source.Name.of("ucc")), FM.Enc.name(Source.Name.of("cc")), FM.Enc.name(Source.Name.of("c")), FM.Enc.term(Source.Term.Tup{Source.Q1{}, Source.Term.Lab{Source.Name.of("Zero")}, Source.Term.Lab{Source.Name.of("()")}}), FM.Enc.p(FM.Enc.term(Source.Term.Lab{Source.Name.of("Zero")}), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")})), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")}), FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.term(Source.Term.Lab{Source.Name.of("Zero")}), FM.Enc.name(Source.Name.of("Zero")), FM.Enc.name(Source.Name.of("ero")), FM.Enc.name(Source.Name.of("ro")), FM.Enc.name(Source.Name.of("o")), Fun.V.z{}, FM.Enc.def(dr_1028), Fun.V.z{}, FM.Enc.name(bs_1027), FM.Enc.book(bk_1022), FM.Enc.mname(Some{bs_1027}), FM.Enc.mdef(Some{dr_1028}), FM.Enc.nat(c_1025)]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.mstart(Some{FM.Start{FM.Start.eval(Source.Name.of("bootstrap.run")), List.append(&2, Source.Def, bk_1022, [Source.Def{Source.Name.of("bootstrap.input"), ty_1026, FM.Input.term(bs_1027, FM.Nats.from(c_1025, 0n)), False{}}, dr_1028])}}), ks}},
            L.Book.append(bk_1022, Con{Source.Def{Source.Name.of("bootstrap.input"), ty_1026, FM.Input.term(bs_1027, FM.Nats.from(c_1025, 0n)), False{}}, Con{dr_1028, Nil{}}}, Con{Fun.Fr{Code.F.Entry.k3(), [FM.Enc.book(Con{Source.Def{Source.Name.of("bootstrap.input"), ty_1026, FM.Input.term(bs_1027, FM.Nats.from(c_1025, 0n)), False{}}, Con{dr_1028, Nil{}}}), FM.Enc.book(Con{dr_1028, Nil{}}), FM.Enc.def(Source.Def{Source.Name.of("bootstrap.input"), ty_1026, FM.Input.term(bs_1027, FM.Nats.from(c_1025, 0n)), False{}}), FM.Enc.name(Source.Name.of("bootstrap.input")), FM.Enc.name(Source.Name.of("ootstrap.input")), FM.Enc.name(Source.Name.of("otstrap.input")), FM.Enc.name(Source.Name.of("tstrap.input")), FM.Enc.name(Source.Name.of("strap.input")), FM.Enc.name(Source.Name.of("trap.input")), FM.Enc.name(Source.Name.of("rap.input")), FM.Enc.name(Source.Name.of("ap.input")), FM.Enc.name(Source.Name.of("p.input")), FM.Enc.name(Source.Name.of(".input")), FM.Enc.name(Source.Name.of("input")), FM.Enc.name(Source.Name.of("nput")), FM.Enc.name(Source.Name.of("put")), FM.Enc.name(Source.Name.of("ut")), FM.Enc.name(Source.Name.of("t")), FM.Enc.term(FM.Input.term(bs_1027, FM.Nats.from(c_1025, 0n))), FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.name(Source.Name.of("Nil")), FM.Enc.name(Source.Name.of("il")), FM.Enc.name(Source.Name.of("l")), FM.Enc.name(Source.Name.of("Con")), FM.Enc.name(Source.Name.of("on")), FM.Enc.name(Source.Name.of("n")), FM.Enc.terms(FM.Nats.from(c_1025, 0n)), FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.name(Source.Name.of("Succ")), FM.Enc.name(Source.Name.of("ucc")), FM.Enc.name(Source.Name.of("cc")), FM.Enc.name(Source.Name.of("c")), FM.Enc.term(Source.Term.Tup{Source.Q1{}, Source.Term.Lab{Source.Name.of("Zero")}, Source.Term.Lab{Source.Name.of("()")}}), FM.Enc.p(FM.Enc.term(Source.Term.Lab{Source.Name.of("Zero")}), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")})), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")}), FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.term(Source.Term.Lab{Source.Name.of("Zero")}), FM.Enc.name(Source.Name.of("Zero")), FM.Enc.name(Source.Name.of("ero")), FM.Enc.name(Source.Name.of("ro")), FM.Enc.name(Source.Name.of("o")), Fun.V.z{}, FM.Enc.def(dr_1028), Fun.V.z{}, FM.Enc.name(bs_1027), FM.Enc.book(bk_1022), FM.Enc.mname(Some{bs_1027}), FM.Enc.mdef(Some{dr_1028}), FM.Enc.nat(c_1025)]}, ks}),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.book(List.append(&2, Source.Def, bk_1022, Con{Source.Def{Source.Name.of("bootstrap.input"), ty_1026, FM.Input.term(bs_1027, FM.Nats.from(c_1025, 0n)), False{}}, Con{dr_1028, Nil{}}})), Con{Fun.Fr{Code.F.Entry.k3(), [FM.Enc.book(Con{Source.Def{Source.Name.of("bootstrap.input"), ty_1026, FM.Input.term(bs_1027, FM.Nats.from(c_1025, 0n)), False{}}, Con{dr_1028, Nil{}}}), FM.Enc.book(Con{dr_1028, Nil{}}), FM.Enc.def(Source.Def{Source.Name.of("bootstrap.input"), ty_1026, FM.Input.term(bs_1027, FM.Nats.from(c_1025, 0n)), False{}}), FM.Enc.name(Source.Name.of("bootstrap.input")), FM.Enc.name(Source.Name.of("ootstrap.input")), FM.Enc.name(Source.Name.of("otstrap.input")), FM.Enc.name(Source.Name.of("tstrap.input")), FM.Enc.name(Source.Name.of("strap.input")), FM.Enc.name(Source.Name.of("trap.input")), FM.Enc.name(Source.Name.of("rap.input")), FM.Enc.name(Source.Name.of("ap.input")), FM.Enc.name(Source.Name.of("p.input")), FM.Enc.name(Source.Name.of(".input")), FM.Enc.name(Source.Name.of("input")), FM.Enc.name(Source.Name.of("nput")), FM.Enc.name(Source.Name.of("put")), FM.Enc.name(Source.Name.of("ut")), FM.Enc.name(Source.Name.of("t")), FM.Enc.term(FM.Input.term(bs_1027, FM.Nats.from(c_1025, 0n))), FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.name(Source.Name.of("Nil")), FM.Enc.name(Source.Name.of("il")), FM.Enc.name(Source.Name.of("l")), FM.Enc.name(Source.Name.of("Con")), FM.Enc.name(Source.Name.of("on")), FM.Enc.name(Source.Name.of("n")), FM.Enc.terms(FM.Nats.from(c_1025, 0n)), FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.name(Source.Name.of("Succ")), FM.Enc.name(Source.Name.of("ucc")), FM.Enc.name(Source.Name.of("cc")), FM.Enc.name(Source.Name.of("c")), FM.Enc.term(Source.Term.Tup{Source.Q1{}, Source.Term.Lab{Source.Name.of("Zero")}, Source.Term.Lab{Source.Name.of("()")}}), FM.Enc.p(FM.Enc.term(Source.Term.Lab{Source.Name.of("Zero")}), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")})), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")}), FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.term(Source.Term.Lab{Source.Name.of("Zero")}), FM.Enc.name(Source.Name.of("Zero")), FM.Enc.name(Source.Name.of("ero")), FM.Enc.name(Source.Name.of("ro")), FM.Enc.name(Source.Name.of("o")), Fun.V.z{}, FM.Enc.def(dr_1028), Fun.V.z{}, FM.Enc.name(bs_1027), FM.Enc.book(bk_1022), FM.Enc.mname(Some{bs_1027}), FM.Enc.mdef(Some{dr_1028}), FM.Enc.nat(c_1025)]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.book(List.append(&2, Source.Def, bk_1022, Con{Source.Def{Source.Name.of("bootstrap.input"), ty_1026, FM.Input.term(bs_1027, FM.Nats.from(c_1025, 0n)), False{}}, Con{dr_1028, Nil{}}})), Con{Fun.Fr{Code.F.Entry.k3(), [FM.Enc.book(Con{Source.Def{Source.Name.of("bootstrap.input"), ty_1026, FM.Input.term(bs_1027, FM.Nats.from(c_1025, 0n)), False{}}, Con{dr_1028, Nil{}}}), FM.Enc.book(Con{dr_1028, Nil{}}), FM.Enc.def(Source.Def{Source.Name.of("bootstrap.input"), ty_1026, FM.Input.term(bs_1027, FM.Nats.from(c_1025, 0n)), False{}}), FM.Enc.name(Source.Name.of("bootstrap.input")), FM.Enc.name(Source.Name.of("ootstrap.input")), FM.Enc.name(Source.Name.of("otstrap.input")), FM.Enc.name(Source.Name.of("tstrap.input")), FM.Enc.name(Source.Name.of("strap.input")), FM.Enc.name(Source.Name.of("trap.input")), FM.Enc.name(Source.Name.of("rap.input")), FM.Enc.name(Source.Name.of("ap.input")), FM.Enc.name(Source.Name.of("p.input")), FM.Enc.name(Source.Name.of(".input")), FM.Enc.name(Source.Name.of("input")), FM.Enc.name(Source.Name.of("nput")), FM.Enc.name(Source.Name.of("put")), FM.Enc.name(Source.Name.of("ut")), FM.Enc.name(Source.Name.of("t")), FM.Enc.term(FM.Input.term(bs_1027, FM.Nats.from(c_1025, 0n))), FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.name(Source.Name.of("Nil")), FM.Enc.name(Source.Name.of("il")), FM.Enc.name(Source.Name.of("l")), FM.Enc.name(Source.Name.of("Con")), FM.Enc.name(Source.Name.of("on")), FM.Enc.name(Source.Name.of("n")), FM.Enc.terms(FM.Nats.from(c_1025, 0n)), FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.name(Source.Name.of("Succ")), FM.Enc.name(Source.Name.of("ucc")), FM.Enc.name(Source.Name.of("cc")), FM.Enc.name(Source.Name.of("c")), FM.Enc.term(Source.Term.Tup{Source.Q1{}, Source.Term.Lab{Source.Name.of("Zero")}, Source.Term.Lab{Source.Name.of("()")}}), FM.Enc.p(FM.Enc.term(Source.Term.Lab{Source.Name.of("Zero")}), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")})), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")}), FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.term(Source.Term.Lab{Source.Name.of("Zero")}), FM.Enc.name(Source.Name.of("Zero")), FM.Enc.name(Source.Name.of("ero")), FM.Enc.name(Source.Name.of("ro")), FM.Enc.name(Source.Name.of("o")), Fun.V.z{}, FM.Enc.def(dr_1028), Fun.V.z{}, FM.Enc.name(bs_1027), FM.Enc.book(bk_1022), FM.Enc.mname(Some{bs_1027}), FM.Enc.mdef(Some{dr_1028}), FM.Enc.nat(c_1025)]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.mstart(Some{FM.Start{FM.Start.eval(Source.Name.of("bootstrap.run")), List.append(&2, Source.Def, bk_1022, [Source.Def{Source.Name.of("bootstrap.input"), ty_1026, FM.Input.term(bs_1027, FM.Nats.from(c_1025, 0n)), False{}}, dr_1028])}}), ks}},
            FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.book(List.append(&2, Source.Def, bk_1022, Con{Source.Def{Source.Name.of("bootstrap.input"), ty_1026, FM.Input.term(bs_1027, FM.Nats.from(c_1025, 0n)), False{}}, Con{dr_1028, Nil{}}})), Con{Fun.Fr{Code.F.Entry.k3(), [FM.Enc.book(Con{Source.Def{Source.Name.of("bootstrap.input"), ty_1026, FM.Input.term(bs_1027, FM.Nats.from(c_1025, 0n)), False{}}, Con{dr_1028, Nil{}}}), FM.Enc.book(Con{dr_1028, Nil{}}), FM.Enc.def(Source.Def{Source.Name.of("bootstrap.input"), ty_1026, FM.Input.term(bs_1027, FM.Nats.from(c_1025, 0n)), False{}}), FM.Enc.name(Source.Name.of("bootstrap.input")), FM.Enc.name(Source.Name.of("ootstrap.input")), FM.Enc.name(Source.Name.of("otstrap.input")), FM.Enc.name(Source.Name.of("tstrap.input")), FM.Enc.name(Source.Name.of("strap.input")), FM.Enc.name(Source.Name.of("trap.input")), FM.Enc.name(Source.Name.of("rap.input")), FM.Enc.name(Source.Name.of("ap.input")), FM.Enc.name(Source.Name.of("p.input")), FM.Enc.name(Source.Name.of(".input")), FM.Enc.name(Source.Name.of("input")), FM.Enc.name(Source.Name.of("nput")), FM.Enc.name(Source.Name.of("put")), FM.Enc.name(Source.Name.of("ut")), FM.Enc.name(Source.Name.of("t")), FM.Enc.term(FM.Input.term(bs_1027, FM.Nats.from(c_1025, 0n))), FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.name(Source.Name.of("Nil")), FM.Enc.name(Source.Name.of("il")), FM.Enc.name(Source.Name.of("l")), FM.Enc.name(Source.Name.of("Con")), FM.Enc.name(Source.Name.of("on")), FM.Enc.name(Source.Name.of("n")), FM.Enc.terms(FM.Nats.from(c_1025, 0n)), FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.name(Source.Name.of("Succ")), FM.Enc.name(Source.Name.of("ucc")), FM.Enc.name(Source.Name.of("cc")), FM.Enc.name(Source.Name.of("c")), FM.Enc.term(Source.Term.Tup{Source.Q1{}, Source.Term.Lab{Source.Name.of("Zero")}, Source.Term.Lab{Source.Name.of("()")}}), FM.Enc.p(FM.Enc.term(Source.Term.Lab{Source.Name.of("Zero")}), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")})), FM.Enc.term(Source.Term.Lab{Source.Name.of("()")}), FM.Enc.name(Source.Name.of("()")), FM.Enc.name(Source.Name.of(")")), FM.Enc.term(Source.Term.Lab{Source.Name.of("Zero")}), FM.Enc.name(Source.Name.of("Zero")), FM.Enc.name(Source.Name.of("ero")), FM.Enc.name(Source.Name.of("ro")), FM.Enc.name(Source.Name.of("o")), Fun.V.z{}, FM.Enc.def(dr_1028), Fun.V.z{}, FM.Enc.name(bs_1027), FM.Enc.book(bk_1022), FM.Enc.mname(Some{bs_1027}), FM.Enc.mdef(Some{dr_1028}), FM.Enc.nat(c_1025)]}, ks}}}),
            (19n, {==}))))))))))


# Numbers
# =======

def Nat.add_zero(a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, 0n), p, Nat.add_zero(p))

def Nat.add_succ(a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, 1n+b), 1n+Nat.add(p, b), Nat.add_succ(p, b))

# The input
# =========

# the term at b of the terms of the numbers i to i + c, for b at most c
def Terms.at_from(b: Nat, c: Nat, +i: Nat, h: {Nat.is_le(b, c) == True{} : Bool}) ->
  {FM.Terms.at(FM.Nats.from(c, i), b) == Source.Bytes.nat(Nat.add(b, i)) : Source.Term}:
  match b:
    case 0n:
      match c:
        case 0n:
          {==}
        case 1n+d:
          {==}
    case 1n++p:
      match c:
        case 0n:
          Shared.Bool.absurd({FM.Terms.at(FM.Nats.from(0n, i), 1n+p) == Source.Bytes.nat(Nat.add(1n+p, i)) : Source.Term}, h)
        case 1n++d:
          %Nat.add_succ(p, i) : {FM.Terms.at(FM.Nats.from(d, 1n+i), p) == Source.Bytes.nat(_) : Source.Term}
          Terms.at_from(p, d, 1n+i, h)

def Input.term_eq(bs: List<&2, Nat>, +c: Nat, +h: {Spec.Input.le(bs, c) == True{} : Bool}) ->
  {FM.Input.term(bs, FM.Nats.from(c, 0n)) == Source.Bytes.term(bs) : Source.Term}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, +rest}:
      %Input.term_eq(rest, c, SP.Bool.and_right(Nat.is_le(b, c), Spec.Input.le(rest, c), h)) :
        {FM.Input.term(Con{b, rest}, FM.Nats.from(c, 0n)) ==
          Source.Term.Tup{Source.Q1{}, Source.Term.Lab{Source.Name.of("Con")}, Source.Term.Tup{Source.Q1{}, Source.Bytes.nat(b),
            Source.Term.Tup{Source.Q1{}, _, Source.Term.Lab{Source.Name.of("()")}}}} : Source.Term}
      %Nat.add_zero(b) :
        {FM.Input.term(Con{b, rest}, FM.Nats.from(c, 0n)) ==
          Source.Term.Tup{Source.Q1{}, Source.Term.Lab{Source.Name.of("Con")}, Source.Term.Tup{Source.Q1{}, Source.Bytes.nat(_),
            Source.Term.Tup{Source.Q1{}, FM.Input.term(rest, FM.Nats.from(c, 0n)), Source.Term.Lab{Source.Name.of("()")}}}} : Source.Term}
      %Terms.at_from(b, c, 0n, SP.Bool.and_left(Nat.is_le(b, c), Spec.Input.le(rest, c), h)) :
        {FM.Input.term(Con{b, rest}, FM.Nats.from(c, 0n)) ==
          Source.Term.Tup{Source.Q1{}, Source.Term.Lab{Source.Name.of("Con")}, Source.Term.Tup{Source.Q1{}, _,
            Source.Term.Tup{Source.Q1{}, FM.Input.term(rest, FM.Nats.from(c, 0n)), Source.Term.Lab{Source.Name.of("()")}}}} : Source.Term}
      {==}

# the run of a start
def Start.run(n: Nat, m: Maybe<&2, FM.Start>) -> Maybe<&2, Source.Obs>:
  match m:
    case Some{FM.Start{s, bk}}:
      Machine.Machine.run(n, s, bk)
    case None{}:
      None{}

def Entry.eq.got(d: Maybe<&2, Source.Def>, +n: Nat, +bs: List<&2, Nat>, +bk: List<&2, Source.Def>, +c: Nat,
  +h: {Spec.Input.le(bs, c) == True{} : Bool}) ->
  {Spec.Run.at(n, Source.Entry.run(Source.Input.apply.of(d, bk, bs))) ==
    Start.run(n, FM.Start.of(bk, Some{bs}, FM.Input.arg_type.of(d), c, FM.Input.run_def.of(d))) : Maybe<&2, Source.Obs>}:
  match d:
    case None{}:
      {==}
    case Some{+df}:
      match df:
        case Source.Def{+k, +t, +v, +o}:
          match t:
            case Source.Term.Var{+i}:
              {==}
            case Source.Term.Ref{+k}:
              {==}
            case Source.Term.Ann{+x, +t}:
              {==}
            case Source.Term.Let{+q, +v, +f}:
              {==}
            case Source.Term.Typ{+q}:
              {==}
            case Source.Term.Min{+a, +b}:
              {==}
            case Source.Term.All{+q, +a, +b}:
              Equal.cong(Source.Term, Maybe<&2, Source.Obs>, x => Machine.Machine.run(n, FM.Start.eval(Source.Name.of("bootstrap.run")), List.append(&2, Source.Def, bk, [Source.Def{Source.Name.of("bootstrap.input"), a, x, False{}}, Source.Def{Source.Name.of("bootstrap.run"), Source.Term.sub(b, 0n, Source.Sub.one{Source.Term.Ref{Source.Name.of("bootstrap.input")}}), Source.Term.App{q, Source.Term.Ref{Source.Name.of("main")}, Source.Term.Ref{Source.Name.of("bootstrap.input")}}, False{}}])), Source.Bytes.term(bs), FM.Input.term(bs, FM.Nats.from(c, 0n)), Equal.sym(Source.Term, FM.Input.term(bs, FM.Nats.from(c, 0n)), Source.Bytes.term(bs), Input.term_eq(bs, c, h)))
            case Source.Term.Lam{+q, +f}:
              {==}
            case Source.Term.App{+q, +f, +x}:
              {==}
            case Source.Term.Sig{+q, +a, +b}:
              {==}
            case Source.Term.Tup{+q, +a, +b}:
              {==}
            case Source.Term.Prj{+h}:
              {==}
            case Source.Term.Enu{+ks}:
              {==}
            case Source.Term.Lab{+k}:
              {==}
            case Source.Term.Mat{+k, +h, +m}:
              {==}
            case Source.Term.Efq{}:
              {==}
            case Source.Term.Eql{+a, +b, +t}:
              {==}
            case Source.Term.Rfl{}:
              {==}
            case Source.Term.Rwt{+e, +p, +f}:
              {==}

def Entry.eq(n: Nat, input: Maybe<&2, List<&2, Nat>>, +bk: List<&2, Source.Def>, +c: Nat,
  +h: {Spec.Input.ok(input, c) == True{} : Bool}) ->
  {Spec.Run.at(n, Source.entry(input, bk)) ==
    Start.run(n, FM.Start.of(bk, input, FM.Input.arg_type(bk), c, FM.Input.run_def(bk))) : Maybe<&2, Source.Obs>}:
  match input:
    case None{}:
      {==}
    case Some{+bs}:
      Entry.eq.got(Source.Book.get(bk, Source.Name.of("main")), n, bs, bk, c, h)

# The run
# =======

def Run.X(+s: Machine.St, +bk: List<&2, Source.Def>, +ks: List<&2, Fun.Fr>) -> Fun.Step:
  Fun.Step.go{Fun.S.run{Code.F.Run(), [FM.Enc.st(s), FM.Enc.book(bk)], ks}}

def Run.k1(+m: Machine.Move, +s: Machine.St, +bk: List<&2, Source.Def>, +ks: List<&2, Fun.Fr>) -> Fun.Step:
  Fun.Step.go{Fun.S.run{Code.F.Run.k1(), [FM.Enc.move(m), FM.Enc.st(s), FM.Enc.book(bk)], ks}}

def Run.k2(+mo: Maybe<&2, Source.Obs>, +v: Machine.Val, +s: Machine.St, +bk: List<&2, Source.Def>,
  +ks: List<&2, Fun.Fr>) -> Fun.Step:
  Fun.Step.go{Fun.S.run{Code.F.Run.k2(), [FM.Enc.mobs(mo), Fun.V.z{}, FM.Enc.val(v), FM.Enc.move(Machine.Move.done{v}),
    FM.Enc.st(s), FM.Enc.book(bk)], ks}}

def Run.out(+o: Source.Obs, +ks: List<&2, Fun.Fr>) -> Fun.Step:
  Fun.Step.go{Fun.S.ret{FM.Enc.name(Contract.Out.of(o)), ks}}

def Run.fr1(+s: Machine.St, +bk: List<&2, Source.Def>, +ks: List<&2, Fun.Fr>) -> List<&2, Fun.Fr>:
  Con{Fun.Fr{Code.F.Run.k1(), [FM.Enc.st(s), FM.Enc.book(bk)]}, ks}

def Run.fr2(+v: Machine.Val, +s: Machine.St, +bk: List<&2, Source.Def>, +ks: List<&2, Fun.Fr>) -> List<&2, Fun.Fr>:
  Con{Fun.Fr{Code.F.Run.k2(), [Fun.V.z{}, FM.Enc.val(v), FM.Enc.move(Machine.Move.done{v}), FM.Enc.st(s), FM.Enc.book(bk)]},
    ks}

# the step, from the start of Run
def Run.to_k1(+s: Machine.St, +bk: List<&2, Source.Def>, +ks: List<&2, Fun.Fr>) ->
  Fun.Reach1(Code.prog(), Run.X(s, bk, ks), Run.k1(Machine.Machine.step(s, bk), s, bk, ks)):
  FP.Reach1.of(Code.prog(), Run.X(s, bk, ks), Run.k1(Machine.Machine.step(s, bk), s, bk, ks),
    FP.Reach.trans(Code.prog(), Fun.F.iter(1n, Code.prog(), Run.X(s, bk, ks)),
      Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Machine.step(s, bk)), Run.fr1(s, bk, ks)}},
      Run.k1(Machine.Machine.step(s, bk), s, bk, ks),
      L.Machine.step(s, bk, Run.fr1(s, bk, ks)),
      FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Machine.step(s, bk)), Run.fr1(s, bk, ks)}})))

# the observation, after a step that is done
def Run.to_k2(+v: Machine.Val, +s: Machine.St, +bk: List<&2, Source.Def>, +ks: List<&2, Fun.Fr>) ->
  Fun.Reach(Code.prog(), Run.k1(Machine.Move.done{v}, s, bk, ks), Run.k2(Machine.Val.observe(v), v, s, bk, ks)):
  FP.Reach.trans(Code.prog(), Run.k1(Machine.Move.done{v}, s, bk, ks),
    Fun.F.iter(3n, Code.prog(), Run.k1(Machine.Move.done{v}, s, bk, ks)), Run.k2(Machine.Val.observe(v), v, s, bk, ks),
    FP.Reach.steps(3n, Code.prog(), Run.k1(Machine.Move.done{v}, s, bk, ks)),
    FP.Reach.trans(Code.prog(), Fun.F.iter(3n, Code.prog(), Run.k1(Machine.Move.done{v}, s, bk, ks)),
      Fun.Step.go{Fun.S.ret{FM.Enc.mobs(Machine.Val.observe(v)), Run.fr2(v, s, bk, ks)}},
      Run.k2(Machine.Val.observe(v), v, s, bk, ks),
      L.Val.observe(v, Run.fr2(v, s, bk, ks)),
      FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.mobs(Machine.Val.observe(v)), Run.fr2(v, s, bk, ks)}})))

def Obs.value(m: Maybe<&2, Source.Obs>, d: Source.Obs) -> Source.Obs:
  match m:
    case Some{o}:
      o
    case None{}:
      d

def Run.keeps.k2(mo: Maybe<&2, Source.Obs>, +v: Machine.Val, +s: Machine.St, +bk: List<&2, Source.Def>, +o: Source.Obs,
  +ks: List<&2, Fun.Fr>, +h: {mo == Some{o} : Maybe<&2, Source.Obs>}) ->
  Fun.Reach(Code.prog(), Run.k2(mo, v, s, bk, ks), Run.out(o, ks)):
  match mo:
    case None{}:
      Empty.absurd(Fun.Reach(Code.prog(), Run.k2(None{}, v, s, bk, ks), Run.out(o, ks)), Shared.Maybe.no_none(Source.Obs, o, h))
    case Some{+ob}:
      %Equal.cong(Maybe<&2, Source.Obs>, Source.Obs, m => Obs.value(m, ob), Some{ob}, Some{o}, h) :
        Fun.Reach(Code.prog(), Run.k2(Some{ob}, v, s, bk, ks), Run.out(_, ks))
      FP.Reach.trans(Code.prog(), Run.k2(Some{ob}, v, s, bk, ks), Fun.F.iter(2n, Code.prog(), Run.k2(Some{ob}, v, s, bk, ks)),
        Run.out(ob, ks), FP.Reach.steps(2n, Code.prog(), Run.k2(Some{ob}, v, s, bk, ks)), L.Out.of(ob, ks))

# Run ends with the output of the machine's result
def Run.keeps(n: Nat, +s: Machine.St, +bk: List<&2, Source.Def>, +o: Source.Obs, +ks: List<&2, Fun.Fr>,
  +h: {Machine.Machine.run(n, s, bk) == Some{o} : Maybe<&2, Source.Obs>}) ->
  Fun.Reach(Code.prog(), Run.X(s, bk, ks), Run.out(o, ks)):
  match n:
    case 0n:
      Empty.absurd(Fun.Reach(Code.prog(), Run.X(s, bk, ks), Run.out(o, ks)), Shared.Maybe.no_none(Source.Obs, o, h))
    case 1n+m:
      FP.Reach.trans(Code.prog(), Run.X(s, bk, ks), Run.k1(Machine.Machine.step(s, bk), s, bk, ks), Run.out(o, ks),
        FP.Reach1.reach(Code.prog(), Run.X(s, bk, ks), Run.k1(Machine.Machine.step(s, bk), s, bk, ks), Run.to_k1(s, bk, ks)),
        Elim.Move(Machine.Machine.step(s, bk),
          x => ({Machine.Run.next(x, s2 => Machine.Machine.run(m, s2, bk)) == Some{o} : Maybe<&2, Source.Obs>} ->
            Fun.Reach(Code.prog(), Run.k1(x, s, bk, ks), Run.out(o, ks))),
          +s2 => hx => FP.Reach.trans(Code.prog(), Run.k1(Machine.Move.go{s2}, s, bk, ks), Run.X(s2, bk, ks), Run.out(o, ks),
            FP.Reach.steps(2n, Code.prog(), Run.k1(Machine.Move.go{s2}, s, bk, ks)),
            Run.keeps(m, s2, bk, o, ks, hx)),
          +v => hx => FP.Reach.trans(Code.prog(), Run.k1(Machine.Move.done{v}, s, bk, ks),
            Run.k2(Machine.Val.observe(v), v, s, bk, ks), Run.out(o, ks),
            Run.to_k2(v, s, bk, ks),
            Run.keeps.k2(Machine.Val.observe(v), v, s, bk, o, ks, hx)),
          hx => Empty.absurd(Fun.Reach(Code.prog(), Run.k1(Machine.Move.stuck{}, s, bk, ks), Run.out(o, ks)),
            Shared.Maybe.no_none(Source.Obs, o, hx)))(h))

def Run.adds.zero(N: Nat, +s: Machine.St, +bk: List<&2, Source.Def>, +w: Fun.V,
  +h1: {Fun.F.iter(N, Code.prog(), Run.X(s, bk, [])) == Fun.Step.halt{w} : Fun.Step},
  +h2: {Nat.is_le(N, 0n) == True{} : Bool}) ->
  {Spec.Res(Machine.Machine.run(0n, s, bk)) == Some{w} : Maybe<&2, Fun.V>}:
  match N:
    case 0n:
      Shared.Bool.absurd({Spec.Res(Machine.Machine.run(0n, s, bk)) == Some{w} : Maybe<&2, Fun.V>},
        Equal.cong(Fun.Step, Bool, x => FP.Step.is_halt(x), Run.X(s, bk, []), Fun.Step.halt{w}, h1))
    case 1n+M:
      Shared.Bool.absurd({Spec.Res(Machine.Machine.run(0n, s, bk)) == Some{w} : Maybe<&2, Fun.V>}, h2)

def Run.adds.after(+N: Nat, +k: Nat, +s2: Machine.St, +bk: List<&2, Source.Def>, +w: Fun.V,
  +h2: {Nat.is_le(N, 1n+k) == True{} : Bool},
  ih: @M: Nat -> {Fun.F.iter(M, Code.prog(), Run.X(s2, bk, [])) == Fun.Step.halt{w} : Fun.Step} ->
    {Nat.is_le(M, k) == True{} : Bool} -> {Spec.Res(Machine.Machine.run(k, s2, bk)) == Some{w} : Maybe<&2, Fun.V>},
  a: FP.After(Code.prog(), N, Run.X(s2, bk, []), w)) ->
  {Spec.Res(Machine.Machine.run(k, s2, bk)) == Some{w} : Maybe<&2, Fun.V>}:
  (+M, +p) = a
  (+h3, +lt) = p
  ih(M, h3, Shared.Nat.is_le_trans(1n+M, N, 1n+k, lt, h2))

def Run.adds.go(+N: Nat, +k: Nat, +s: Machine.St, +s2: Machine.St, +bk: List<&2, Source.Def>, +w: Fun.V,
  +h1: {Fun.F.iter(N, Code.prog(), Run.X(s, bk, [])) == Fun.Step.halt{w} : Fun.Step},
  +h2: {Nat.is_le(N, 1n+k) == True{} : Bool},
  r: Fun.Reach1(Code.prog(), Run.X(s, bk, []), Run.X(s2, bk, [])),
  ih: @M: Nat -> {Fun.F.iter(M, Code.prog(), Run.X(s2, bk, [])) == Fun.Step.halt{w} : Fun.Step} ->
    {Nat.is_le(M, k) == True{} : Bool} -> {Spec.Res(Machine.Machine.run(k, s2, bk)) == Some{w} : Maybe<&2, Fun.V>}) ->
  {Spec.Res(Machine.Machine.run(k, s2, bk)) == Some{w} : Maybe<&2, Fun.V>}:
  (+n, +e) = r
  Run.adds.after(N, k, s2, bk, w, h2, ih,
    FP.Iter.after(N, n, Code.prog(), Run.X(s, bk, []), Run.X(s2, bk, []), w, e, {==}, h1))

def Run.adds.k2(mo: Maybe<&2, Source.Obs>, +N: Nat, +v: Machine.Val, +s: Machine.St, +bk: List<&2, Source.Def>,
  +w: Fun.V, +h1: {Fun.F.iter(N, Code.prog(), Run.X(s, bk, [])) == Fun.Step.halt{w} : Fun.Step},
  r: Fun.Reach(Code.prog(), Run.X(s, bk, []), Run.k2(mo, v, s, bk, []))) ->
  {Spec.Res(mo) == Some{w} : Maybe<&2, Fun.V>}:
  match mo:
    case None{}:
      Empty.absurd({Spec.Res(None{}) == Some{w} : Maybe<&2, Fun.V>},
        FP.Reach.stuck_end(Code.prog(), Run.X(s, bk, []), w,
          FP.Reach.trans(Code.prog(), Run.X(s, bk, []), Run.k2(None{}, v, s, bk, []), Fun.Step.stuck{}, r,
            FP.Reach.steps(2n, Code.prog(), Run.k2(None{}, v, s, bk, []))), N, h1))
    case Some{+ob}:
      Equal.cong(Fun.V, Maybe<&2, Fun.V>, z => Some{z}, FM.Enc.name(Contract.Out.of(ob)), w,
        FP.Reach.det(Code.prog(), Run.X(s, bk, []), FM.Enc.name(Contract.Out.of(ob)), w,
          FP.Reach.trans(Code.prog(), Run.X(s, bk, []), Run.k2(Some{ob}, v, s, bk, []),
            Fun.Step.halt{FM.Enc.name(Contract.Out.of(ob))}, r,
            FP.Reach.trans(Code.prog(), Run.k2(Some{ob}, v, s, bk, []), Run.out(ob, []),
              Fun.Step.halt{FM.Enc.name(Contract.Out.of(ob))},
              FP.Reach.trans(Code.prog(), Run.k2(Some{ob}, v, s, bk, []), Fun.F.iter(2n, Code.prog(), Run.k2(Some{ob}, v, s, bk, [])),
                Run.out(ob, []), FP.Reach.steps(2n, Code.prog(), Run.k2(Some{ob}, v, s, bk, [])), L.Out.of(ob, [])),
              FP.Reach.steps(1n, Code.prog(), Run.out(ob, [])))), N, h1))

def Run.adds.done(+N: Nat, +s: Machine.St, +v: Machine.Val, +bk: List<&2, Source.Def>, +w: Fun.V,
  +h1: {Fun.F.iter(N, Code.prog(), Run.X(s, bk, [])) == Fun.Step.halt{w} : Fun.Step},
  r: Fun.Reach1(Code.prog(), Run.X(s, bk, []), Run.k1(Machine.Move.done{v}, s, bk, []))) ->
  {Spec.Res(Machine.Val.observe(v)) == Some{w} : Maybe<&2, Fun.V>}:
  Run.adds.k2(Machine.Val.observe(v), N, v, s, bk, w, h1,
    FP.Reach.trans(Code.prog(), Run.X(s, bk, []), Run.k1(Machine.Move.done{v}, s, bk, []),
      Run.k2(Machine.Val.observe(v), v, s, bk, []),
      FP.Reach1.reach(Code.prog(), Run.X(s, bk, []), Run.k1(Machine.Move.done{v}, s, bk, []), r),
      Run.to_k2(v, s, bk, [])))

def Run.adds.stuck(+N: Nat, +s: Machine.St, +bk: List<&2, Source.Def>, +w: Fun.V,
  +h1: {Fun.F.iter(N, Code.prog(), Run.X(s, bk, [])) == Fun.Step.halt{w} : Fun.Step},
  r: Fun.Reach1(Code.prog(), Run.X(s, bk, []), Run.k1(Machine.Move.stuck{}, s, bk, []))) ->
  {Spec.Res(None{}) == Some{w} : Maybe<&2, Fun.V>}:
  Empty.absurd({Spec.Res(None{}) == Some{w} : Maybe<&2, Fun.V>},
    FP.Reach.stuck_end(Code.prog(), Run.X(s, bk, []), w,
      FP.Reach.trans(Code.prog(), Run.X(s, bk, []), Run.k1(Machine.Move.stuck{}, s, bk, []), Fun.Step.stuck{},
        FP.Reach1.reach(Code.prog(), Run.X(s, bk, []), Run.k1(Machine.Move.stuck{}, s, bk, []), r),
        FP.Reach.steps(3n, Code.prog(), Run.k1(Machine.Move.stuck{}, s, bk, []))), N, h1))

# an end of Run within k steps of the machine is the output of its result
def Run.adds(k: Nat, +N: Nat, +s: Machine.St, +bk: List<&2, Source.Def>, +w: Fun.V,
  +h1: {Fun.F.iter(N, Code.prog(), Run.X(s, bk, [])) == Fun.Step.halt{w} : Fun.Step},
  +h2: {Nat.is_le(N, k) == True{} : Bool}) ->
  {Spec.Res(Machine.Machine.run(k, s, bk)) == Some{w} : Maybe<&2, Fun.V>}:
  match k:
    case 0n:
      Run.adds.zero(N, s, bk, w, h1, h2)
    case 1n++j:
      Elim.Move(Machine.Machine.step(s, bk),
        x => (Fun.Reach1(Code.prog(), Run.X(s, bk, []), Run.k1(x, s, bk, [])) ->
          {Spec.Res(Machine.Run.next(x, s2 => Machine.Machine.run(j, s2, bk))) == Some{w} : Maybe<&2, Fun.V>}),
        +s2 => r => Run.adds.go(N, j, s, s2, bk, w, h1, h2,
          FP.Reach1.then(Code.prog(), Run.X(s, bk, []), Run.k1(Machine.Move.go{s2}, s, bk, []), Run.X(s2, bk, []), r,
            FP.Reach.steps(2n, Code.prog(), Run.k1(Machine.Move.go{s2}, s, bk, []))),
          M => h3 => h4 => Run.adds(j, M, s2, bk, w, h3, h4)),
        +v => r => Run.adds.done(N, s, v, bk, w, h1, r),
        r => Run.adds.stuck(N, s, bk, w, h1, r))(Run.to_k1(s, bk, []))

# Main
# ====

def Main.X(+bk: List<&2, Source.Def>, +input: Maybe<&2, List<&2, Nat>>, +c: Nat) -> Fun.Step:
  Fun.Step.go{FM.start.of(bk, input, c)}

def Main.k1(+so: Maybe<&2, FM.Start>, +bk: List<&2, Source.Def>, +input: Maybe<&2, List<&2, Nat>>, +c: Nat) -> Fun.Step:
  Fun.Step.go{Fun.S.run{Code.F.Main.k1(), [FM.Enc.mstart(so), FM.Enc.book(bk), FM.Enc.mname(input),
    FM.Enc.mdef(FM.Input.run_def(bk)), FM.Enc.nat(c)], []}}

def Main.so(+bk: List<&2, Source.Def>, +input: Maybe<&2, List<&2, Nat>>, +c: Nat) -> Maybe<&2, FM.Start>:
  FM.Start.of(bk, input, FM.Input.arg_type(bk), c, FM.Input.run_def(bk))

def Main.fr(+bk: List<&2, Source.Def>, +input: Maybe<&2, List<&2, Nat>>, +c: Nat) -> List<&2, Fun.Fr>:
  [Fun.Fr{Code.F.Main.k1(), [FM.Enc.book(bk), FM.Enc.mname(input), FM.Enc.mdef(FM.Input.run_def(bk)), FM.Enc.nat(c)]}]

# the entry, from the start
def Main.to_k1(+bk: List<&2, Source.Def>, +input: Maybe<&2, List<&2, Nat>>, +c: Nat) ->
  Fun.Reach1(Code.prog(), Main.X(bk, input, c), Main.k1(Main.so(bk, input, c), bk, input, c)):
  FP.Reach1.of(Code.prog(), Main.X(bk, input, c), Main.k1(Main.so(bk, input, c), bk, input, c),
    FP.Reach.trans(Code.prog(), Fun.F.iter(1n, Code.prog(), Main.X(bk, input, c)),
      Fun.Step.go{Fun.S.ret{FM.Enc.mstart(Main.so(bk, input, c)), Main.fr(bk, input, c)}},
      Main.k1(Main.so(bk, input, c), bk, input, c),
      L.Entry(input, bk, FM.Input.run_def(bk), c, FM.Input.arg_type(bk), Main.fr(bk, input, c)),
      FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.mstart(Main.so(bk, input, c)), Main.fr(bk, input, c)}})))

def Main.keeps.run(mr: Maybe<&2, Source.Obs>, +n: Nat, +s: Machine.St, +b: List<&2, Source.Def>, +w: Fun.V,
  +e: {Machine.Machine.run(n, s, b) == mr : Maybe<&2, Source.Obs>}, +h: {Spec.Res(mr) == Some{w} : Maybe<&2, Fun.V>}) ->
  Fun.Reach(Code.prog(), Run.X(s, b, []), Fun.Step.halt{w}):
  match mr:
    case None{}:
      Empty.absurd(Fun.Reach(Code.prog(), Run.X(s, b, []), Fun.Step.halt{w}), Shared.Maybe.no_none(Fun.V, w, h))
    case Some{+o}:
      %Equal.cong(Maybe<&2, Fun.V>, Fun.V, m => FP.Out.value(m, FM.Enc.name(Contract.Out.of(o))),
        Some{FM.Enc.name(Contract.Out.of(o))}, Some{w}, h) : Fun.Reach(Code.prog(), Run.X(s, b, []), Fun.Step.halt{_})
      FP.Reach.trans(Code.prog(), Run.X(s, b, []), Run.out(o, []), Fun.Step.halt{FM.Enc.name(Contract.Out.of(o))},
        Run.keeps(n, s, b, o, [], e), FP.Reach.steps(1n, Code.prog(), Run.out(o, [])))

def Main.keeps.k1(so: Maybe<&2, FM.Start>, +bk: List<&2, Source.Def>, +input: Maybe<&2, List<&2, Nat>>, +c: Nat,
  +n: Nat, +w: Fun.V, +h: {Spec.Res(Start.run(n, so)) == Some{w} : Maybe<&2, Fun.V>}) ->
  Fun.Reach(Code.prog(), Main.k1(so, bk, input, c), Fun.Step.halt{w}):
  match so:
    case None{}:
      Empty.absurd(Fun.Reach(Code.prog(), Main.k1(None{}, bk, input, c), Fun.Step.halt{w}), Shared.Maybe.no_none(Fun.V, w, h))
    case Some{+x}:
      match x:
        case FM.Start{+s, +b}:
          FP.Reach.trans(Code.prog(), Main.k1(Some{FM.Start{s, b}}, bk, input, c), Run.X(s, b, []), Fun.Step.halt{w},
            FP.Reach.steps(3n, Code.prog(), Main.k1(Some{FM.Start{s, b}}, bk, input, c)),
            Main.keeps.run(Machine.Machine.run(n, s, b), n, s, b, w, {==}, h))

# the program ends with the output of the machine's result
def Main.keeps(+input: Maybe<&2, List<&2, Nat>>, +bk: List<&2, Source.Def>, +c: Nat, +n: Nat, +w: Fun.V,
  +hb: {Spec.Input.ok(input, c) == True{} : Bool},
  +h: {Spec.Res(Spec.Run.at(n, Source.entry(input, bk))) == Some{w} : Maybe<&2, Fun.V>}) ->
  Fun.Reach(Code.prog(), Main.X(bk, input, c), Fun.Step.halt{w}):
  FP.Reach.trans(Code.prog(), Main.X(bk, input, c), Main.k1(Main.so(bk, input, c), bk, input, c), Fun.Step.halt{w},
    FP.Reach1.reach(Code.prog(), Main.X(bk, input, c), Main.k1(Main.so(bk, input, c), bk, input, c), Main.to_k1(bk, input, c)),
    Main.keeps.k1(Main.so(bk, input, c), bk, input, c, n, w,
      Equal.trans(Maybe<&2, Fun.V>, Spec.Res(Start.run(n, Main.so(bk, input, c))), Spec.Res(Spec.Run.at(n, Source.entry(input, bk))),
        Some{w},
        Equal.cong(Maybe<&2, Source.Obs>, Maybe<&2, Fun.V>, m => Spec.Res(m), Start.run(n, Main.so(bk, input, c)),
          Spec.Run.at(n, Source.entry(input, bk)),
          Equal.sym(Maybe<&2, Source.Obs>, Spec.Run.at(n, Source.entry(input, bk)), Start.run(n, Main.so(bk, input, c)),
            Entry.eq(n, input, bk, c, hb))), h)))

def Main.adds.after(+n: Nat, +s: Machine.St, +b: List<&2, Source.Def>, +w: Fun.V,
  a: FP.After(Code.prog(), n, Run.X(s, b, []), w)) -> {Spec.Res(Machine.Machine.run(n, s, b)) == Some{w} : Maybe<&2, Fun.V>}:
  (+M, +p) = a
  (+h3, +lt) = p
  Run.adds(n, M, s, b, w, h3, Shared.Nat.is_le_pred(M, n, lt))

def Main.adds.run(+n: Nat, +bk: List<&2, Source.Def>, +input: Maybe<&2, List<&2, Nat>>, +c: Nat, +s: Machine.St,
  +b: List<&2, Source.Def>, +w: Fun.V, +hh: {Fun.F.iter(n, Code.prog(), Main.X(bk, input, c)) == Fun.Step.halt{w} : Fun.Step},
  r: Fun.Reach1(Code.prog(), Main.X(bk, input, c), Run.X(s, b, []))) ->
  {Spec.Res(Machine.Machine.run(n, s, b)) == Some{w} : Maybe<&2, Fun.V>}:
  (+m, +e) = r
  Main.adds.after(n, s, b, w, FP.Iter.after(n, m, Code.prog(), Main.X(bk, input, c), Run.X(s, b, []), w, e, {==}, hh))

def Main.adds.k1(so: Maybe<&2, FM.Start>, +bk: List<&2, Source.Def>, +input: Maybe<&2, List<&2, Nat>>, +c: Nat,
  +n: Nat, +w: Fun.V, +hh: {Fun.F.iter(n, Code.prog(), Main.X(bk, input, c)) == Fun.Step.halt{w} : Fun.Step},
  r: Fun.Reach1(Code.prog(), Main.X(bk, input, c), Main.k1(so, bk, input, c))) ->
  {Spec.Res(Start.run(n, so)) == Some{w} : Maybe<&2, Fun.V>}:
  match so:
    case None{}:
      Empty.absurd({Spec.Res(Start.run(n, None{})) == Some{w} : Maybe<&2, Fun.V>},
        FP.Reach.stuck_end(Code.prog(), Main.X(bk, input, c), w,
          FP.Reach.trans(Code.prog(), Main.X(bk, input, c), Main.k1(None{}, bk, input, c), Fun.Step.stuck{},
            FP.Reach1.reach(Code.prog(), Main.X(bk, input, c), Main.k1(None{}, bk, input, c), r),
            FP.Reach.steps(2n, Code.prog(), Main.k1(None{}, bk, input, c))), n, hh))
    case Some{+x}:
      match x:
        case FM.Start{+s, +b}:
          Main.adds.run(n, bk, input, c, s, b, w, hh,
            FP.Reach1.then(Code.prog(), Main.X(bk, input, c), Main.k1(Some{FM.Start{s, b}}, bk, input, c), Run.X(s, b, []), r,
              FP.Reach.steps(3n, Code.prog(), Main.k1(Some{FM.Start{s, b}}, bk, input, c))))

# an end of the program is the output of the machine's result
def Main.adds(+input: Maybe<&2, List<&2, Nat>>, +bk: List<&2, Source.Def>, +c: Nat, +n: Nat, +w: Fun.V,
  +hb: {Spec.Input.ok(input, c) == True{} : Bool},
  +h: {Fun.F.run(n, Code.prog(), FM.start.of(bk, input, c)) == Some{w} : Maybe<&2, Fun.V>}) ->
  {Spec.Res(Spec.Run.at(n, Source.entry(input, bk))) == Some{w} : Maybe<&2, Fun.V>}:
  %Equal.cong(Maybe<&2, Source.Obs>, Maybe<&2, Fun.V>, m => Spec.Res(m), Start.run(n, Main.so(bk, input, c)),
    Spec.Run.at(n, Source.entry(input, bk)),
    Equal.sym(Maybe<&2, Source.Obs>, Spec.Run.at(n, Source.entry(input, bk)), Start.run(n, Main.so(bk, input, c)),
      Entry.eq(n, input, bk, c, hb))) : {_ == Some{w} : Maybe<&2, Fun.V>}
  Main.adds.k1(Main.so(bk, input, c), bk, input, c, n, w,
    FP.Out.halt(Fun.F.iter(n, Code.prog(), Main.X(bk, input, c)), w, h), Main.to_k1(bk, input, c))

# Laws
# ====

def Spec.keeps(bk, input, n, c, w, hb, h):
  Main.keeps(input, bk, c, n, w, hb, h)

def Spec.adds_none(bk, input, n, c, w, hb, h):
  Main.adds(input, bk, c, n, w, hb, h)
