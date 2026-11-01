import Base
import ./impl.bend as C
import ./proof_term.bend as T

def Regs(+xs: List<&2, U32>, oc: U32, ow: U32, ov: U32, oi: U32, t1: U32, t2: U32) -> List<&2, U32>:
  [T.tm.reg(xs, 0n), T.tm.reg(xs, 1n), T.tm.reg(xs, 2n), T.tm.reg(xs, 3n), T.tm.reg(xs, 4n), T.tm.reg(xs, 5n), T.tm.reg(xs, 6n), T.tm.reg(xs, 7n), T.tm.reg(xs, 8n), T.tm.reg(xs, 9n), T.tm.reg(xs, 10n), T.tm.reg(xs, 11n), T.tm.reg(xs, 12n), T.tm.reg(xs, 13n), T.tm.reg(xs, 14n), T.tm.reg(xs, 15n), T.tm.reg(xs, 16n), T.tm.reg(xs, 17n), T.tm.reg(xs, 18n), T.tm.reg(xs, 19n), T.tm.reg(xs, 20n), T.tm.reg(xs, 21n), T.tm.reg(xs, 22n), T.tm.reg(xs, 23n), T.tm.reg(xs, 24n), T.tm.reg(xs, 25n), T.tm.reg(xs, 26n), T.tm.reg(xs, 27n), T.tm.reg(xs, 28n), T.tm.reg(xs, 29n), T.tm.reg(xs, 30n), T.tm.reg(xs, 31n), T.tm.reg(xs, 32n), T.tm.reg(xs, 33n), T.tm.reg(xs, 34n), T.tm.reg(xs, 35n), T.tm.reg(xs, 36n), T.tm.reg(xs, 37n), T.tm.reg(xs, 38n), T.tm.reg(xs, 39n), T.tm.reg(xs, 40n), T.tm.reg(xs, 41n), T.tm.reg(xs, 42n), T.tm.reg(xs, 43n), T.tm.reg(xs, 44n), oc, ow, ov, oi, T.tm.reg(xs, 49n), T.tm.reg(xs, 50n), T.tm.reg(xs, 51n), T.tm.reg(xs, 52n), T.tm.reg(xs, 53n), T.tm.reg(xs, 54n), T.tm.reg(xs, 55n), T.tm.reg(xs, 56n), T.tm.reg(xs, 57n), T.tm.reg(xs, 58n), T.tm.reg(xs, 59n), T.tm.reg(xs, 60n), T.tm.reg(xs, 61n), t1, t2]

def St(rs: List<&2, U32>, m: C.Cir.Cells, nx: U32, fs: U32, im: U32, pg: U32, lim: U32, inp: List<&2, U32>, out: List<&2, U32>, outn: U32) -> C.Cir.State:
  C.Cir.State{rs, m, nx, fs, im, pg, lim, inp, out, outn}

def test1(+xs: List<&2, U32>, +oc: U32, +ow: U32, +ov: U32, +oi: U32, +t1: U32, +t2: U32, +m: C.Cir.Cells, +nx: U32, +fs: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +out: List<&2, U32>, +outn: U32, +n: Nat) ->
  {C.Cir.exec(1n+n, C.M.set(C.R.oc(), C.M.g(C.R.focus())), St(Regs(xs, oc, ow, ov, oi, t1, t2), m, nx, fs, im, pg, lim, inp, out, outn))
   == C.Cir.Out.next{St(Regs(xs, T.tm.reg(xs, 0n), ow, ov, oi, t1, t2), m, nx, fs, im, pg, lim, inp, out, outn)} : C.Cir.Out}:
  {==}
