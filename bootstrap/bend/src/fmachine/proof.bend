import Base
import ../source/impl.bend as Source
import ../machine/impl.bend as Machine
import ../shared/impl.bend as Shared
import ../fun/impl.bend as Fun
import ../fun/proof.bend as FP
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

def Elim.MObs(+x: Maybe<&2, Source.Obs>, -P: Maybe<&2, Source.Obs> -> Type, c0: P(None{}), c1: @o: Source.Obs -> P(Some{o})) -> P(x):
  match x:
    case None{}:
      c0
    case Some{o}:
      c1(o)

def Elim.Quan(+x: Source.Quan, -P: Source.Quan -> Type, c0: P(Source.Q0{}), c1: P(Source.Q1{}), c2: P(Source.Q2{})) -> P(x):
  match x:
    case Source.Q0{}:
      c0
    case Source.Q1{}:
      c1
    case Source.Q2{}:
      c2

# Lemmas
# ======

def L.Name.is_eq(+a_1: List<&2, Nat>, +b_2: List<&2, Nat>, +ks: List<&2, Fun.Fr>) ->
  FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Name.is_eq(), [FM.Enc.name(a_1), FM.Enc.name(b_2)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(a_1, b_2)), ks}}):
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
            Shared.Bool.elim(Nat.is_eq(x_5, y_7), bq => FP.Reach(Code.prog(), Bool.pick(Fun.Step, bq, Fun.Step.go{Fun.S.run{Code.F.Name.is_eq.k1(), [FM.Enc.name(ys_8), FM.Enc.nat(y_7), FM.Enc.name(xs_6), FM.Enc.nat(x_5), FM.Enc.name(Con{x_5, xs_6}), FM.Enc.name(Con{y_7, ys_8})], ks}}, Fun.Step.go{Fun.S.run{Code.F.Name.is_eq.k2(), [FM.Enc.name(ys_8), FM.Enc.nat(y_7), FM.Enc.name(xs_6), FM.Enc.nat(x_5), FM.Enc.name(Con{x_5, xs_6}), FM.Enc.name(Con{y_7, ys_8})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Bool.and(bq, Source.Name.is_eq(xs_6, ys_8))), ks}}),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Name.is_eq.k1(), [FM.Enc.name(ys_8), FM.Enc.nat(y_7), FM.Enc.name(xs_6), FM.Enc.nat(x_5), FM.Enc.name(Con{x_5, xs_6}), FM.Enc.name(Con{y_7, ys_8})], ks}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Name.is_eq.k1(), [FM.Enc.name(ys_8), FM.Enc.nat(y_7), FM.Enc.name(xs_6), FM.Enc.nat(x_5), FM.Enc.name(Con{x_5, xs_6}), FM.Enc.name(Con{y_7, ys_8})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Bool.and(True{}, Source.Name.is_eq(xs_6, ys_8))), ks}},
            FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Name.is_eq.k1(), [FM.Enc.name(ys_8), FM.Enc.nat(y_7), FM.Enc.name(xs_6), FM.Enc.nat(x_5), FM.Enc.name(Con{x_5, xs_6}), FM.Enc.name(Con{y_7, ys_8})], ks}}),
            L.Name.is_eq(xs_6, ys_8, ks)),
            (1n, {==})))

def L.Book.get(+bk_9: List<&2, Source.Def>, +k_10: List<&2, Nat>, +ks: List<&2, Fun.Fr>) ->
  FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Book.get(), [FM.Enc.book(bk_9), FM.Enc.name(k_10)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.mdef(Source.Book.get(bk_9, k_10)), ks}}):
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
            Elim.Bool(Source.Name.is_eq(n_13, k_10), m1 => FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Book.get.k1(), [FM.Enc.bool(m1), FM.Enc.term(v_15), FM.Enc.name(n_13), FM.Enc.book(rest_12), FM.Enc.def(Source.Def{n_13, t_14, v_15, o_16}), FM.Enc.book(Con{Source.Def{n_13, t_14, v_15, o_16}, rest_12}), FM.Enc.name(k_10)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.mdef(Source.Bool.lazy(Maybe<&2, Source.Def>, m1, u => Some{Source.Def{n_13, t_14, v_15, o_16}}, u => Source.Book.get(rest_12, k_10))), ks}}),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Book.get.k1(), [FM.Enc.bool(False{}), FM.Enc.term(v_15), FM.Enc.name(n_13), FM.Enc.book(rest_12), FM.Enc.def(Source.Def{n_13, t_14, v_15, o_16}), FM.Enc.book(Con{Source.Def{n_13, t_14, v_15, o_16}, rest_12}), FM.Enc.name(k_10)], ks}}, Fun.F.iter(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Book.get.k1(), [FM.Enc.bool(False{}), FM.Enc.term(v_15), FM.Enc.name(n_13), FM.Enc.book(rest_12), FM.Enc.def(Source.Def{n_13, t_14, v_15, o_16}), FM.Enc.book(Con{Source.Def{n_13, t_14, v_15, o_16}, rest_12}), FM.Enc.name(k_10)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.mdef(Source.Bool.lazy(Maybe<&2, Source.Def>, False{}, u => Some{Source.Def{n_13, t_14, v_15, o_16}}, u => Source.Book.get(rest_12, k_10))), ks}},
            FP.Reach.steps(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Book.get.k1(), [FM.Enc.bool(False{}), FM.Enc.term(v_15), FM.Enc.name(n_13), FM.Enc.book(rest_12), FM.Enc.def(Source.Def{n_13, t_14, v_15, o_16}), FM.Enc.book(Con{Source.Def{n_13, t_14, v_15, o_16}, rest_12}), FM.Enc.name(k_10)], ks}}),
            L.Book.get(rest_12, k_10, ks)),
            (3n, {==})))))

def L.Env.get(+e_18: Machine.Val, +i_19: Nat, +ks: List<&2, Fun.Fr>) ->
  FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.get(), [FM.Enc.val(e_18), FM.Enc.nat(i_19)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.val(Machine.Env.get(e_18, i_19)), ks}}):
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
  FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Env.find(), [FM.Enc.val(e_34), FM.Enc.nat(i_35)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.look(Machine.Env.find(e_34, i_35)), ks}}):
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
  FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.form.of(), [FM.Enc.look(l_124)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.form(Machine.Val.form.of(l_124)), ks}}):
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
  FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.form(), [FM.Enc.val(x_176)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.form(Machine.Val.form(x_176)), ks}}):
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
  FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go(), [FM.Enc.val(e_178), FM.Enc.term(t_179), FM.Enc.bool(c_180)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(e_178, t_179, c_180)), ks}}):
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
                    Elim.Bool(Machine.Val.data.go(Machine.Val.nil{}, a_239, True{}), m2 => FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go.k1(), [FM.Enc.bool(m2), FM.Enc.term(b_240), FM.Enc.term(a_239), FM.Enc.p(FM.Enc.term(a_239), FM.Enc.term(b_240)), FM.Enc.quan(Source.Q1{}), Fun.V.z{}, Fun.V.z{}, Fun.V.z{}, Fun.V.z{}, FM.Enc.val(Machine.Val.nil{}), FM.Enc.term(Source.Term.Tup{Source.Q1{}, a_239, b_240}), FM.Enc.bool(True{})], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(Bool.and(m2, Machine.Val.data.go(Machine.Val.nil{}, b_240, True{}))), ks}}),
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
                    Elim.Bool(Machine.Val.data.go(Machine.Val.nil{}, a_239, True{}), m3 => FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go.k1(), [FM.Enc.bool(m3), FM.Enc.term(b_240), FM.Enc.term(a_239), FM.Enc.p(FM.Enc.term(a_239), FM.Enc.term(b_240)), FM.Enc.quan(Source.Q2{}), Fun.V.z{}, Fun.V.z{}, Fun.V.z{}, Fun.V.z{}, FM.Enc.val(Machine.Val.nil{}), FM.Enc.term(Source.Term.Tup{Source.Q2{}, a_239, b_240}), FM.Enc.bool(True{})], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(Bool.and(m3, Machine.Val.data.go(Machine.Val.nil{}, b_240, True{}))), ks}}),
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
                    Elim.Bool(Machine.Val.data.go(Machine.Val.env{x_255, rest_256}, a_317, True{}), m4 => FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go.k2(), [FM.Enc.bool(m4), FM.Enc.term(b_318), FM.Enc.term(a_317), FM.Enc.p(FM.Enc.term(a_317), FM.Enc.term(b_318)), FM.Enc.quan(Source.Q1{}), Fun.V.z{}, Fun.V.z{}, FM.Enc.val(rest_256), FM.Enc.val(x_255), FM.Enc.val(Machine.Val.env{x_255, rest_256}), FM.Enc.term(Source.Term.Tup{Source.Q1{}, a_317, b_318}), FM.Enc.bool(True{})], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(Bool.and(m4, Machine.Val.data.go(Machine.Val.env{x_255, rest_256}, b_318, True{}))), ks}}),
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
                    Elim.Bool(Machine.Val.data.go(Machine.Val.env{x_255, rest_256}, a_317, True{}), m5 => FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go.k2(), [FM.Enc.bool(m5), FM.Enc.term(b_318), FM.Enc.term(a_317), FM.Enc.p(FM.Enc.term(a_317), FM.Enc.term(b_318)), FM.Enc.quan(Source.Q2{}), Fun.V.z{}, Fun.V.z{}, FM.Enc.val(rest_256), FM.Enc.val(x_255), FM.Enc.val(Machine.Val.env{x_255, rest_256}), FM.Enc.term(Source.Term.Tup{Source.Q2{}, a_317, b_318}), FM.Enc.bool(True{})], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(Bool.and(m5, Machine.Val.data.go(Machine.Val.env{x_255, rest_256}, b_318, True{}))), ks}}),
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
          Elim.Quan(q_339, m6 => FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go(), [FM.Enc.val(Machine.Val.tup{m6, a_340, b_341}), FM.Enc.term(t_179), FM.Enc.bool(False{})], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(Machine.Val.tup{m6, a_340, b_341}, t_179, False{})), ks}}),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go(), [FM.Enc.val(Machine.Val.tup{Source.Q0{}, a_340, b_341}), FM.Enc.term(t_179), FM.Enc.bool(False{})], ks}}, Fun.F.iter(8n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go(), [FM.Enc.val(Machine.Val.tup{Source.Q0{}, a_340, b_341}), FM.Enc.term(t_179), FM.Enc.bool(False{})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(Machine.Val.tup{Source.Q0{}, a_340, b_341}, t_179, False{})), ks}},
            FP.Reach.steps(8n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go(), [FM.Enc.val(Machine.Val.tup{Source.Q0{}, a_340, b_341}), FM.Enc.term(t_179), FM.Enc.bool(False{})], ks}}),
            L.Val.data.go(b_341, False{}, t_179, ks)),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go(), [FM.Enc.val(Machine.Val.tup{Source.Q1{}, a_340, b_341}), FM.Enc.term(t_179), FM.Enc.bool(False{})], ks}}, Fun.F.iter(8n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go(), [FM.Enc.val(Machine.Val.tup{Source.Q1{}, a_340, b_341}), FM.Enc.term(t_179), FM.Enc.bool(False{})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(Machine.Val.tup{Source.Q1{}, a_340, b_341}, t_179, False{})), ks}},
            FP.Reach.steps(8n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go(), [FM.Enc.val(Machine.Val.tup{Source.Q1{}, a_340, b_341}), FM.Enc.term(t_179), FM.Enc.bool(False{})], ks}}),
            FP.Reach.trans(Code.prog(), Fun.F.iter(8n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go(), [FM.Enc.val(Machine.Val.tup{Source.Q1{}, a_340, b_341}), FM.Enc.term(t_179), FM.Enc.bool(False{})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(a_340, t_179, False{})), Con{Fun.Fr{Code.F.Val.data.go.k3(), [Fun.V.z{}, Fun.V.z{}, FM.Enc.val(b_341), FM.Enc.val(a_340), FM.Enc.p(FM.Enc.val(a_340), FM.Enc.val(b_341)), FM.Enc.quan(Source.Q1{}), FM.Enc.val(Machine.Val.tup{Source.Q1{}, a_340, b_341}), FM.Enc.term(t_179), FM.Enc.bool(False{})]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(Machine.Val.tup{Source.Q1{}, a_340, b_341}, t_179, False{})), ks}},
            L.Val.data.go(a_340, False{}, t_179, Con{Fun.Fr{Code.F.Val.data.go.k3(), [Fun.V.z{}, Fun.V.z{}, FM.Enc.val(b_341), FM.Enc.val(a_340), FM.Enc.p(FM.Enc.val(a_340), FM.Enc.val(b_341)), FM.Enc.quan(Source.Q1{}), FM.Enc.val(Machine.Val.tup{Source.Q1{}, a_340, b_341}), FM.Enc.term(t_179), FM.Enc.bool(False{})]}, ks}),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(a_340, t_179, False{})), Con{Fun.Fr{Code.F.Val.data.go.k3(), [Fun.V.z{}, Fun.V.z{}, FM.Enc.val(b_341), FM.Enc.val(a_340), FM.Enc.p(FM.Enc.val(a_340), FM.Enc.val(b_341)), FM.Enc.quan(Source.Q1{}), FM.Enc.val(Machine.Val.tup{Source.Q1{}, a_340, b_341}), FM.Enc.term(t_179), FM.Enc.bool(False{})]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(a_340, t_179, False{})), Con{Fun.Fr{Code.F.Val.data.go.k3(), [Fun.V.z{}, Fun.V.z{}, FM.Enc.val(b_341), FM.Enc.val(a_340), FM.Enc.p(FM.Enc.val(a_340), FM.Enc.val(b_341)), FM.Enc.quan(Source.Q1{}), FM.Enc.val(Machine.Val.tup{Source.Q1{}, a_340, b_341}), FM.Enc.term(t_179), FM.Enc.bool(False{})]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(Machine.Val.tup{Source.Q1{}, a_340, b_341}, t_179, False{})), ks}},
            FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.data.go(a_340, t_179, False{})), Con{Fun.Fr{Code.F.Val.data.go.k3(), [Fun.V.z{}, Fun.V.z{}, FM.Enc.val(b_341), FM.Enc.val(a_340), FM.Enc.p(FM.Enc.val(a_340), FM.Enc.val(b_341)), FM.Enc.quan(Source.Q1{}), FM.Enc.val(Machine.Val.tup{Source.Q1{}, a_340, b_341}), FM.Enc.term(t_179), FM.Enc.bool(False{})]}, ks}}}),
            Elim.Bool(Machine.Val.data.go(a_340, t_179, False{}), m7 => FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go.k3(), [FM.Enc.bool(m7), Fun.V.z{}, Fun.V.z{}, FM.Enc.val(b_341), FM.Enc.val(a_340), FM.Enc.p(FM.Enc.val(a_340), FM.Enc.val(b_341)), FM.Enc.quan(Source.Q1{}), FM.Enc.val(Machine.Val.tup{Source.Q1{}, a_340, b_341}), FM.Enc.term(t_179), FM.Enc.bool(False{})], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(Bool.and(m7, Machine.Val.data.go(b_341, t_179, False{}))), ks}}),
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
            Elim.Bool(Machine.Val.data.go(a_340, t_179, False{}), m8 => FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go.k3(), [FM.Enc.bool(m8), Fun.V.z{}, Fun.V.z{}, FM.Enc.val(b_341), FM.Enc.val(a_340), FM.Enc.p(FM.Enc.val(a_340), FM.Enc.val(b_341)), FM.Enc.quan(Source.Q2{}), FM.Enc.val(Machine.Val.tup{Source.Q2{}, a_340, b_341}), FM.Enc.term(t_179), FM.Enc.bool(False{})], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(Bool.and(m8, Machine.Val.data.go(b_341, t_179, False{}))), ks}}),
            (2n, {==}),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go.k3(), [FM.Enc.bool(True{}), Fun.V.z{}, Fun.V.z{}, FM.Enc.val(b_341), FM.Enc.val(a_340), FM.Enc.p(FM.Enc.val(a_340), FM.Enc.val(b_341)), FM.Enc.quan(Source.Q2{}), FM.Enc.val(Machine.Val.tup{Source.Q2{}, a_340, b_341}), FM.Enc.term(t_179), FM.Enc.bool(False{})], ks}}, Fun.F.iter(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go.k3(), [FM.Enc.bool(True{}), Fun.V.z{}, Fun.V.z{}, FM.Enc.val(b_341), FM.Enc.val(a_340), FM.Enc.p(FM.Enc.val(a_340), FM.Enc.val(b_341)), FM.Enc.quan(Source.Q2{}), FM.Enc.val(Machine.Val.tup{Source.Q2{}, a_340, b_341}), FM.Enc.term(t_179), FM.Enc.bool(False{})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Bool.and(True{}, Machine.Val.data.go(b_341, t_179, False{}))), ks}},
            FP.Reach.steps(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.data.go.k3(), [FM.Enc.bool(True{}), Fun.V.z{}, Fun.V.z{}, FM.Enc.val(b_341), FM.Enc.val(a_340), FM.Enc.p(FM.Enc.val(a_340), FM.Enc.val(b_341)), FM.Enc.quan(Source.Q2{}), FM.Enc.val(Machine.Val.tup{Source.Q2{}, a_340, b_341}), FM.Enc.term(t_179), FM.Enc.bool(False{})], ks}}),
            L.Val.data.go(b_341, False{}, t_179, ks)))))))
        case True{}:
          (7n, {==})
    case Machine.Val.call{+_k_344, +_xs_345}:
      (7n, {==})

def L.Val.is_data(+x_346: Machine.Val, +ks: List<&2, Fun.Fr>) ->
  FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.is_data(), [FM.Enc.val(x_346)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.is_data(x_346)), ks}}):
  FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.is_data(), [FM.Enc.val(x_346)], ks}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.is_data(), [FM.Enc.val(x_346)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Val.is_data(x_346)), ks}},
    FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.is_data(), [FM.Enc.val(x_346)], ks}}),
    L.Val.data.go(x_346, False{}, Source.Term.Efq{}, ks))

def L.Val.observe(+v_347: Machine.Val, +ks: List<&2, Fun.Fr>) ->
  FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.observe(), [FM.Enc.val(v_347)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.mobs(Machine.Val.observe(v_347)), ks}}):
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
        Elim.MObs(Machine.Val.observe(b_358), m9 => FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.observe.k1(), [FM.Enc.mobs(m9), FM.Enc.val(b_358), FM.Enc.val(a_357), FM.Enc.p(FM.Enc.val(a_357), FM.Enc.val(b_358)), FM.Enc.quan(q_356), FM.Enc.val(Machine.Val.tup{q_356, a_357, b_358})], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.mobs(Source.Obs.tup.of(m9, Source.Quan.live(q_356), Machine.Val.observe(a_357))), ks}}),
        (2n, {==}),
        +y_360 => Elim.Quan(q_356, m10 => FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.observe.k1(), [FM.Enc.mobs(Some{y_360}), FM.Enc.val(b_358), FM.Enc.val(a_357), FM.Enc.p(FM.Enc.val(a_357), FM.Enc.val(b_358)), FM.Enc.quan(m10), FM.Enc.val(Machine.Val.tup{m10, a_357, b_358})], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.mobs(Source.Obs.tup.of(Some{y_360}, Source.Quan.live(m10), Machine.Val.observe(a_357))), ks}}),
        (5n, {==}),
        FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.observe.k1(), [FM.Enc.mobs(Some{y_360}), FM.Enc.val(b_358), FM.Enc.val(a_357), FM.Enc.p(FM.Enc.val(a_357), FM.Enc.val(b_358)), FM.Enc.quan(Source.Q1{}), FM.Enc.val(Machine.Val.tup{Source.Q1{}, a_357, b_358})], ks}}, Fun.F.iter(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.observe.k1(), [FM.Enc.mobs(Some{y_360}), FM.Enc.val(b_358), FM.Enc.val(a_357), FM.Enc.p(FM.Enc.val(a_357), FM.Enc.val(b_358)), FM.Enc.quan(Source.Q1{}), FM.Enc.val(Machine.Val.tup{Source.Q1{}, a_357, b_358})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.mobs(Source.Obs.tup.of(Some{y_360}, Source.Quan.live(Source.Q1{}), Machine.Val.observe(a_357))), ks}},
        FP.Reach.steps(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.observe.k1(), [FM.Enc.mobs(Some{y_360}), FM.Enc.val(b_358), FM.Enc.val(a_357), FM.Enc.p(FM.Enc.val(a_357), FM.Enc.val(b_358)), FM.Enc.quan(Source.Q1{}), FM.Enc.val(Machine.Val.tup{Source.Q1{}, a_357, b_358})], ks}}),
        FP.Reach.trans(Code.prog(), Fun.F.iter(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.observe.k1(), [FM.Enc.mobs(Some{y_360}), FM.Enc.val(b_358), FM.Enc.val(a_357), FM.Enc.p(FM.Enc.val(a_357), FM.Enc.val(b_358)), FM.Enc.quan(Source.Q1{}), FM.Enc.val(Machine.Val.tup{Source.Q1{}, a_357, b_358})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.mobs(Machine.Val.observe(a_357)), Con{Fun.Fr{Code.F.Val.observe.k2(), [Fun.V.z{}, FM.Enc.obs(y_360), FM.Enc.mobs(Some{y_360}), FM.Enc.val(b_358), FM.Enc.val(a_357), FM.Enc.p(FM.Enc.val(a_357), FM.Enc.val(b_358)), FM.Enc.quan(Source.Q1{}), FM.Enc.val(Machine.Val.tup{Source.Q1{}, a_357, b_358})]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.mobs(Source.Obs.tup.of(Some{y_360}, Source.Quan.live(Source.Q1{}), Machine.Val.observe(a_357))), ks}},
        L.Val.observe(a_357, Con{Fun.Fr{Code.F.Val.observe.k2(), [Fun.V.z{}, FM.Enc.obs(y_360), FM.Enc.mobs(Some{y_360}), FM.Enc.val(b_358), FM.Enc.val(a_357), FM.Enc.p(FM.Enc.val(a_357), FM.Enc.val(b_358)), FM.Enc.quan(Source.Q1{}), FM.Enc.val(Machine.Val.tup{Source.Q1{}, a_357, b_358})]}, ks}),
        FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.mobs(Machine.Val.observe(a_357)), Con{Fun.Fr{Code.F.Val.observe.k2(), [Fun.V.z{}, FM.Enc.obs(y_360), FM.Enc.mobs(Some{y_360}), FM.Enc.val(b_358), FM.Enc.val(a_357), FM.Enc.p(FM.Enc.val(a_357), FM.Enc.val(b_358)), FM.Enc.quan(Source.Q1{}), FM.Enc.val(Machine.Val.tup{Source.Q1{}, a_357, b_358})]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.mobs(Machine.Val.observe(a_357)), Con{Fun.Fr{Code.F.Val.observe.k2(), [Fun.V.z{}, FM.Enc.obs(y_360), FM.Enc.mobs(Some{y_360}), FM.Enc.val(b_358), FM.Enc.val(a_357), FM.Enc.p(FM.Enc.val(a_357), FM.Enc.val(b_358)), FM.Enc.quan(Source.Q1{}), FM.Enc.val(Machine.Val.tup{Source.Q1{}, a_357, b_358})]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.mobs(Source.Obs.tup.of(Some{y_360}, Source.Quan.live(Source.Q1{}), Machine.Val.observe(a_357))), ks}},
        FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.mobs(Machine.Val.observe(a_357)), Con{Fun.Fr{Code.F.Val.observe.k2(), [Fun.V.z{}, FM.Enc.obs(y_360), FM.Enc.mobs(Some{y_360}), FM.Enc.val(b_358), FM.Enc.val(a_357), FM.Enc.p(FM.Enc.val(a_357), FM.Enc.val(b_358)), FM.Enc.quan(Source.Q1{}), FM.Enc.val(Machine.Val.tup{Source.Q1{}, a_357, b_358})]}, ks}}}),
        Elim.MObs(Machine.Val.observe(a_357), m11 => FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.observe.k2(), [FM.Enc.mobs(m11), Fun.V.z{}, FM.Enc.obs(y_360), FM.Enc.mobs(Some{y_360}), FM.Enc.val(b_358), FM.Enc.val(a_357), FM.Enc.p(FM.Enc.val(a_357), FM.Enc.val(b_358)), FM.Enc.quan(Source.Q1{}), FM.Enc.val(Machine.Val.tup{Source.Q1{}, a_357, b_358})], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.mobs(Source.Obs.tup.of(Some{y_360}, Source.Quan.live(Source.Q1{}), m11)), ks}}),
        (2n, {==}),
        +x_362 => (4n, {==}))))),
        FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.observe.k1(), [FM.Enc.mobs(Some{y_360}), FM.Enc.val(b_358), FM.Enc.val(a_357), FM.Enc.p(FM.Enc.val(a_357), FM.Enc.val(b_358)), FM.Enc.quan(Source.Q2{}), FM.Enc.val(Machine.Val.tup{Source.Q2{}, a_357, b_358})], ks}}, Fun.F.iter(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.observe.k1(), [FM.Enc.mobs(Some{y_360}), FM.Enc.val(b_358), FM.Enc.val(a_357), FM.Enc.p(FM.Enc.val(a_357), FM.Enc.val(b_358)), FM.Enc.quan(Source.Q2{}), FM.Enc.val(Machine.Val.tup{Source.Q2{}, a_357, b_358})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.mobs(Source.Obs.tup.of(Some{y_360}, Source.Quan.live(Source.Q2{}), Machine.Val.observe(a_357))), ks}},
        FP.Reach.steps(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.observe.k1(), [FM.Enc.mobs(Some{y_360}), FM.Enc.val(b_358), FM.Enc.val(a_357), FM.Enc.p(FM.Enc.val(a_357), FM.Enc.val(b_358)), FM.Enc.quan(Source.Q2{}), FM.Enc.val(Machine.Val.tup{Source.Q2{}, a_357, b_358})], ks}}),
        FP.Reach.trans(Code.prog(), Fun.F.iter(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.observe.k1(), [FM.Enc.mobs(Some{y_360}), FM.Enc.val(b_358), FM.Enc.val(a_357), FM.Enc.p(FM.Enc.val(a_357), FM.Enc.val(b_358)), FM.Enc.quan(Source.Q2{}), FM.Enc.val(Machine.Val.tup{Source.Q2{}, a_357, b_358})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.mobs(Machine.Val.observe(a_357)), Con{Fun.Fr{Code.F.Val.observe.k2(), [Fun.V.z{}, FM.Enc.obs(y_360), FM.Enc.mobs(Some{y_360}), FM.Enc.val(b_358), FM.Enc.val(a_357), FM.Enc.p(FM.Enc.val(a_357), FM.Enc.val(b_358)), FM.Enc.quan(Source.Q2{}), FM.Enc.val(Machine.Val.tup{Source.Q2{}, a_357, b_358})]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.mobs(Source.Obs.tup.of(Some{y_360}, Source.Quan.live(Source.Q2{}), Machine.Val.observe(a_357))), ks}},
        L.Val.observe(a_357, Con{Fun.Fr{Code.F.Val.observe.k2(), [Fun.V.z{}, FM.Enc.obs(y_360), FM.Enc.mobs(Some{y_360}), FM.Enc.val(b_358), FM.Enc.val(a_357), FM.Enc.p(FM.Enc.val(a_357), FM.Enc.val(b_358)), FM.Enc.quan(Source.Q2{}), FM.Enc.val(Machine.Val.tup{Source.Q2{}, a_357, b_358})]}, ks}),
        FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.mobs(Machine.Val.observe(a_357)), Con{Fun.Fr{Code.F.Val.observe.k2(), [Fun.V.z{}, FM.Enc.obs(y_360), FM.Enc.mobs(Some{y_360}), FM.Enc.val(b_358), FM.Enc.val(a_357), FM.Enc.p(FM.Enc.val(a_357), FM.Enc.val(b_358)), FM.Enc.quan(Source.Q2{}), FM.Enc.val(Machine.Val.tup{Source.Q2{}, a_357, b_358})]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.mobs(Machine.Val.observe(a_357)), Con{Fun.Fr{Code.F.Val.observe.k2(), [Fun.V.z{}, FM.Enc.obs(y_360), FM.Enc.mobs(Some{y_360}), FM.Enc.val(b_358), FM.Enc.val(a_357), FM.Enc.p(FM.Enc.val(a_357), FM.Enc.val(b_358)), FM.Enc.quan(Source.Q2{}), FM.Enc.val(Machine.Val.tup{Source.Q2{}, a_357, b_358})]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.mobs(Source.Obs.tup.of(Some{y_360}, Source.Quan.live(Source.Q2{}), Machine.Val.observe(a_357))), ks}},
        FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.mobs(Machine.Val.observe(a_357)), Con{Fun.Fr{Code.F.Val.observe.k2(), [Fun.V.z{}, FM.Enc.obs(y_360), FM.Enc.mobs(Some{y_360}), FM.Enc.val(b_358), FM.Enc.val(a_357), FM.Enc.p(FM.Enc.val(a_357), FM.Enc.val(b_358)), FM.Enc.quan(Source.Q2{}), FM.Enc.val(Machine.Val.tup{Source.Q2{}, a_357, b_358})]}, ks}}}),
        Elim.MObs(Machine.Val.observe(a_357), m12 => FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.observe.k2(), [FM.Enc.mobs(m12), Fun.V.z{}, FM.Enc.obs(y_360), FM.Enc.mobs(Some{y_360}), FM.Enc.val(b_358), FM.Enc.val(a_357), FM.Enc.p(FM.Enc.val(a_357), FM.Enc.val(b_358)), FM.Enc.quan(Source.Q2{}), FM.Enc.val(Machine.Val.tup{Source.Q2{}, a_357, b_358})], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.mobs(Source.Obs.tup.of(Some{y_360}, Source.Quan.live(Source.Q2{}), m12)), ks}}),
        (2n, {==}),
        +x_364 => (4n, {==}))))))))))
    case Machine.Val.call{+_k_365, +_xs_366}:
      (4n, {==})

def L.Lam.takes(+p_367: Source.Quan, +q_368: Source.Quan, +x_369: Machine.Val, +ks: List<&2, Fun.Fr>) ->
  FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Lam.takes(), [FM.Enc.quan(p_367), FM.Enc.quan(q_368), FM.Enc.val(x_369)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(Machine.Lam.takes(p_367, q_368, x_369)), ks}}):
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
  FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Head.takes(), [FM.Enc.term(f_370)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Spine.head.takes(Source.Term.unspine(f_370, xs_371))), ks}}):
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
  FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go(), [FM.Enc.term(t_408), FM.Enc.val(e_409), FM.Enc.val(xs_410)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Machine.Walk.go(t_408, e_409, xs_410)), ks}}):
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
            Elim.Bool(Machine.Lam.takes(p_424, q_428, x_429), m13 => FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k1(), [FM.Enc.bool(m13), FM.Enc.val(rest_430), FM.Enc.val(x_429), FM.Enc.p(FM.Enc.val(x_429), FM.Enc.val(rest_430)), FM.Enc.quan(q_428), FM.Enc.term(f_425), FM.Enc.quan(p_424), FM.Enc.term(Source.Term.Lam{p_424, f_425}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{q_428, x_429, rest_430})], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Source.Bool.lazy(Machine.Leaf, m13, u => Machine.Walk.go(f_425, Machine.Val.env{x_429, e_409}, rest_430), u => Machine.Leaf.fail{})), ks}}),
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
            Elim.Bool(Source.Spine.head.takes(Source.Term.unspine(f_441, Nil{})), m14 => FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k2(), [FM.Enc.bool(m14), Fun.V.z{}, FM.Enc.nat(v_443), FM.Enc.term(Source.Term.Var{v_443}), FM.Enc.term(f_441), FM.Enc.p(FM.Enc.term(f_441), FM.Enc.term(Source.Term.Var{v_443})), FM.Enc.quan(q_440), FM.Enc.term(Source.Term.App{q_440, f_441, Source.Term.Var{v_443}}), FM.Enc.val(e_409), FM.Enc.val(xs_410)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Source.Bool.lazy(Machine.Leaf, m14, u => Machine.Walk.go(f_441, e_409, Machine.Val.arg{q_440, Machine.Env.get(e_409, v_443), xs_410}), u => Machine.Leaf.at{Source.Term.App{q_440, f_441, Source.Term.Var{v_443}}, e_409, xs_410})), ks}}),
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
            Elim.Form(Machine.Val.form(x_491), m15 => FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k4(), [FM.Enc.form(m15), FM.Enc.val(rest_492), FM.Enc.val(x_491), FM.Enc.p(FM.Enc.val(x_491), FM.Enc.val(rest_492)), FM.Enc.quan(q_490), Fun.V.z{}, FM.Enc.term(h_487), FM.Enc.term(Source.Term.Prj{h_487}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{q_490, x_491, rest_492})], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Machine.Walk.prj.of(m15, q_490, rest_492, ys => Machine.Walk.go(h_487, e_409, ys))), ks}}),
            +r_494 => +a_495 => +b_496 => Elim.Quan(q_490, m16 => FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k4(), [FM.Enc.form(Machine.Form.tup{r_494, a_495, b_496}), FM.Enc.val(rest_492), FM.Enc.val(x_491), FM.Enc.p(FM.Enc.val(x_491), FM.Enc.val(rest_492)), FM.Enc.quan(m16), Fun.V.z{}, FM.Enc.term(h_487), FM.Enc.term(Source.Term.Prj{h_487}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{m16, x_491, rest_492})], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Machine.Walk.prj.of(Machine.Form.tup{r_494, a_495, b_496}, m16, rest_492, ys => Machine.Walk.go(h_487, e_409, ys))), ks}}),
            (4n, {==}),
            Elim.Quan(r_494, m17 => FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k4(), [FM.Enc.form(Machine.Form.tup{m17, a_495, b_496}), FM.Enc.val(rest_492), FM.Enc.val(x_491), FM.Enc.p(FM.Enc.val(x_491), FM.Enc.val(rest_492)), FM.Enc.quan(Source.Q1{}), Fun.V.z{}, FM.Enc.term(h_487), FM.Enc.term(Source.Term.Prj{h_487}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q1{}, x_491, rest_492})], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Machine.Walk.prj.of(Machine.Form.tup{m17, a_495, b_496}, Source.Q1{}, rest_492, ys => Machine.Walk.go(h_487, e_409, ys))), ks}}),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k4(), [FM.Enc.form(Machine.Form.tup{Source.Q0{}, a_495, b_496}), FM.Enc.val(rest_492), FM.Enc.val(x_491), FM.Enc.p(FM.Enc.val(x_491), FM.Enc.val(rest_492)), FM.Enc.quan(Source.Q1{}), Fun.V.z{}, FM.Enc.term(h_487), FM.Enc.term(Source.Term.Prj{h_487}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q1{}, x_491, rest_492})], ks}}, Fun.F.iter(9n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k4(), [FM.Enc.form(Machine.Form.tup{Source.Q0{}, a_495, b_496}), FM.Enc.val(rest_492), FM.Enc.val(x_491), FM.Enc.p(FM.Enc.val(x_491), FM.Enc.val(rest_492)), FM.Enc.quan(Source.Q1{}), Fun.V.z{}, FM.Enc.term(h_487), FM.Enc.term(Source.Term.Prj{h_487}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q1{}, x_491, rest_492})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Machine.Walk.prj.of(Machine.Form.tup{Source.Q0{}, a_495, b_496}, Source.Q1{}, rest_492, ys => Machine.Walk.go(h_487, e_409, ys))), ks}},
            FP.Reach.steps(9n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k4(), [FM.Enc.form(Machine.Form.tup{Source.Q0{}, a_495, b_496}), FM.Enc.val(rest_492), FM.Enc.val(x_491), FM.Enc.p(FM.Enc.val(x_491), FM.Enc.val(rest_492)), FM.Enc.quan(Source.Q1{}), Fun.V.z{}, FM.Enc.term(h_487), FM.Enc.term(Source.Term.Prj{h_487}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q1{}, x_491, rest_492})], ks}}),
            L.Walk.go(h_487, e_409, Machine.Val.arg{Source.Q0{}, a_495, Machine.Val.arg{Source.Q1{}, b_496, rest_492}}, ks)),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k4(), [FM.Enc.form(Machine.Form.tup{Source.Q1{}, a_495, b_496}), FM.Enc.val(rest_492), FM.Enc.val(x_491), FM.Enc.p(FM.Enc.val(x_491), FM.Enc.val(rest_492)), FM.Enc.quan(Source.Q1{}), Fun.V.z{}, FM.Enc.term(h_487), FM.Enc.term(Source.Term.Prj{h_487}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q1{}, x_491, rest_492})], ks}}, Fun.F.iter(9n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k4(), [FM.Enc.form(Machine.Form.tup{Source.Q1{}, a_495, b_496}), FM.Enc.val(rest_492), FM.Enc.val(x_491), FM.Enc.p(FM.Enc.val(x_491), FM.Enc.val(rest_492)), FM.Enc.quan(Source.Q1{}), Fun.V.z{}, FM.Enc.term(h_487), FM.Enc.term(Source.Term.Prj{h_487}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q1{}, x_491, rest_492})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Machine.Walk.prj.of(Machine.Form.tup{Source.Q1{}, a_495, b_496}, Source.Q1{}, rest_492, ys => Machine.Walk.go(h_487, e_409, ys))), ks}},
            FP.Reach.steps(9n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k4(), [FM.Enc.form(Machine.Form.tup{Source.Q1{}, a_495, b_496}), FM.Enc.val(rest_492), FM.Enc.val(x_491), FM.Enc.p(FM.Enc.val(x_491), FM.Enc.val(rest_492)), FM.Enc.quan(Source.Q1{}), Fun.V.z{}, FM.Enc.term(h_487), FM.Enc.term(Source.Term.Prj{h_487}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q1{}, x_491, rest_492})], ks}}),
            L.Walk.go(h_487, e_409, Machine.Val.arg{Source.Q1{}, a_495, Machine.Val.arg{Source.Q1{}, b_496, rest_492}}, ks)),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k4(), [FM.Enc.form(Machine.Form.tup{Source.Q2{}, a_495, b_496}), FM.Enc.val(rest_492), FM.Enc.val(x_491), FM.Enc.p(FM.Enc.val(x_491), FM.Enc.val(rest_492)), FM.Enc.quan(Source.Q1{}), Fun.V.z{}, FM.Enc.term(h_487), FM.Enc.term(Source.Term.Prj{h_487}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q1{}, x_491, rest_492})], ks}}, Fun.F.iter(9n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k4(), [FM.Enc.form(Machine.Form.tup{Source.Q2{}, a_495, b_496}), FM.Enc.val(rest_492), FM.Enc.val(x_491), FM.Enc.p(FM.Enc.val(x_491), FM.Enc.val(rest_492)), FM.Enc.quan(Source.Q1{}), Fun.V.z{}, FM.Enc.term(h_487), FM.Enc.term(Source.Term.Prj{h_487}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q1{}, x_491, rest_492})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Machine.Walk.prj.of(Machine.Form.tup{Source.Q2{}, a_495, b_496}, Source.Q1{}, rest_492, ys => Machine.Walk.go(h_487, e_409, ys))), ks}},
            FP.Reach.steps(9n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k4(), [FM.Enc.form(Machine.Form.tup{Source.Q2{}, a_495, b_496}), FM.Enc.val(rest_492), FM.Enc.val(x_491), FM.Enc.p(FM.Enc.val(x_491), FM.Enc.val(rest_492)), FM.Enc.quan(Source.Q1{}), Fun.V.z{}, FM.Enc.term(h_487), FM.Enc.term(Source.Term.Prj{h_487}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q1{}, x_491, rest_492})], ks}}),
            L.Walk.go(h_487, e_409, Machine.Val.arg{Source.Q2{}, a_495, Machine.Val.arg{Source.Q1{}, b_496, rest_492}}, ks))),
            Elim.Quan(r_494, m18 => FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k4(), [FM.Enc.form(Machine.Form.tup{m18, a_495, b_496}), FM.Enc.val(rest_492), FM.Enc.val(x_491), FM.Enc.p(FM.Enc.val(x_491), FM.Enc.val(rest_492)), FM.Enc.quan(Source.Q2{}), Fun.V.z{}, FM.Enc.term(h_487), FM.Enc.term(Source.Term.Prj{h_487}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q2{}, x_491, rest_492})], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Machine.Walk.prj.of(Machine.Form.tup{m18, a_495, b_496}, Source.Q2{}, rest_492, ys => Machine.Walk.go(h_487, e_409, ys))), ks}}),
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
            Elim.Form(Machine.Val.form(x_514), m19 => FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k5(), [FM.Enc.form(m19), FM.Enc.val(rest_515), FM.Enc.val(x_514), FM.Enc.p(FM.Enc.val(x_514), FM.Enc.val(rest_515)), FM.Enc.quan(q_513), FM.Enc.term(m_510), FM.Enc.term(h_509), FM.Enc.p(FM.Enc.term(h_509), FM.Enc.term(m_510)), FM.Enc.name(k_508), FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{q_513, x_514, rest_515})], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Machine.Walk.mat.of(m19, q_513, k_508, rest_515, ys => Machine.Walk.go(h_509, e_409, ys), ys => Machine.Walk.go(m_510, e_409, ys))), ks}}),
            +_r_517 => +_a_518 => +_b_519 => (2n, {==}),
            +j_520 => Elim.Quan(q_513, m20 => FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k5(), [FM.Enc.form(Machine.Form.lab{j_520}), FM.Enc.val(rest_515), FM.Enc.val(x_514), FM.Enc.p(FM.Enc.val(x_514), FM.Enc.val(rest_515)), FM.Enc.quan(m20), FM.Enc.term(m_510), FM.Enc.term(h_509), FM.Enc.p(FM.Enc.term(h_509), FM.Enc.term(m_510)), FM.Enc.name(k_508), FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{m20, x_514, rest_515})], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Machine.Walk.mat.of(Machine.Form.lab{j_520}, m20, k_508, rest_515, ys => Machine.Walk.go(h_509, e_409, ys), ys => Machine.Walk.go(m_510, e_409, ys))), ks}}),
            (3n, {==}),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k5(), [FM.Enc.form(Machine.Form.lab{j_520}), FM.Enc.val(rest_515), FM.Enc.val(x_514), FM.Enc.p(FM.Enc.val(x_514), FM.Enc.val(rest_515)), FM.Enc.quan(Source.Q1{}), FM.Enc.term(m_510), FM.Enc.term(h_509), FM.Enc.p(FM.Enc.term(h_509), FM.Enc.term(m_510)), FM.Enc.name(k_508), FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q1{}, x_514, rest_515})], ks}}, Fun.F.iter(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k5(), [FM.Enc.form(Machine.Form.lab{j_520}), FM.Enc.val(rest_515), FM.Enc.val(x_514), FM.Enc.p(FM.Enc.val(x_514), FM.Enc.val(rest_515)), FM.Enc.quan(Source.Q1{}), FM.Enc.term(m_510), FM.Enc.term(h_509), FM.Enc.p(FM.Enc.term(h_509), FM.Enc.term(m_510)), FM.Enc.name(k_508), FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q1{}, x_514, rest_515})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Machine.Walk.mat.of(Machine.Form.lab{j_520}, Source.Q1{}, k_508, rest_515, ys => Machine.Walk.go(h_509, e_409, ys), ys => Machine.Walk.go(m_510, e_409, ys))), ks}},
            FP.Reach.steps(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k5(), [FM.Enc.form(Machine.Form.lab{j_520}), FM.Enc.val(rest_515), FM.Enc.val(x_514), FM.Enc.p(FM.Enc.val(x_514), FM.Enc.val(rest_515)), FM.Enc.quan(Source.Q1{}), FM.Enc.term(m_510), FM.Enc.term(h_509), FM.Enc.p(FM.Enc.term(h_509), FM.Enc.term(m_510)), FM.Enc.name(k_508), FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q1{}, x_514, rest_515})], ks}}),
            FP.Reach.trans(Code.prog(), Fun.F.iter(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k5(), [FM.Enc.form(Machine.Form.lab{j_520}), FM.Enc.val(rest_515), FM.Enc.val(x_514), FM.Enc.p(FM.Enc.val(x_514), FM.Enc.val(rest_515)), FM.Enc.quan(Source.Q1{}), FM.Enc.term(m_510), FM.Enc.term(h_509), FM.Enc.p(FM.Enc.term(h_509), FM.Enc.term(m_510)), FM.Enc.name(k_508), FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q1{}, x_514, rest_515})], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(j_520, k_508)), Con{Fun.Fr{Code.F.Walk.go.k6(), [Fun.V.z{}, FM.Enc.name(j_520), FM.Enc.form(Machine.Form.lab{j_520}), FM.Enc.val(rest_515), FM.Enc.val(x_514), FM.Enc.p(FM.Enc.val(x_514), FM.Enc.val(rest_515)), FM.Enc.quan(Source.Q1{}), FM.Enc.term(m_510), FM.Enc.term(h_509), FM.Enc.p(FM.Enc.term(h_509), FM.Enc.term(m_510)), FM.Enc.name(k_508), FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q1{}, x_514, rest_515})]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Machine.Walk.mat.of(Machine.Form.lab{j_520}, Source.Q1{}, k_508, rest_515, ys => Machine.Walk.go(h_509, e_409, ys), ys => Machine.Walk.go(m_510, e_409, ys))), ks}},
            L.Name.is_eq(j_520, k_508, Con{Fun.Fr{Code.F.Walk.go.k6(), [Fun.V.z{}, FM.Enc.name(j_520), FM.Enc.form(Machine.Form.lab{j_520}), FM.Enc.val(rest_515), FM.Enc.val(x_514), FM.Enc.p(FM.Enc.val(x_514), FM.Enc.val(rest_515)), FM.Enc.quan(Source.Q1{}), FM.Enc.term(m_510), FM.Enc.term(h_509), FM.Enc.p(FM.Enc.term(h_509), FM.Enc.term(m_510)), FM.Enc.name(k_508), FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q1{}, x_514, rest_515})]}, ks}),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(j_520, k_508)), Con{Fun.Fr{Code.F.Walk.go.k6(), [Fun.V.z{}, FM.Enc.name(j_520), FM.Enc.form(Machine.Form.lab{j_520}), FM.Enc.val(rest_515), FM.Enc.val(x_514), FM.Enc.p(FM.Enc.val(x_514), FM.Enc.val(rest_515)), FM.Enc.quan(Source.Q1{}), FM.Enc.term(m_510), FM.Enc.term(h_509), FM.Enc.p(FM.Enc.term(h_509), FM.Enc.term(m_510)), FM.Enc.name(k_508), FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q1{}, x_514, rest_515})]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(j_520, k_508)), Con{Fun.Fr{Code.F.Walk.go.k6(), [Fun.V.z{}, FM.Enc.name(j_520), FM.Enc.form(Machine.Form.lab{j_520}), FM.Enc.val(rest_515), FM.Enc.val(x_514), FM.Enc.p(FM.Enc.val(x_514), FM.Enc.val(rest_515)), FM.Enc.quan(Source.Q1{}), FM.Enc.term(m_510), FM.Enc.term(h_509), FM.Enc.p(FM.Enc.term(h_509), FM.Enc.term(m_510)), FM.Enc.name(k_508), FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q1{}, x_514, rest_515})]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Machine.Walk.mat.of(Machine.Form.lab{j_520}, Source.Q1{}, k_508, rest_515, ys => Machine.Walk.go(h_509, e_409, ys), ys => Machine.Walk.go(m_510, e_409, ys))), ks}},
            FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(j_520, k_508)), Con{Fun.Fr{Code.F.Walk.go.k6(), [Fun.V.z{}, FM.Enc.name(j_520), FM.Enc.form(Machine.Form.lab{j_520}), FM.Enc.val(rest_515), FM.Enc.val(x_514), FM.Enc.p(FM.Enc.val(x_514), FM.Enc.val(rest_515)), FM.Enc.quan(Source.Q1{}), FM.Enc.term(m_510), FM.Enc.term(h_509), FM.Enc.p(FM.Enc.term(h_509), FM.Enc.term(m_510)), FM.Enc.name(k_508), FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q1{}, x_514, rest_515})]}, ks}}}),
            Elim.Bool(Source.Name.is_eq(j_520, k_508), m21 => FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k6(), [FM.Enc.bool(m21), Fun.V.z{}, FM.Enc.name(j_520), FM.Enc.form(Machine.Form.lab{j_520}), FM.Enc.val(rest_515), FM.Enc.val(x_514), FM.Enc.p(FM.Enc.val(x_514), FM.Enc.val(rest_515)), FM.Enc.quan(Source.Q1{}), FM.Enc.term(m_510), FM.Enc.term(h_509), FM.Enc.p(FM.Enc.term(h_509), FM.Enc.term(m_510)), FM.Enc.name(k_508), FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q1{}, x_514, rest_515})], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Source.Bool.lazy(Machine.Leaf, m21, w => Machine.Walk.go(h_509, e_409, rest_515), w => Machine.Walk.go(m_510, e_409, Machine.Val.arg{Source.Q1{}, Machine.Val.lab{j_520}, rest_515}))), ks}}),
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
            Elim.Bool(Source.Name.is_eq(j_520, k_508), m22 => FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Walk.go.k6(), [FM.Enc.bool(m22), Fun.V.z{}, FM.Enc.name(j_520), FM.Enc.form(Machine.Form.lab{j_520}), FM.Enc.val(rest_515), FM.Enc.val(x_514), FM.Enc.p(FM.Enc.val(x_514), FM.Enc.val(rest_515)), FM.Enc.quan(Source.Q2{}), FM.Enc.term(m_510), FM.Enc.term(h_509), FM.Enc.p(FM.Enc.term(h_509), FM.Enc.term(m_510)), FM.Enc.name(k_508), FM.Enc.term(Source.Term.Mat{k_508, h_509, m_510}), FM.Enc.val(e_409), FM.Enc.val(Machine.Val.arg{Source.Q2{}, x_514, rest_515})], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.leaf(Source.Bool.lazy(Machine.Leaf, m22, w => Machine.Walk.go(h_509, e_409, rest_515), w => Machine.Walk.go(m_510, e_409, Machine.Val.arg{Source.Q2{}, Machine.Val.lab{j_520}, rest_515}))), ks}}),
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
  FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Args.snoc(), [FM.Enc.val(xs_550), FM.Enc.quan(q_551), FM.Enc.val(x_552)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.val(Machine.Args.snoc(xs_550, q_551, x_552)), ks}}):
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
  FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Args.frames(), [FM.Enc.val(xs_567), FM.Enc.frs(fs_568)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.frs(Machine.Args.frames(xs_567, fs_568)), ks}}):
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
  FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Call.leaf(), [FM.Enc.leaf(w_583), FM.Enc.name(k_584), FM.Enc.val(xs_585), FM.Enc.frs(fs_586)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Call.leaf(w_583, k_584, xs_585, fs_586)), ks}}):
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
  FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Call.try(), [FM.Enc.book(bk_591), FM.Enc.name(k_592), FM.Enc.val(xs_593), FM.Enc.frs(fs_594)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Call.try(bk_591, k_592, xs_593, fs_594)), ks}}):
  FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Call.try(), [FM.Enc.book(bk_591), FM.Enc.name(k_592), FM.Enc.val(xs_593), FM.Enc.frs(fs_594)], ks}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Call.try(), [FM.Enc.book(bk_591), FM.Enc.name(k_592), FM.Enc.val(xs_593), FM.Enc.frs(fs_594)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Call.try(bk_591, k_592, xs_593, fs_594)), ks}},
    FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Call.try(), [FM.Enc.book(bk_591), FM.Enc.name(k_592), FM.Enc.val(xs_593), FM.Enc.frs(fs_594)], ks}}),
    FP.Reach.trans(Code.prog(), Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Call.try(), [FM.Enc.book(bk_591), FM.Enc.name(k_592), FM.Enc.val(xs_593), FM.Enc.frs(fs_594)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.mdef(Source.Book.get(bk_591, k_592)), Con{Fun.Fr{Code.F.Call.try.k1(), [FM.Enc.book(bk_591), FM.Enc.name(k_592), FM.Enc.val(xs_593), FM.Enc.frs(fs_594)]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Call.try(bk_591, k_592, xs_593, fs_594)), ks}},
    L.Book.get(bk_591, k_592, Con{Fun.Fr{Code.F.Call.try.k1(), [FM.Enc.book(bk_591), FM.Enc.name(k_592), FM.Enc.val(xs_593), FM.Enc.frs(fs_594)]}, ks}),
    FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.mdef(Source.Book.get(bk_591, k_592)), Con{Fun.Fr{Code.F.Call.try.k1(), [FM.Enc.book(bk_591), FM.Enc.name(k_592), FM.Enc.val(xs_593), FM.Enc.frs(fs_594)]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.mdef(Source.Book.get(bk_591, k_592)), Con{Fun.Fr{Code.F.Call.try.k1(), [FM.Enc.book(bk_591), FM.Enc.name(k_592), FM.Enc.val(xs_593), FM.Enc.frs(fs_594)]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Call.try(bk_591, k_592, xs_593, fs_594)), ks}},
    FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.mdef(Source.Book.get(bk_591, k_592)), Con{Fun.Fr{Code.F.Call.try.k1(), [FM.Enc.book(bk_591), FM.Enc.name(k_592), FM.Enc.val(xs_593), FM.Enc.frs(fs_594)]}, ks}}}),
    Elim.MDef(Source.Book.get(bk_591, k_592), m23 => FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Call.try.k1(), [FM.Enc.mdef(m23), FM.Enc.book(bk_591), FM.Enc.name(k_592), FM.Enc.val(xs_593), FM.Enc.frs(fs_594)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Call.got(m23, k_592, xs_593, fs_594)), ks}}),
    (2n, {==}),
    +df_596 => Elim.Def(df_596, m24 => FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Call.try.k1(), [FM.Enc.mdef(Some{m24}), FM.Enc.book(bk_591), FM.Enc.name(k_592), FM.Enc.val(xs_593), FM.Enc.frs(fs_594)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Call.got(Some{m24}, k_592, xs_593, fs_594)), ks}}),
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
  FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Apply.go(), [FM.Enc.val(f_602), FM.Enc.quan(q_603), FM.Enc.val(x_604), FM.Enc.book(bk_605), FM.Enc.frs(fs_606)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Apply.go(f_602, q_603, x_604, bk_605, fs_606)), ks}}):
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
            Elim.Bool(Machine.Lam.takes(p_627, q_603, x_604), m25 => FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Apply.go.k1(), [FM.Enc.bool(m25), FM.Enc.term(b_628), FM.Enc.quan(p_627), FM.Enc.val(e_613), FM.Enc.term(Source.Term.Lam{p_627, b_628}), FM.Enc.val(Machine.Val.clo{Source.Term.Lam{p_627, b_628}, e_613}), FM.Enc.quan(q_603), FM.Enc.val(x_604), FM.Enc.book(bk_605), FM.Enc.frs(fs_606)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.move(Source.Bool.lazy(Machine.Move, m25, u => Machine.Move.go{Machine.St.eval{b_628, Machine.Val.env{x_604, e_613}, fs_606}}, u => Machine.Move.stuck{})), ks}}),
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
                    Elim.Bool(Source.Name.is_eq(j_678, k_668), m26 => FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Apply.go.k2(), [FM.Enc.bool(m26), Fun.V.z{}, FM.Enc.name(j_678), FM.Enc.term(m_670), FM.Enc.term(h_669), FM.Enc.p(FM.Enc.term(h_669), FM.Enc.term(m_670)), FM.Enc.name(k_668), FM.Enc.val(e_613), FM.Enc.term(Source.Term.Mat{k_668, h_669, m_670}), FM.Enc.val(Machine.Val.clo{Source.Term.Mat{k_668, h_669, m_670}, e_613}), FM.Enc.quan(Source.Q1{}), FM.Enc.val(Machine.Val.lab{j_678}), FM.Enc.book(bk_605), FM.Enc.frs(fs_606)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.move(Source.Bool.lazy(Machine.Move, m26, u => Machine.Move.go{Machine.St.eval{h_669, e_613, fs_606}}, u => Machine.Move.go{Machine.St.eval{m_670, e_613, Con{Machine.Fr.arg{Source.Q1{}, Machine.Val.lab{j_678}}, fs_606}}})), ks}}),
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
                    Elim.Bool(Source.Name.is_eq(j_692, k_668), m27 => FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Apply.go.k2(), [FM.Enc.bool(m27), Fun.V.z{}, FM.Enc.name(j_692), FM.Enc.term(m_670), FM.Enc.term(h_669), FM.Enc.p(FM.Enc.term(h_669), FM.Enc.term(m_670)), FM.Enc.name(k_668), FM.Enc.val(e_613), FM.Enc.term(Source.Term.Mat{k_668, h_669, m_670}), FM.Enc.val(Machine.Val.clo{Source.Term.Mat{k_668, h_669, m_670}, e_613}), FM.Enc.quan(Source.Q2{}), FM.Enc.val(Machine.Val.lab{j_692}), FM.Enc.book(bk_605), FM.Enc.frs(fs_606)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.move(Source.Bool.lazy(Machine.Move, m27, u => Machine.Move.go{Machine.St.eval{h_669, e_613, fs_606}}, u => Machine.Move.go{Machine.St.eval{m_670, e_613, Con{Machine.Fr.arg{Source.Q2{}, Machine.Val.lab{j_692}}, fs_606}}})), ks}}),
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
  FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Val.force(), [FM.Enc.val(x_712), FM.Enc.frs(fs_713)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Val.force(x_712, fs_713)), ks}}):
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
  FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Eval.go(), [FM.Enc.term(t_727), FM.Enc.val(e_728), FM.Enc.frs(fs_729), FM.Enc.book(bk_730)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Eval.go(t_727, e_728, fs_729, bk_730)), ks}}):
  match t_727:
    case Source.Term.Var{+i_731}:
      FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Eval.go(), [FM.Enc.term(Source.Term.Var{i_731}), FM.Enc.val(e_728), FM.Enc.frs(fs_729), FM.Enc.book(bk_730)], ks}}, Fun.F.iter(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Eval.go(), [FM.Enc.term(Source.Term.Var{i_731}), FM.Enc.val(e_728), FM.Enc.frs(fs_729), FM.Enc.book(bk_730)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Eval.go(Source.Term.Var{i_731}, e_728, fs_729, bk_730)), ks}},
        FP.Reach.steps(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Eval.go(), [FM.Enc.term(Source.Term.Var{i_731}), FM.Enc.val(e_728), FM.Enc.frs(fs_729), FM.Enc.book(bk_730)], ks}}),
        FP.Reach.trans(Code.prog(), Fun.F.iter(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Eval.go(), [FM.Enc.term(Source.Term.Var{i_731}), FM.Enc.val(e_728), FM.Enc.frs(fs_729), FM.Enc.book(bk_730)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.look(Machine.Env.find(e_728, i_731)), Con{Fun.Fr{Code.F.Eval.go.k1(), [Fun.V.z{}, FM.Enc.nat(i_731), FM.Enc.term(Source.Term.Var{i_731}), FM.Enc.val(e_728), FM.Enc.frs(fs_729), FM.Enc.book(bk_730)]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Eval.go(Source.Term.Var{i_731}, e_728, fs_729, bk_730)), ks}},
        L.Env.find(e_728, i_731, Con{Fun.Fr{Code.F.Eval.go.k1(), [Fun.V.z{}, FM.Enc.nat(i_731), FM.Enc.term(Source.Term.Var{i_731}), FM.Enc.val(e_728), FM.Enc.frs(fs_729), FM.Enc.book(bk_730)]}, ks}),
        FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.look(Machine.Env.find(e_728, i_731)), Con{Fun.Fr{Code.F.Eval.go.k1(), [Fun.V.z{}, FM.Enc.nat(i_731), FM.Enc.term(Source.Term.Var{i_731}), FM.Enc.val(e_728), FM.Enc.frs(fs_729), FM.Enc.book(bk_730)]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.look(Machine.Env.find(e_728, i_731)), Con{Fun.Fr{Code.F.Eval.go.k1(), [Fun.V.z{}, FM.Enc.nat(i_731), FM.Enc.term(Source.Term.Var{i_731}), FM.Enc.val(e_728), FM.Enc.frs(fs_729), FM.Enc.book(bk_730)]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Eval.go(Source.Term.Var{i_731}, e_728, fs_729, bk_730)), ks}},
        FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.look(Machine.Env.find(e_728, i_731)), Con{Fun.Fr{Code.F.Eval.go.k1(), [Fun.V.z{}, FM.Enc.nat(i_731), FM.Enc.term(Source.Term.Var{i_731}), FM.Enc.val(e_728), FM.Enc.frs(fs_729), FM.Enc.book(bk_730)]}, ks}}}),
        Elim.Look(Machine.Env.find(e_728, i_731), m28 => FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Eval.go.k1(), [FM.Enc.look(m28), Fun.V.z{}, FM.Enc.nat(i_731), FM.Enc.term(Source.Term.Var{i_731}), FM.Enc.val(e_728), FM.Enc.frs(fs_729), FM.Enc.book(bk_730)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Eval.var(m28, fs_729)), ks}}),
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
  FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Name.is_quan(), [FM.Enc.name(n_770)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_quan(n_770)), ks}}):
  FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Name.is_quan(), [FM.Enc.name(n_770)], ks}}, Fun.F.iter(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Name.is_quan(), [FM.Enc.name(n_770)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_quan(n_770)), ks}},
    FP.Reach.steps(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Name.is_quan(), [FM.Enc.name(n_770)], ks}}),
    FP.Reach.trans(Code.prog(), Fun.F.iter(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Name.is_quan(), [FM.Enc.name(n_770)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(n_770, Source.Name.of("Q0"))), Con{Fun.Fr{Code.F.Name.is_quan.k1(), [FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.name(n_770)]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_quan(n_770)), ks}},
    L.Name.is_eq(n_770, Source.Name.of("Q0"), Con{Fun.Fr{Code.F.Name.is_quan.k1(), [FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.name(n_770)]}, ks}),
    FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(n_770, Source.Name.of("Q0"))), Con{Fun.Fr{Code.F.Name.is_quan.k1(), [FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.name(n_770)]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(n_770, Source.Name.of("Q0"))), Con{Fun.Fr{Code.F.Name.is_quan.k1(), [FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.name(n_770)]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_quan(n_770)), ks}},
    FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(n_770, Source.Name.of("Q0"))), Con{Fun.Fr{Code.F.Name.is_quan.k1(), [FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.name(n_770)]}, ks}}}),
    Elim.Bool(Source.Name.is_eq(n_770, Source.Name.of("Q0")), m29 => FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Name.is_quan.k1(), [FM.Enc.bool(m29), FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.name(n_770)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(m29 || Source.Name.is_eq(n_770, Source.Name.of("Q1")) || Source.Name.is_eq(n_770, Source.Name.of("Q2"))), ks}}),
    FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Name.is_quan.k1(), [FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.name(n_770)], ks}}, Fun.F.iter(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Name.is_quan.k1(), [FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.name(n_770)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(False{} || Source.Name.is_eq(n_770, Source.Name.of("Q1")) || Source.Name.is_eq(n_770, Source.Name.of("Q2"))), ks}},
    FP.Reach.steps(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Name.is_quan.k1(), [FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.name(n_770)], ks}}),
    FP.Reach.trans(Code.prog(), Fun.F.iter(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Name.is_quan.k1(), [FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.name(n_770)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(n_770, Source.Name.of("Q1"))), Con{Fun.Fr{Code.F.Name.is_quan.k2(), [FM.Enc.name(Source.Name.of("Q1")), FM.Enc.name(Source.Name.of("1")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.name(n_770)]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(False{} || Source.Name.is_eq(n_770, Source.Name.of("Q1")) || Source.Name.is_eq(n_770, Source.Name.of("Q2"))), ks}},
    L.Name.is_eq(n_770, Source.Name.of("Q1"), Con{Fun.Fr{Code.F.Name.is_quan.k2(), [FM.Enc.name(Source.Name.of("Q1")), FM.Enc.name(Source.Name.of("1")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.name(n_770)]}, ks}),
    FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(n_770, Source.Name.of("Q1"))), Con{Fun.Fr{Code.F.Name.is_quan.k2(), [FM.Enc.name(Source.Name.of("Q1")), FM.Enc.name(Source.Name.of("1")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.name(n_770)]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(n_770, Source.Name.of("Q1"))), Con{Fun.Fr{Code.F.Name.is_quan.k2(), [FM.Enc.name(Source.Name.of("Q1")), FM.Enc.name(Source.Name.of("1")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.name(n_770)]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(False{} || Source.Name.is_eq(n_770, Source.Name.of("Q1")) || Source.Name.is_eq(n_770, Source.Name.of("Q2"))), ks}},
    FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(n_770, Source.Name.of("Q1"))), Con{Fun.Fr{Code.F.Name.is_quan.k2(), [FM.Enc.name(Source.Name.of("Q1")), FM.Enc.name(Source.Name.of("1")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.name(n_770)]}, ks}}}),
    Elim.Bool(Source.Name.is_eq(n_770, Source.Name.of("Q1")), m30 => FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Name.is_quan.k2(), [FM.Enc.bool(m30), FM.Enc.name(Source.Name.of("Q1")), FM.Enc.name(Source.Name.of("1")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.name(n_770)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.bool(False{} || m30 || Source.Name.is_eq(n_770, Source.Name.of("Q2"))), ks}}),
    FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Name.is_quan.k2(), [FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q1")), FM.Enc.name(Source.Name.of("1")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.name(n_770)], ks}}, Fun.F.iter(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Name.is_quan.k2(), [FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q1")), FM.Enc.name(Source.Name.of("1")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.name(n_770)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(False{} || False{} || Source.Name.is_eq(n_770, Source.Name.of("Q2"))), ks}},
    FP.Reach.steps(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Name.is_quan.k2(), [FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q1")), FM.Enc.name(Source.Name.of("1")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.name(n_770)], ks}}),
    L.Name.is_eq(n_770, Source.Name.of("Q2"), ks)),
    (2n, {==}))))),
    (2n, {==})))))

def L.Term.qmin(+i_773: List<&2, Nat>, +j_774: List<&2, Nat>, +ks: List<&2, Fun.Fr>) ->
  FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Term.qmin(), [FM.Enc.name(i_773), FM.Enc.name(j_774)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.term(Source.Term.qmin(i_773, j_774)), ks}}):
  FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Term.qmin(), [FM.Enc.name(i_773), FM.Enc.name(j_774)], ks}}, Fun.F.iter(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Term.qmin(), [FM.Enc.name(i_773), FM.Enc.name(j_774)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.term(Source.Term.qmin(i_773, j_774)), ks}},
    FP.Reach.steps(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Term.qmin(), [FM.Enc.name(i_773), FM.Enc.name(j_774)], ks}}),
    FP.Reach.trans(Code.prog(), Fun.F.iter(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Term.qmin(), [FM.Enc.name(i_773), FM.Enc.name(j_774)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(i_773, Source.Name.of("Q2"))), Con{Fun.Fr{Code.F.Term.qmin.k1(), [FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.term(Source.Term.qmin(i_773, j_774)), ks}},
    L.Name.is_eq(i_773, Source.Name.of("Q2"), Con{Fun.Fr{Code.F.Term.qmin.k1(), [FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)]}, ks}),
    FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(i_773, Source.Name.of("Q2"))), Con{Fun.Fr{Code.F.Term.qmin.k1(), [FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(i_773, Source.Name.of("Q2"))), Con{Fun.Fr{Code.F.Term.qmin.k1(), [FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.term(Source.Term.qmin(i_773, j_774)), ks}},
    FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(i_773, Source.Name.of("Q2"))), Con{Fun.Fr{Code.F.Term.qmin.k1(), [FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)]}, ks}}}),
    Elim.Bool(Source.Name.is_eq(i_773, Source.Name.of("Q2")), m31 => FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Term.qmin.k1(), [FM.Enc.bool(m31), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.term(Source.Bool.if(Source.Term, m31, Source.Term.Lab{j_774}, Source.Bool.if(Source.Term, Source.Name.is_eq(j_774, Source.Name.of("Q2")), Source.Term.Lab{i_773}, Source.Bool.if(Source.Term, Source.Name.is_eq(i_773, Source.Name.of("Q0")) || Source.Name.is_eq(j_774, Source.Name.of("Q0")), Source.Term.Lab{Source.Name.of("Q0")}, Source.Term.Lab{Source.Name.of("Q1")})))), ks}}),
    FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Term.qmin.k1(), [FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)], ks}}, Fun.F.iter(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Term.qmin.k1(), [FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.term(Source.Bool.if(Source.Term, False{}, Source.Term.Lab{j_774}, Source.Bool.if(Source.Term, Source.Name.is_eq(j_774, Source.Name.of("Q2")), Source.Term.Lab{i_773}, Source.Bool.if(Source.Term, Source.Name.is_eq(i_773, Source.Name.of("Q0")) || Source.Name.is_eq(j_774, Source.Name.of("Q0")), Source.Term.Lab{Source.Name.of("Q0")}, Source.Term.Lab{Source.Name.of("Q1")})))), ks}},
    FP.Reach.steps(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Term.qmin.k1(), [FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)], ks}}),
    FP.Reach.trans(Code.prog(), Fun.F.iter(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Term.qmin.k1(), [FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(j_774, Source.Name.of("Q2"))), Con{Fun.Fr{Code.F.Term.qmin.k2(), [FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.term(Source.Bool.if(Source.Term, False{}, Source.Term.Lab{j_774}, Source.Bool.if(Source.Term, Source.Name.is_eq(j_774, Source.Name.of("Q2")), Source.Term.Lab{i_773}, Source.Bool.if(Source.Term, Source.Name.is_eq(i_773, Source.Name.of("Q0")) || Source.Name.is_eq(j_774, Source.Name.of("Q0")), Source.Term.Lab{Source.Name.of("Q0")}, Source.Term.Lab{Source.Name.of("Q1")})))), ks}},
    L.Name.is_eq(j_774, Source.Name.of("Q2"), Con{Fun.Fr{Code.F.Term.qmin.k2(), [FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)]}, ks}),
    FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(j_774, Source.Name.of("Q2"))), Con{Fun.Fr{Code.F.Term.qmin.k2(), [FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(j_774, Source.Name.of("Q2"))), Con{Fun.Fr{Code.F.Term.qmin.k2(), [FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.term(Source.Bool.if(Source.Term, False{}, Source.Term.Lab{j_774}, Source.Bool.if(Source.Term, Source.Name.is_eq(j_774, Source.Name.of("Q2")), Source.Term.Lab{i_773}, Source.Bool.if(Source.Term, Source.Name.is_eq(i_773, Source.Name.of("Q0")) || Source.Name.is_eq(j_774, Source.Name.of("Q0")), Source.Term.Lab{Source.Name.of("Q0")}, Source.Term.Lab{Source.Name.of("Q1")})))), ks}},
    FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(j_774, Source.Name.of("Q2"))), Con{Fun.Fr{Code.F.Term.qmin.k2(), [FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)]}, ks}}}),
    Elim.Bool(Source.Name.is_eq(j_774, Source.Name.of("Q2")), m32 => FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Term.qmin.k2(), [FM.Enc.bool(m32), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.term(Source.Bool.if(Source.Term, m32, Source.Term.Lab{i_773}, Source.Bool.if(Source.Term, Source.Name.is_eq(i_773, Source.Name.of("Q0")) || Source.Name.is_eq(j_774, Source.Name.of("Q0")), Source.Term.Lab{Source.Name.of("Q0")}, Source.Term.Lab{Source.Name.of("Q1")}))), ks}}),
    FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Term.qmin.k2(), [FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)], ks}}, Fun.F.iter(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Term.qmin.k2(), [FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.term(Source.Bool.if(Source.Term, False{}, Source.Term.Lab{i_773}, Source.Bool.if(Source.Term, Source.Name.is_eq(i_773, Source.Name.of("Q0")) || Source.Name.is_eq(j_774, Source.Name.of("Q0")), Source.Term.Lab{Source.Name.of("Q0")}, Source.Term.Lab{Source.Name.of("Q1")}))), ks}},
    FP.Reach.steps(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Term.qmin.k2(), [FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)], ks}}),
    FP.Reach.trans(Code.prog(), Fun.F.iter(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Term.qmin.k2(), [FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(i_773, Source.Name.of("Q0"))), Con{Fun.Fr{Code.F.Term.qmin.k3(), [FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.term(Source.Bool.if(Source.Term, False{}, Source.Term.Lab{i_773}, Source.Bool.if(Source.Term, Source.Name.is_eq(i_773, Source.Name.of("Q0")) || Source.Name.is_eq(j_774, Source.Name.of("Q0")), Source.Term.Lab{Source.Name.of("Q0")}, Source.Term.Lab{Source.Name.of("Q1")}))), ks}},
    L.Name.is_eq(i_773, Source.Name.of("Q0"), Con{Fun.Fr{Code.F.Term.qmin.k3(), [FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)]}, ks}),
    FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(i_773, Source.Name.of("Q0"))), Con{Fun.Fr{Code.F.Term.qmin.k3(), [FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(i_773, Source.Name.of("Q0"))), Con{Fun.Fr{Code.F.Term.qmin.k3(), [FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.term(Source.Bool.if(Source.Term, False{}, Source.Term.Lab{i_773}, Source.Bool.if(Source.Term, Source.Name.is_eq(i_773, Source.Name.of("Q0")) || Source.Name.is_eq(j_774, Source.Name.of("Q0")), Source.Term.Lab{Source.Name.of("Q0")}, Source.Term.Lab{Source.Name.of("Q1")}))), ks}},
    FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(i_773, Source.Name.of("Q0"))), Con{Fun.Fr{Code.F.Term.qmin.k3(), [FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)]}, ks}}}),
    Elim.Bool(Source.Name.is_eq(i_773, Source.Name.of("Q0")), m33 => FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Term.qmin.k3(), [FM.Enc.bool(m33), FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.term(Source.Bool.if(Source.Term, m33 || Source.Name.is_eq(j_774, Source.Name.of("Q0")), Source.Term.Lab{Source.Name.of("Q0")}, Source.Term.Lab{Source.Name.of("Q1")})), ks}}),
    FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Term.qmin.k3(), [FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)], ks}}, Fun.F.iter(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Term.qmin.k3(), [FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.term(Source.Bool.if(Source.Term, False{} || Source.Name.is_eq(j_774, Source.Name.of("Q0")), Source.Term.Lab{Source.Name.of("Q0")}, Source.Term.Lab{Source.Name.of("Q1")})), ks}},
    FP.Reach.steps(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Term.qmin.k3(), [FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)], ks}}),
    FP.Reach.trans(Code.prog(), Fun.F.iter(4n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Term.qmin.k3(), [FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(j_774, Source.Name.of("Q0"))), Con{Fun.Fr{Code.F.Term.qmin.k4(), [FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.term(Source.Bool.if(Source.Term, False{} || Source.Name.is_eq(j_774, Source.Name.of("Q0")), Source.Term.Lab{Source.Name.of("Q0")}, Source.Term.Lab{Source.Name.of("Q1")})), ks}},
    L.Name.is_eq(j_774, Source.Name.of("Q0"), Con{Fun.Fr{Code.F.Term.qmin.k4(), [FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)]}, ks}),
    FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(j_774, Source.Name.of("Q0"))), Con{Fun.Fr{Code.F.Term.qmin.k4(), [FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(j_774, Source.Name.of("Q0"))), Con{Fun.Fr{Code.F.Term.qmin.k4(), [FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.term(Source.Bool.if(Source.Term, False{} || Source.Name.is_eq(j_774, Source.Name.of("Q0")), Source.Term.Lab{Source.Name.of("Q0")}, Source.Term.Lab{Source.Name.of("Q1")})), ks}},
    FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_eq(j_774, Source.Name.of("Q0"))), Con{Fun.Fr{Code.F.Term.qmin.k4(), [FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)]}, ks}}}),
    Elim.Bool(Source.Name.is_eq(j_774, Source.Name.of("Q0")), m34 => FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Term.qmin.k4(), [FM.Enc.bool(m34), FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q0")), FM.Enc.name(Source.Name.of("0")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.bool(False{}), FM.Enc.name(Source.Name.of("Q2")), FM.Enc.name(Source.Name.of("2")), FM.Enc.name(i_773), FM.Enc.name(j_774)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.term(Source.Bool.if(Source.Term, False{} || m34, Source.Term.Lab{Source.Name.of("Q0")}, Source.Term.Lab{Source.Name.of("Q1")})), ks}}),
    (5n, {==}),
    (5n, {==}))))),
    (5n, {==}))))),
    (3n, {==}))))),
    (3n, {==})))))

def L.Ret.meet(+a_779: Machine.Val, +b_780: Machine.Val, +fs_781: List<&2, Machine.Fr>, +ks: List<&2, Fun.Fr>) ->
  FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ret.meet(), [FM.Enc.val(a_779), FM.Enc.val(b_780), FM.Enc.frs(fs_781)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Ret.meet(a_779, b_780, fs_781)), ks}}):
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
            Elim.Bool(Source.Name.is_quan(i_789), m35 => FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ret.meet.k1(), [FM.Enc.bool(m35), Fun.V.z{}, FM.Enc.name(j_797), Fun.V.z{}, FM.Enc.name(i_789), FM.Enc.val(Machine.Val.lab{i_789}), FM.Enc.val(Machine.Val.lab{j_797}), FM.Enc.frs(fs_781)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.move(Source.Bool.lazy(Machine.Move, m35 && Source.Name.is_quan(j_797), u => Machine.Move.go{Machine.St.eval{Source.Term.qmin(i_789, j_797), Machine.Val.nil{}, fs_781}}, u => Machine.Move.stuck{})), ks}}),
            (2n, {==}),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ret.meet.k1(), [FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(j_797), Fun.V.z{}, FM.Enc.name(i_789), FM.Enc.val(Machine.Val.lab{i_789}), FM.Enc.val(Machine.Val.lab{j_797}), FM.Enc.frs(fs_781)], ks}}, Fun.F.iter(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ret.meet.k1(), [FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(j_797), Fun.V.z{}, FM.Enc.name(i_789), FM.Enc.val(Machine.Val.lab{i_789}), FM.Enc.val(Machine.Val.lab{j_797}), FM.Enc.frs(fs_781)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.move(Source.Bool.lazy(Machine.Move, True{} && Source.Name.is_quan(j_797), u => Machine.Move.go{Machine.St.eval{Source.Term.qmin(i_789, j_797), Machine.Val.nil{}, fs_781}}, u => Machine.Move.stuck{})), ks}},
            FP.Reach.steps(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ret.meet.k1(), [FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(j_797), Fun.V.z{}, FM.Enc.name(i_789), FM.Enc.val(Machine.Val.lab{i_789}), FM.Enc.val(Machine.Val.lab{j_797}), FM.Enc.frs(fs_781)], ks}}),
            FP.Reach.trans(Code.prog(), Fun.F.iter(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ret.meet.k1(), [FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(j_797), Fun.V.z{}, FM.Enc.name(i_789), FM.Enc.val(Machine.Val.lab{i_789}), FM.Enc.val(Machine.Val.lab{j_797}), FM.Enc.frs(fs_781)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_quan(j_797)), Con{Fun.Fr{Code.F.Ret.meet.k2(), [Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(j_797), Fun.V.z{}, FM.Enc.name(i_789), FM.Enc.val(Machine.Val.lab{i_789}), FM.Enc.val(Machine.Val.lab{j_797}), FM.Enc.frs(fs_781)]}, ks}}}, Fun.Step.go{Fun.S.ret{FM.Enc.move(Source.Bool.lazy(Machine.Move, True{} && Source.Name.is_quan(j_797), u => Machine.Move.go{Machine.St.eval{Source.Term.qmin(i_789, j_797), Machine.Val.nil{}, fs_781}}, u => Machine.Move.stuck{})), ks}},
            L.Name.is_quan(j_797, Con{Fun.Fr{Code.F.Ret.meet.k2(), [Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(j_797), Fun.V.z{}, FM.Enc.name(i_789), FM.Enc.val(Machine.Val.lab{i_789}), FM.Enc.val(Machine.Val.lab{j_797}), FM.Enc.frs(fs_781)]}, ks}),
            FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_quan(j_797)), Con{Fun.Fr{Code.F.Ret.meet.k2(), [Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(j_797), Fun.V.z{}, FM.Enc.name(i_789), FM.Enc.val(Machine.Val.lab{i_789}), FM.Enc.val(Machine.Val.lab{j_797}), FM.Enc.frs(fs_781)]}, ks}}}, Fun.F.iter(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_quan(j_797)), Con{Fun.Fr{Code.F.Ret.meet.k2(), [Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(j_797), Fun.V.z{}, FM.Enc.name(i_789), FM.Enc.val(Machine.Val.lab{i_789}), FM.Enc.val(Machine.Val.lab{j_797}), FM.Enc.frs(fs_781)]}, ks}}}), Fun.Step.go{Fun.S.ret{FM.Enc.move(Source.Bool.lazy(Machine.Move, True{} && Source.Name.is_quan(j_797), u => Machine.Move.go{Machine.St.eval{Source.Term.qmin(i_789, j_797), Machine.Val.nil{}, fs_781}}, u => Machine.Move.stuck{})), ks}},
            FP.Reach.steps(1n, Code.prog(), Fun.Step.go{Fun.S.ret{FM.Enc.bool(Source.Name.is_quan(j_797)), Con{Fun.Fr{Code.F.Ret.meet.k2(), [Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(j_797), Fun.V.z{}, FM.Enc.name(i_789), FM.Enc.val(Machine.Val.lab{i_789}), FM.Enc.val(Machine.Val.lab{j_797}), FM.Enc.frs(fs_781)]}, ks}}}),
            Elim.Bool(Source.Name.is_quan(j_797), m36 => FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ret.meet.k2(), [FM.Enc.bool(m36), Fun.V.z{}, Fun.V.z{}, FM.Enc.bool(True{}), Fun.V.z{}, FM.Enc.name(j_797), Fun.V.z{}, FM.Enc.name(i_789), FM.Enc.val(Machine.Val.lab{i_789}), FM.Enc.val(Machine.Val.lab{j_797}), FM.Enc.frs(fs_781)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.move(Source.Bool.lazy(Machine.Move, m36, u => Machine.Move.go{Machine.St.eval{Source.Term.qmin(i_789, j_797), Machine.Val.nil{}, fs_781}}, u => Machine.Move.stuck{})), ks}}),
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
  FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ret.frame(), [FM.Enc.fr(fr_811), FM.Enc.val(v_812), FM.Enc.frs(fs_813), FM.Enc.book(bk_814)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Ret.frame(fr_811, v_812, fs_813, bk_814)), ks}}):
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
            Elim.Bool(Machine.Val.is_data(v_812), m37 => FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ret.frame.k1(), [FM.Enc.bool(m37), Fun.V.z{}, Fun.V.z{}, FM.Enc.val(e_821), FM.Enc.term(f_820), FM.Enc.p(FM.Enc.term(f_820), FM.Enc.val(e_821)), FM.Enc.quan(Source.Q2{}), FM.Enc.fr(Machine.Fr.let{Source.Q2{}, f_820, e_821}), FM.Enc.val(v_812), FM.Enc.frs(fs_813), FM.Enc.book(bk_814)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.move(Source.Bool.lazy(Machine.Move, Bool.not(Source.Quan.is_q2(Source.Q2{})) || m37, u => Machine.Move.go{Machine.St.eval{f_820, Machine.Val.env{v_812, e_821}, fs_813}}, u => Machine.Move.stuck{})), ks}}),
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
  FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ret.go(), [FM.Enc.val(v_847), FM.Enc.frs(fs_848), FM.Enc.book(bk_849)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Ret.go(v_847, fs_848, bk_849)), ks}}):
  match fs_848:
    case Nil{}:
      (3n, {==})
    case Con{+fr_850, +rest_851}:
      FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ret.go(), [FM.Enc.val(v_847), FM.Enc.frs(Con{fr_850, rest_851}), FM.Enc.book(bk_849)], ks}}, Fun.F.iter(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ret.go(), [FM.Enc.val(v_847), FM.Enc.frs(Con{fr_850, rest_851}), FM.Enc.book(bk_849)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Ret.go(v_847, Con{fr_850, rest_851}, bk_849)), ks}},
        FP.Reach.steps(2n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Ret.go(), [FM.Enc.val(v_847), FM.Enc.frs(Con{fr_850, rest_851}), FM.Enc.book(bk_849)], ks}}),
        L.Ret.frame(fr_850, v_847, rest_851, bk_849, ks))

def L.Machine.step(+s_852: Machine.St, +bk_853: List<&2, Source.Def>, +ks: List<&2, Fun.Fr>) ->
  FP.Reach(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Machine.step(), [FM.Enc.st(s_852), FM.Enc.book(bk_853)], ks}}, Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Machine.step(s_852, bk_853)), ks}}):
  match s_852:
    case Machine.St.eval{+t_854, +e_855, +fs_856}:
      FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Machine.step(), [FM.Enc.st(Machine.St.eval{t_854, e_855, fs_856}), FM.Enc.book(bk_853)], ks}}, Fun.F.iter(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Machine.step(), [FM.Enc.st(Machine.St.eval{t_854, e_855, fs_856}), FM.Enc.book(bk_853)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Machine.step(Machine.St.eval{t_854, e_855, fs_856}, bk_853)), ks}},
        FP.Reach.steps(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Machine.step(), [FM.Enc.st(Machine.St.eval{t_854, e_855, fs_856}), FM.Enc.book(bk_853)], ks}}),
        L.Eval.go(t_854, e_855, fs_856, bk_853, ks))
    case Machine.St.ret{+v_857, +fs_858}:
      FP.Reach.trans(Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Machine.step(), [FM.Enc.st(Machine.St.ret{v_857, fs_858}), FM.Enc.book(bk_853)], ks}}, Fun.F.iter(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Machine.step(), [FM.Enc.st(Machine.St.ret{v_857, fs_858}), FM.Enc.book(bk_853)], ks}}), Fun.Step.go{Fun.S.ret{FM.Enc.move(Machine.Machine.step(Machine.St.ret{v_857, fs_858}, bk_853)), ks}},
        FP.Reach.steps(3n, Code.prog(), Fun.Step.go{Fun.S.run{Code.F.Machine.step(), [FM.Enc.st(Machine.St.ret{v_857, fs_858}), FM.Enc.book(bk_853)], ks}}),
        L.Ret.go(v_857, fs_858, bk_853, ks))
