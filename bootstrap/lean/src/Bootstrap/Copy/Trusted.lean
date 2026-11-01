import Bootstrap.Book

-- Made by scripts/Defs.lean from the `bend -o` output of bootstrap/bend/src/compiler/trusted.bend (while proof.bend has open TODOs, bend -o refuses it: this is the same lowering, bend2/safe.ts, of the book that bend2 checked, with each hole read as its own def; no def or type copied here names one).
-- Do not edit it.

open Quan Term

set_option maxRecDepth 100000

def «trustedCopy.Wasm.Outcome» : Def :=
  ⟨"Wasm.Outcome",
    (Term.Typ (Term.Lab "Q2")),
    (Term.Sig Quan.Q1 (Term.Enu ["Wasm.Outcome.result", "Wasm.Outcome.out_of_memory", "Wasm.Outcome.no_result", "Wasm.Outcome.unsupported",
 "Wasm.Outcome.trap", "Wasm.Outcome.not_done"]) (Term.App Quan.Q1 (Term.Ref "Wasm.Outcome.arms") (Term.Var 0))),
    false⟩

def «trustedCopy.Wasm.run» : Def :=
  ⟨"Wasm.run",
    (Term.All Quan.Q1 (Term.Ref "Nat") (Term.All Quan.Q1 (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "U32")) (Term.All Quan.Q1 (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "U32")) (Term.All Quan.Q1 (Term.Ref "U32") (Term.Ref "Wasm.Outcome"))))),
    (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Wasm.run.made") (Term.Var 3)) (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Wasm.instantiate") (Term.Var 2)) (Term.Var 0))) (Term.Var 1)))))),
    false⟩

def «trustedCopy.Compiler.compile» : Def :=
  ⟨"Compiler.compile",
    (Term.All Quan.Q2 (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "U32")) (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "U32"))),
    (Term.Lam Quan.Q2 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Compiler.compile.of") (Term.Lam Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Compiler.module") (Term.Var 0)))) (Term.App Quan.Q2 (Term.App Quan.Q1 (Term.Ref "Img.small") (Term.Var 0)) (Term.Ref "U32.lit0"))) (Term.App Quan.Q1 (Term.Ref "Book.read") (Term.Var 0)))),
    false⟩

def «trustedCopy.Either.arms» : Def :=
  ⟨"Either.arms",
    (Term.All Quan.Q0 (Term.Enu ["Q0", "Q1", "Q2"]) (Term.All Quan.Q0 (Term.Enu ["Q0", "Q1", "Q2"]) (Term.All Quan.Q0 (Term.Typ (Term.Var 1)) (Term.All Quan.Q0 (Term.Typ (Term.Var 1)) (Term.All Quan.Q1 (Term.Enu ["Inl", "Inr"]) (Term.Typ (Term.Min (Term.Var 4) (Term.Var 3)))))))),
    (Term.Lam Quan.Q0 (Term.Lam Quan.Q0 (Term.Lam Quan.Q0 (Term.Lam Quan.Q0 (Term.Mat "Inl" (Term.Sig Quan.Q1 (Term.Var 1) (Term.Enu ["()"])) (Term.Mat "Inr" (Term.Sig Quan.Q1 (Term.Var 0) (Term.Enu ["()"])) Term.Efq)))))),
    false⟩

def «trustedCopy.Either» : Def :=
  ⟨"Either",
    (Term.All Quan.Q0 (Term.Enu ["Q0", "Q1", "Q2"]) (Term.All Quan.Q0 (Term.Enu ["Q0", "Q1", "Q2"]) (Term.All Quan.Q0 (Term.Typ (Term.Var 1)) (Term.All Quan.Q0 (Term.Typ (Term.Var 1)) (Term.Typ (Term.Min (Term.Var 3) (Term.Var 2))))))),
    (Term.Lam Quan.Q0 (Term.Lam Quan.Q0 (Term.Lam Quan.Q0 (Term.Lam Quan.Q0 (Term.Sig Quan.Q1 (Term.Enu ["Inl", "Inr"]) (Term.App Quan.Q1 (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "Either.arms") (Term.Var 4)) (Term.Var 3)) (Term.Var 2)) (Term.Var 1)) (Term.Var 0))))))),
    false⟩

def «trustedCopy.Or» : Def :=
  ⟨"Or",
    (Term.All Quan.Q0 (Term.Typ (Term.Lab "Q1")) (Term.All Quan.Q0 (Term.Typ (Term.Lab "Q1")) (Term.Typ (Term.Lab "Q1")))),
    (Term.Lam Quan.Q0 (Term.Lam Quan.Q0 (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "Either") (Term.Lab "Q1")) (Term.Lab "Q1")) (Term.Var 1)) (Term.Var 0)))),
    false⟩

def «trustedCopy.main» : Def :=
  ⟨"main",
    (Term.All Quan.Q2 (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "U32")) (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "U32"))),
    (Term.Lam Quan.Q2 (Term.App Quan.Q2 (Term.Ref "Compiler.compile") (Term.Var 0))),
    false⟩

def «trustedCopy.spec.no_wrong_result» : String × Term :=
  ("spec.no_wrong_result",
    (Term.All Quan.Q2 (Term.Ref "Nat") (Term.All Quan.Q2 (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "U32")) (Term.All Quan.Q2 (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "U32")) (Term.All Quan.Q2 (Term.Ref "U32") (Term.All Quan.Q2 (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "U32")) (Term.All Quan.Q1 (Term.Eql (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Wasm.run") (Term.Var 4)) (Term.App Quan.Q2 (Term.Ref "Compiler.compile") (Term.Var 3))) (Term.Var 2)) (Term.Var 1)) (Term.Tup Quan.Q1 (Term.Lab "Wasm.Outcome.result") (Term.Tup Quan.Q1 (Term.Var 0) (Term.Lab "()"))) (Term.Ref "Wasm.Outcome")) (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "Exists") (Term.Ref "Nat")) (Term.Lam Quan.Q0 (Term.Eql (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Program.gives") (Term.Var 5)) (Term.Var 4)) (Term.Var 0)) (Term.Tup Quan.Q1 (Term.Lab "Some") (Term.Tup Quan.Q1 (Term.Var 2) (Term.Lab "()"))) (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "Maybe") (Term.Lab "Q2")) (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "U32")))))))))))))

def «trustedCopy.spec.no_other_failure» : String × Term :=
  ("spec.no_other_failure",
    (Term.All Quan.Q2 (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "U32")) (Term.All Quan.Q2 (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "U32")) (Term.All Quan.Q2 (Term.Ref "Nat") (Term.All Quan.Q2 (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "U32")) (Term.All Quan.Q2 (Term.Ref "U32") (Term.All Quan.Q1 (Term.Eql (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Program.gives") (Term.Var 4)) (Term.Var 3)) (Term.Var 2)) (Term.Tup Quan.Q1 (Term.Lab "Some") (Term.Tup Quan.Q1 (Term.Var 1) (Term.Lab "()"))) (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "Maybe") (Term.Lab "Q2")) (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "U32")))) (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "Exists") (Term.Ref "Nat")) (Term.Lam Quan.Q0 (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "Or") (Term.Eql (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Wasm.run") (Term.Var 0)) (Term.App Quan.Q2 (Term.Ref "Compiler.compile") (Term.Var 6))) (Term.Var 5)) (Term.Var 2)) (Term.Tup Quan.Q1 (Term.Lab "Wasm.Outcome.result") (Term.Tup Quan.Q1 (Term.Var 3) (Term.Lab "()"))) (Term.Ref "Wasm.Outcome"))) (Term.Eql (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Wasm.run") (Term.Var 0)) (Term.App Quan.Q2 (Term.Ref "Compiler.compile") (Term.Var 6))) (Term.Var 5)) (Term.Var 2)) (Term.Tup Quan.Q1 (Term.Lab "Wasm.Outcome.out_of_memory") (Term.Lab "()")) (Term.Ref "Wasm.Outcome"))))))))))))

def «trustedCopy.spec.enough_memory» : String × Term :=
  ("spec.enough_memory",
    (Term.All Quan.Q2 (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "U32")) (Term.All Quan.Q2 (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "U32")) (Term.All Quan.Q2 (Term.Ref "Nat") (Term.All Quan.Q2 (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "U32")) (Term.All Quan.Q2 (Term.Ref "U32") (Term.All Quan.Q1 (Term.Eql (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Program.gives") (Term.Var 4)) (Term.Var 3)) (Term.Var 2)) (Term.Tup Quan.Q1 (Term.Lab "Some") (Term.Tup Quan.Q1 (Term.Var 1) (Term.Lab "()"))) (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "Maybe") (Term.Lab "Q2")) (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "U32")))) (Term.All Quan.Q1 (Term.Eql (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.is_le") (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q2 (Term.Ref "Program.need") (Term.Var 5)) (Term.Var 4)) (Term.Var 3))) (Term.App Quan.Q1 (Term.Ref "Program.memory") (Term.Var 1))) (Term.Tup Quan.Q1 (Term.Lab "True") (Term.Lab "()")) (Term.Ref "Bool")) (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "Exists") (Term.Ref "Nat")) (Term.Lam Quan.Q0 (Term.Eql (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Wasm.run") (Term.Var 0)) (Term.App Quan.Q2 (Term.Ref "Compiler.compile") (Term.Var 7))) (Term.Var 6)) (Term.Var 3)) (Term.Tup Quan.Q1 (Term.Lab "Wasm.Outcome.result") (Term.Tup Quan.Q1 (Term.Var 4) (Term.Lab "()"))) (Term.Ref "Wasm.Outcome"))))))))))))

def trustedCopy.names : List String :=
  ["Quan.arms", "Quan.Q0", "Quan.Q1", "Quan.Q2", "Quan", "Term.arms", "Term.Var", "Term.Ref", "Term.Ann", "Term.Let",
 "Term.Typ", "Term.Min", "Term.All", "Term.Lam", "Term.App", "Term.Sig", "Term.Tup", "Term.Prj", "Term.Enu", "Term.Lab",
 "Term.Mat", "Term.Efq", "Term.Eql", "Term.Rfl", "Term.Rwt", "Term", "Def.arms", "Def", "Item.arms", "Item.quan",
 "Item.nat", "Item.name", "Item.names", "Item.bool", "Item.term", "Item.def", "Item.defs", "Item", "Book.read.succ",
 "Book.read.byte", "Book.read.names", "Book.read.defs", "Book.read.def", "Book.read.var", "Book.read.ref",
 "Book.read.ann", "Book.read.let", "Book.read.typ", "Book.read.min", "Book.read.all", "Book.read.lam", "Book.read.app",
 "Book.read.sig", "Book.read.tup", "Book.read.prj", "Book.read.enu", "Book.read.lab", "Book.read.mat", "Book.read.eql",
 "Book.read.rwt", "Book.read.token32", "Book.read.token24", "Book.read.token16", "Book.read.token8", "Book.read.token",
 "Book.read.step", "Book.read.done", "Book.read.go", "Book.read", "Arg.arms", "Arg", "Quan.live", "Quan.lives_as",
 "Quan.fld", "Name.is_eq", "Term.is_data", "Quan.fits", "Quan.binds", "Term.is_former", "Term.takes", "Term.head",
 "Term.args", "Term.spine", "Env.sub", "Term.shift.at", "Term.shift", "Term.lift.at", "Term.lift", "Term.subst",
 "Term.inst", "Book.get.if", "Book.get", "Eval.walk.if", "Eval.walk.pick", "Eval.walk.app", "Eval.walk.leaf",
 "Eval.walk", "Eval.callWalk.def", "Eval.callWalk.head", "Eval.callWalk", "Eval.waits", "Eval.vals.app",
 "Eval.vals.ref", "Eval.vals.other", "Eval.vals", "Eval.call.if", "Eval.call", "Eval.redex.if", "Eval.redex.pick",
 "Eval.redex", "Quan.read.if", "Quan.read", "Quan.name", "Quan.min", "Eval.meet.of", "Eval.meet", "Eval.step.app",
 "Eval.step.unlet", "Eval.step.let", "Eval.step.tup_b", "Eval.step.tup", "Eval.step.cast", "Eval.step.rwt",
 "Eval.step.min", "Eval.step", "Eval.run", "Eval.steps", "Wasm.Outcome.arms", "Wasm.Outcome.result",
 "Wasm.Outcome.out_of_memory", "Wasm.Outcome.no_result", "Wasm.Outcome.unsupported", "Wasm.Outcome.trap",
 "Wasm.Outcome.not_done", "Wasm.Outcome", "Wasm.Op.arms", "Wasm.Op.add", "Wasm.Op.sub", "Wasm.Op.and", "Wasm.Op.or",
 "Wasm.Op.shl", "Wasm.Op.shr_u", "Wasm.Op.eq", "Wasm.Op.ne", "Wasm.Op.lt_u", "Wasm.Op.gt_u", "Wasm.Op.le_u",
 "Wasm.Op.ge_u", "Wasm.Op", "Wasm.Instr.arms", "Wasm.Instr.const", "Wasm.Instr.local_get", "Wasm.Instr.local_set",
 "Wasm.Instr.local_tee", "Wasm.Instr.op", "Wasm.Instr.eqz", "Wasm.Instr.load", "Wasm.Instr.load8_u", "Wasm.Instr.store",
 "Wasm.Instr.store8", "Wasm.Instr.memory_size", "Wasm.Instr.memory_grow", "Wasm.Instr.block", "Wasm.Instr.loop",
 "Wasm.Instr.br", "Wasm.Instr.br_if", "Wasm.Instr.br_table", "Wasm.Instr", "Wasm.Type.arms", "Wasm.Type",
 "Wasm.Func.arms", "Wasm.Func", "Wasm.Export.arms", "Wasm.Export.func", "Wasm.Export.memory", "Wasm.Export",
 "Wasm.Limits.arms", "Wasm.Limits", "Wasm.Segment.arms", "Wasm.Segment", "Wasm.Module.arms", "Wasm.Module",
 "Wasm.Decoded.arms", "Wasm.Decoded", "Wasm.decode.keep", "Wasm.decode.leb.if", "Wasm.decode.leb.more",
 "Wasm.decode.uleb", "Wasm.decode.sleb.last", "Wasm.decode.sleb.pick", "Wasm.decode.sleb.sign", "Wasm.decode.sleb",
 "Wasm.decode.u32", "Wasm.decode.byte", "Wasm.length32.if", "Wasm.length32.go", "Wasm.length32", "Wasm.decode.bind",
 "Wasm.decode.cons", "Wasm.decode.done", "Wasm.decode.whole", "Wasm.has.if", "Wasm.has", "Wasm.decode.count.if",
 "Wasm.decode.count", "Wasm.decode.take", "Wasm.decode.items_7e_d", "Wasm.decode.items_7e_A", "Wasm.decode.items.qvv",
 "Wasm.decode.vec.qvv", "Wasm.decode.bytes", "Wasm.is_ascii", "Wasm.decode.name", "Wasm.is_i32s", "Wasm.decode.i32s",
 "Wasm.decode.functype", "Wasm.decode.limits.of", "Wasm.decode.limits", "Wasm.decode.export.kind",
 "Wasm.decode.export.of", "Wasm.decode.export", "Wasm.Token.arms", "Wasm.Token.instr", "Wasm.Token.start",
 "Wasm.Token.end", "Wasm.Token", "Wasm.decode.as", "Wasm.decode.index", "Wasm.decode.block", "Wasm.decode.items.qvv_1",
 "Wasm.decode.vec.qvv_1", "Wasm.decode.table", "Wasm.decode.memarg.if", "Wasm.decode.memarg", "Wasm.decode.memory",
 "Wasm.decode.const", "Wasm.decode.token", "Wasm.Open.arms", "Wasm.Open", "Wasm.decode.closed",
 "Wasm.decode.instrs.end", "Wasm.decode.instrs.then", "Wasm.decode.instrs.go", "Wasm.decode.instrs", "Wasm.Code.arms",
 "Wasm.Code", "Wasm.decode.local", "Wasm.locals.if", "Wasm.locals.sum", "Wasm.decode.func.body",
 "Wasm.decode.items.qvv_2", "Wasm.decode.vec.qvv_2", "Wasm.decode.func", "Wasm.decode.code", "Wasm.decode.data.if",
 "Wasm.decode.data", "Wasm.Section.arms", "Wasm.Section", "Wasm.decode.section", "Wasm.decode.sections.cons",
 "Wasm.decode.sections.got", "Wasm.decode.sections", "Wasm.section.is_known", "Wasm.sections.is_ordered",
 "Wasm.sections.find.if", "Wasm.sections.find", "Wasm.decode.part_7e_d", "Wasm.decode.part_7e_A",
 "Wasm.decode.items.qvv_3", "Wasm.decode.vec.qvv_3", "Wasm.decode.part.qvv", "Wasm.decode.one", "Wasm.type.at.if",
 "Wasm.type.at", "Wasm.func.of", "Wasm.funcs.cons", "Wasm.funcs.of", "Wasm.decode.items.qvv_4", "Wasm.decode.vec.qvv_4",
 "Wasm.decode.part.qvv_1", "Wasm.decode.part.qvv_2", "Wasm.decode.items.qvv_5", "Wasm.decode.vec.qvv_5",
 "Wasm.decode.part.qvv_3", "Wasm.decode.items.qvv_6", "Wasm.decode.vec.qvv_6", "Wasm.decode.part.qvv_4",
 "Wasm.decode.items.qvv_7", "Wasm.decode.vec.qvv_7", "Wasm.decode.part.qvv_5", "Wasm.decode.items.qvv_8",
 "Wasm.decode.vec.qvv_8", "Wasm.decode.part.qvv_6", "Wasm.decode.module.parts", "Wasm.decode.module.if",
 "Wasm.decode.module.sections", "Wasm.decode.sections.if", "Wasm.decode.module.header", "Wasm.decode.module",
 "Wasm.Height.arms", "Wasm.Height.at", "Wasm.Height.any", "Wasm.Height", "Wasm.valid.if", "Wasm.valid.label.if",
 "Wasm.valid.label", "Wasm.valid.is_empty", "Wasm.valid.br", "Wasm.valid.br_if", "Wasm.valid.is_type",
 "Wasm.valid.table.all", "Wasm.valid.table", "Wasm.valid.go", "Wasm.valid.is_results", "Wasm.valid.func",
 "Wasm.valid.funcs", "Wasm.valid.max", "Wasm.valid.memory", "Wasm.export.name", "Wasm.valid.is_new",
 "Wasm.valid.exports", "Wasm.valid.data", "Wasm.valid.module", "Wasm.Bytes.arms", "Wasm.Bytes.zero", "Wasm.Bytes.byte",
 "Wasm.Bytes.node", "Wasm.Bytes", "Wasm.Peek.arms", "Wasm.Peek", "Wasm.Bytes.peek.lo", "Wasm.Bytes.peek.hi",
 "Wasm.Bytes.peek", "Wasm.Bytes.set", "Wasm.read8", "Wasm.write8", "Wasm.read32.b3", "Wasm.read32.b2", "Wasm.read32.b1",
 "Wasm.read32.b0", "Wasm.read32", "Wasm.write32", "Wasm.read.bytes.of", "Wasm.read.bytes", "Wasm.write.bytes",
 "Wasm.fits", "Wasm.inside", "Wasm.op", "Wasm.Memory.arms", "Wasm.Memory", "Wasm.Label.arms", "Wasm.Label",
 "Wasm.Frame.arms", "Wasm.Frame", "Wasm.Step.arms", "Wasm.Step.next", "Wasm.Step.done", "Wasm.Step.trap", "Wasm.Step",
 "Wasm.step.end", "Wasm.step.br.to", "Wasm.step.br", "Wasm.step.set", "Wasm.step.tee", "Wasm.step.op", "Wasm.step.eqz",
 "Wasm.load.of", "Wasm.step.peeked", "Wasm.step.loaded", "Wasm.step.load", "Wasm.store.of", "Wasm.step.stored",
 "Wasm.step.store", "Wasm.step.size", "Wasm.step.grown", "Wasm.step.grow", "Wasm.step.br_if.if", "Wasm.step.br_if",
 "Wasm.table.pick.if", "Wasm.table.pick", "Wasm.step.table", "Wasm.step.instr", "Wasm.step", "Wasm.Call.arms",
 "Wasm.Call.done", "Wasm.Call.trap", "Wasm.Call.not_done", "Wasm.Call", "Wasm.call.plus", "Wasm.call.stepped",
 "Wasm.call.go", "Wasm.call", "Wasm.Instance.arms", "Wasm.Instance", "Wasm.Made.arms", "Wasm.Made.instance",
 "Wasm.Made.unsupported", "Wasm.Made.out_of_memory", "Wasm.Made.trap", "Wasm.Made", "Wasm.min.if", "Wasm.min",
 "Wasm.limit", "Wasm.memory.of.if", "Wasm.memory.of", "Wasm.fits.len", "Wasm.memory.init.if", "Wasm.memory.init",
 "Wasm.instantiate.made", "Wasm.instantiate.sized", "Wasm.instantiate.valid", "Wasm.instantiate.decoded",
 "Wasm.instantiate", "Wasm.export.find.if", "Wasm.export.find", "Wasm.export.has_memory", "Wasm.func.at.if",
 "Wasm.func.at", "Wasm.export.func", "Wasm.func.is_type", "Wasm.Invoked.arms", "Wasm.Invoked.values",
 "Wasm.Invoked.trap", "Wasm.Invoked.not_done", "Wasm.Invoked.unsupported", "Wasm.Invoked", "Wasm.invoked",
 "Wasm.invoke.arity", "Wasm.invoke.found", "Wasm.invoke", "Wasm.name.memory", "Wasm.name.alloc", "Wasm.name.run",
 "Wasm.run.output.if", "Wasm.run.output.n", "Wasm.run.output.a", "Wasm.run.output.at", "Wasm.run.output",
 "Wasm.run.status", "Wasm.run.ran", "Wasm.run.written", "Wasm.run.input", "Wasm.run.alloced.if", "Wasm.run.alloced",
 "Wasm.run.sized", "Wasm.run.is_host", "Wasm.run.instance", "Wasm.run.made", "Wasm.run", "Program.name.unit",
 "Program.name.nil", "Program.name.con", "Program.name.u32", "Program.name.wnil", "Program.name.wcon",
 "Program.name.true", "Program.name.false", "Program.name.main", "Program.fields", "Program.ctor", "Program.bit",
 "Program.word", "Program.cell.of", "Program.cell", "Program.bytes", "Program.start", "Program.unbit.if",
 "Program.unbit", "Program.unword.nil", "Program.unword.con", "Program.unword", "Program.unbytes.nil",
 "Program.unbytes.byte", "Program.unbytes.con", "Program.unbytes", "Program.result.if", "Program.result",
 "Program.gives.of", "Program.gives", "Term.size", "Program.largest.next", "Program.largest.go", "Program.largest.of",
 "Program.largest", "Program.need", "Program.memory", "Wasm.encode.leb.if", "Wasm.encode.uleb.go", "Wasm.encode.uleb",
 "Wasm.encode.sign", "Wasm.encode.sleb.go", "Wasm.encode.sleb", "Wasm.encode.len", "Wasm.encode.vec",
 "Wasm.encode.sized", "Wasm.encode.labels", "Wasm.encode.opcode", "Wasm.encode.with", "Wasm.encode.instrs",
 "Wasm.encode.i32s", "Wasm.encode.functype", "Wasm.encode.functypes", "Wasm.encode.indices", "Wasm.encode.locals",
 "Wasm.encode.code", "Wasm.encode.codes", "Wasm.encode.export", "Wasm.encode.exports", "Wasm.encode.limits",
 "Wasm.encode.section", "Wasm.encode.memory", "Wasm.encode.data", "Wasm.encode", "Cir.Cell.arms", "Cir.Cell",
 "Cir.Cell.zero", "Cir.Cell.get", "Cir.Cell.set", "Cir.Cells.arms", "Cir.Cells.none", "Cir.Cells.one", "Cir.Cells.node",
 "Cir.Cells", "Cir.Cells.get.at", "Cir.Cells.set.at", "Cir.Cells.get", "Cir.Cells.set", "Cir.Expr.arms",
 "Cir.Expr.const", "Cir.Expr.get", "Cir.Expr.op", "Cir.Expr.eqz", "Cir.Expr.field", "Cir.Expr.byte", "Cir.Expr.size",
 "Cir.Expr", "Cir.Stmt.arms", "Cir.Stmt.nop", "Cir.Stmt.set", "Cir.Stmt.store", "Cir.Stmt.alloc", "Cir.Stmt.emit",
 "Cir.Stmt.seq", "Cir.Stmt.if", "Cir.Stmt.while", "Cir.Stmt.halt", "Cir.Stmt", "Cir.State.arms", "Cir.State",
 "Cir.Out.arms", "Cir.Out.next", "Cir.Out.halt", "Cir.Out.out_of_memory", "Cir.Out.trap", "Cir.Out.not_done", "Cir.Out",
 "Cir.is_cell", "Cir.eval.op", "Cir.eval.eqz", "Cir.eval.field.if", "Cir.eval.field", "Cir.eval.byte.of",
 "Cir.eval.byte", "Cir.eval.size", "Cir.eval.get", "Cir.eval.input", "Cir.eval", "Cir.regs.set.if", "Cir.regs.set",
 "Cir.exec.set.of", "Cir.exec.set", "Cir.exec.store.if", "Cir.exec.store", "Cir.exec.took", "Cir.room.if", "Cir.room",
 "Cir.at", "Cir.exec.bump.of", "Cir.exec.bump.if", "Cir.exec.alloc.if", "Cir.exec.alloc", "Cir.exec.emit.of",
 "Cir.exec.emit.if", "Cir.exec.emit", "Cir.exec.then", "Cir.exec.if.of", "Cir.exec.if", "Cir.exec", "Cir.l.status",
 "Cir.l.next", "Cir.l.outn", "Cir.l.tmp", "Cir.l.need", "Cir.l.addr", "Cir.l.reg", "Cir.i.get", "Cir.i.set", "Cir.i.op",
 "Cir.i.const", "Cir.code.at", "Cir.code.expr", "Cir.code.exit", "Cir.code.unless", "Cir.code.grow", "Cir.code.need",
 "Cir.code.zero", "Cir.code.alloc", "Cir.code.emit", "Cir.code.result", "Cir.code.halt", "Cir.code.stmt",
 "Cir.input.at", "Cir.alloc", "Cir.run", "Cir.pages", "Cir.word.bytes", "Cir.bytes", "Cir.module", "Cir.load",
 "Cir.ended.halt", "Cir.ended", "Cir.first", "Cir.alloc.grow", "Cir.alloc.end", "Cir.alloc.pages", "Cir.result.alloced",
 "Cir.result.sized", "Cir.result.memory", "Cir.result", "M.c", "M.g", "M.f", "M.add", "M.sub", "M.and", "M.or", "M.shl",
 "M.shr", "M.eq", "M.ne", "M.lt", "M.le", "M.gt", "M.ge", "M.not", "M.set", "M.st", "M.do", "M.if", "M.when", "M.while",
 "M.halt", "R.focus", "R.mode", "R.sp", "R.pend", "R.dx", "R.dr", "R.aq", "R.am", "R.c", "R.h", "R.tag", "R.x", "R.y",
 "R.z", "R.q", "R.n", "R.fr", "R.k", "R.p", "R.wt", "R.wenv", "R.wargs", "R.wa", "R.wx", "R.wq", "R.wn", "R.wres",
 "R.wok", "R.wb", "R.wh", "R.cs", "R.csrc", "R.cd", "R.sdep", "R.ck", "R.cnew", "R.cenv", "R.clen", "R.cj", "R.croot",
 "R.sres", "R.cm", "R.ds", "R.dok", "R.dc", "R.oc", "R.ow", "R.ov", "R.oi", "R.ii", "R.ib", "R.il", "R.iu", "R.iw",
 "R.ij", "R.ss", "R.ssrc", "R.scut", "R.sroot", "R.sk", "R.snew", "R.samt", "R.t1", "R.t2", "Mach.regs", "T.var",
 "T.ref", "T.ann", "T.let", "T.min", "T.lam", "T.app", "T.tup", "T.prj", "T.lab", "T.mat", "T.efq", "T.rfl", "T.rwt",
 "K.app_arg", "K.app_val", "K.app_fun", "K.let_in", "K.tup_b", "K.tup_a", "K.rwt", "K.min_b", "K.min_a", "K.arg",
 "K.check", "K.root", "F.value", "F.data", "F.static", "F.known", "F.owned", "F.fv_max", "I.lab", "I.nil", "I.true",
 "I.false", "I.wnil", "I.z24", "I.ref_main", "I.cache", "I.table", "I.book", "N.unit", "N.nil", "N.con", "N.u32",
 "N.wnil", "N.wcon", "N.true", "N.false", "N.q0", "N.q1", "N.q2", "N.main", "M.tag", "M.q", "M.flag", "M.fv", "M.entry",
 "M.inc", "M.dec", "M.dec.part", "M.alloc", "M.make", "M.release", "M.push", "M.pop", "M.header", "M.data", "M.pick",
 "M.max", "M.put", "M.get", "M.bump", "M.todo.bit", "M.todo", "M.todo.first", "M.todo.last", "M.fv.part", "M.finish",
 "M.if.e", "M.var", "M.copy.push", "M.copy.root", "M.copy.end", "M.copy.walk", "M.shift", "M.copy.part", "M.copy",
 "M.need", "M.release.arg", "M.release.all", "M.fld", "M.takes", "M.walk.lam", "M.walk.prj", "M.walk.mat", "M.walk.app",
 "M.walk", "M.call", "M.one", "M.redex", "M.ev.ann", "M.ev.ref", "M.ev.frame", "M.ev.app", "M.ev.let", "M.ev.tup",
 "M.ev.rwt", "M.ev.min", "M.ev", "M.swap", "M.ret.let", "M.ret.tup", "M.ret.rwt", "M.quan", "M.qmin", "M.ret.min",
 "M.pair", "M.is_lab", "M.last", "M.out.bit", "M.out.word", "M.out.con", "M.out", "M.ret", "M.h.static", "M.h.data",
 "M.input", "Mach.code", "Img.Def.arms", "Img.Def", "Img.cell", "Img.quan", "Img.size", "Img.down", "Img.fv",
 "Img.is_value", "Img.header", "Img.flags", "Img.ref.if", "Img.ref", "Img.id", "Img.term", "Img.names",
 "Img.names.defs", "Img.known", "Img.defs", "Img.bodies", "Img.labels", "Img.pair", "Img.zeros24", "Img.blank",
 "Img.table", "Img.prefix", "Img.cells", "Img.small.if", "Img.small", "Compiler.halt", "Compiler.module",
 "Compiler.compile.of", "Compiler.compile"]

def trustedCopy : List Def :=
  [«trustedCopy.Wasm.Outcome»,
   «trustedCopy.Wasm.run»,
   «trustedCopy.Compiler.compile»,
   «trustedCopy.Either.arms»,
   «trustedCopy.Either»,
   «trustedCopy.Or»,
   «trustedCopy.main»]
