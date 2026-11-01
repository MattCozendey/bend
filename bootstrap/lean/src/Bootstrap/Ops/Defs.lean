import Bootstrap.Book

-- Made by scripts/Defs.lean from the `bend -o` output of bootstrap/tests/compiler/compile.bend.
-- Do not edit it.

open Quan Term

set_option maxRecDepth 100000

def «opsDefs.Nat.double» : Def :=
  ⟨"Nat.double",
    (Term.All Quan.Q1 (Term.Ref "Nat") (Term.Ref "Nat")),
    (Term.Prj (Term.Mat "Zero" (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "Zero") (Term.Lab "()")) Term.Efq) (Term.Mat "Succ" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.double") (Term.Var 0)) (Term.Lab "()"))) (Term.Lab "()"))) Term.Efq))) Term.Efq))),
    false⟩

def «opsDefs.Word.to_nat» : Def :=
  ⟨"Word.to_nat",
    (Term.All Quan.Q1 (Term.Ref "Nat") (Term.All Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Word") (Term.Var 0)) (Term.Ref "Nat"))),
    (Term.Prj (Term.Mat "Zero" (Term.Mat "()" (Term.Lam Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "Zero") (Term.Lab "()"))) Term.Efq) (Term.Mat "Succ" (Term.Prj (Term.Lam Quan.Q2 (Term.Mat "()" (Term.Prj (Term.Mat "WCon" (Term.Prj (Term.Prj (Term.Mat "False" (Term.Mat "()" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.App Quan.Q1 (Term.Ref "Nat.double") (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Word.to_nat") (Term.Var 1)) (Term.Var 0))) Term.Efq))) Term.Efq) (Term.Mat "True" (Term.Mat "()" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.double") (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Word.to_nat") (Term.Var 1)) (Term.Var 0))) (Term.Lab "()"))) Term.Efq))) Term.Efq) Term.Efq)))) Term.Efq)) Term.Efq))) Term.Efq))),
    false⟩

def «opsDefs.U32.to_nat» : Def :=
  ⟨"U32.to_nat",
    (Term.All Quan.Q1 (Term.Ref "U32") (Term.Ref "Nat")),
    (Term.Prj (Term.Mat "U32" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Word.to_nat") (Form.nat 32)) (Term.Var 0)) Term.Efq))) Term.Efq)),
    false⟩

def «opsDefs.Bool.and» : Def :=
  ⟨"Bool.and",
    (Term.All Quan.Q1 (Term.Ref "Bool") (Term.All Quan.Q1 (Term.Ref "Bool") (Term.Ref "Bool"))),
    (Term.Prj (Term.Mat "False" (Term.Mat "()" (Term.Lam Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()"))) Term.Efq) (Term.Mat "True" (Term.Mat "()" (Term.Lam Quan.Q1 (Term.Var 0)) Term.Efq) Term.Efq))),
    false⟩

def «opsDefs.Cmp.is_eq» : Def :=
  ⟨"Cmp.is_eq",
    (Term.All Quan.Q1 (Term.Ref "Cmp") (Term.Ref "Bool")),
    (Term.Prj (Term.Mat "EQ" (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "True") (Term.Lab "()")) Term.Efq) (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")))))),
    false⟩

def «opsDefs.Bool.cmp» : Def :=
  ⟨"Bool.cmp",
    (Term.All Quan.Q1 (Term.Ref "Bool") (Term.All Quan.Q1 (Term.Ref "Bool") (Term.Ref "Cmp"))),
    (Term.Prj (Term.Mat "False" (Term.Mat "()" (Term.Prj (Term.Mat "False" (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "EQ") (Term.Lab "()")) Term.Efq) (Term.Mat "True" (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "LT") (Term.Lab "()")) Term.Efq) Term.Efq))) Term.Efq) (Term.Mat "True" (Term.Mat "()" (Term.Prj (Term.Mat "False" (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "GT") (Term.Lab "()")) Term.Efq) (Term.Mat "True" (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "EQ") (Term.Lab "()")) Term.Efq) Term.Efq))) Term.Efq) Term.Efq))),
    false⟩

def «opsDefs.Word.cmp.fin» : Def :=
  ⟨"Word.cmp.fin",
    (Term.All Quan.Q1 (Term.Ref "Bool") (Term.All Quan.Q1 (Term.Ref "Bool") (Term.All Quan.Q1 (Term.Ref "Cmp") (Term.Ref "Cmp")))),
    (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.Prj (Term.Mat "LT" (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "LT") (Term.Lab "()")) Term.Efq) (Term.Mat "EQ" (Term.Mat "()" (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Bool.cmp") (Term.Var 1)) (Term.Var 0)) Term.Efq) (Term.Mat "GT" (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "GT") (Term.Lab "()")) Term.Efq) Term.Efq)))))),
    false⟩

def «opsDefs.Word.cmp» : Def :=
  ⟨"Word.cmp",
    (Term.All Quan.Q1 (Term.Ref "Nat") (Term.All Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Word") (Term.Var 0)) (Term.All Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Word") (Term.Var 1)) (Term.Ref "Cmp")))),
    (Term.Prj (Term.Mat "Zero" (Term.Mat "()" (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "EQ") (Term.Lab "()")))) Term.Efq) (Term.Mat "Succ" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Prj (Term.Mat "WCon" (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Prj (Term.Mat "WCon" (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Word.cmp.fin") (Term.Var 3)) (Term.Var 1)) (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Word.cmp") (Term.Var 4)) (Term.Var 2)) (Term.Var 0))) Term.Efq))))) Term.Efq)) Term.Efq))))) Term.Efq)) Term.Efq))) Term.Efq))),
    false⟩

def «opsDefs.U32.cmp» : Def :=
  ⟨"U32.cmp",
    (Term.All Quan.Q1 (Term.Ref "U32") (Term.All Quan.Q1 (Term.Ref "U32") (Term.Ref "Cmp"))),
    (Term.Prj (Term.Mat "U32" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Prj (Term.Mat "U32" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Word.cmp") (Form.nat 32)) (Term.Var 1)) (Term.Var 0)) Term.Efq))) Term.Efq)) Term.Efq))) Term.Efq)),
    false⟩

def «opsDefs.U32.is_eq» : Def :=
  ⟨"U32.is_eq",
    (Term.All Quan.Q1 (Term.Ref "U32") (Term.All Quan.Q1 (Term.Ref "U32") (Term.Ref "Bool"))),
    (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Cmp.is_eq") (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "U32.cmp") (Term.Var 1)) (Term.Var 0))))),
    false⟩

def «opsDefs.Bool.or» : Def :=
  ⟨"Bool.or",
    (Term.All Quan.Q1 (Term.Ref "Bool") (Term.All Quan.Q1 (Term.Ref "Bool") (Term.Ref "Bool"))),
    (Term.Prj (Term.Mat "False" (Term.Mat "()" (Term.Lam Quan.Q1 (Term.Var 0)) Term.Efq) (Term.Mat "True" (Term.Mat "()" (Term.Lam Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "True") (Term.Lab "()"))) Term.Efq) Term.Efq))),
    false⟩

def «opsDefs.Bool.not» : Def :=
  ⟨"Bool.not",
    (Term.All Quan.Q1 (Term.Ref "Bool") (Term.Ref "Bool")),
    (Term.Prj (Term.Mat "False" (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "True") (Term.Lab "()")) Term.Efq) (Term.Mat "True" (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) Term.Efq) Term.Efq))),
    false⟩

def «opsDefs.Cmp.is_lt» : Def :=
  ⟨"Cmp.is_lt",
    (Term.All Quan.Q1 (Term.Ref "Cmp") (Term.Ref "Bool")),
    (Term.Prj (Term.Mat "LT" (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "True") (Term.Lab "()")) Term.Efq) (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")))))),
    false⟩

def «opsDefs.Word.or» : Def :=
  ⟨"Word.or",
    (Term.All Quan.Q1 (Term.Ref "Nat") (Term.All Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Word") (Term.Var 0)) (Term.All Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Word") (Term.Var 1)) (Term.App Quan.Q1 (Term.Ref "Word") (Term.Var 2))))),
    (Term.Prj (Term.Mat "Zero" (Term.Mat "()" (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WNil") (Term.Lab "()")))) Term.Efq) (Term.Mat "Succ" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Prj (Term.Mat "WCon" (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Prj (Term.Mat "WCon" (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Bool.or") (Term.Var 3)) (Term.Var 1)) (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Word.or") (Term.Var 4)) (Term.Var 2)) (Term.Var 0)) (Term.Lab "()")))) Term.Efq))))) Term.Efq)) Term.Efq))))) Term.Efq)) Term.Efq))) Term.Efq))),
    false⟩

def «opsDefs.U32.or» : Def :=
  ⟨"U32.or",
    (Term.All Quan.Q1 (Term.Ref "U32") (Term.All Quan.Q1 (Term.Ref "U32") (Term.Ref "U32"))),
    (Term.Prj (Term.Mat "U32" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Prj (Term.Mat "U32" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "U32") (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Word.or") (Form.nat 32)) (Term.Var 1)) (Term.Var 0)) (Term.Lab "()"))) Term.Efq))) Term.Efq)) Term.Efq))) Term.Efq)),
    false⟩

def «opsDefs.Word.and» : Def :=
  ⟨"Word.and",
    (Term.All Quan.Q1 (Term.Ref "Nat") (Term.All Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Word") (Term.Var 0)) (Term.All Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Word") (Term.Var 1)) (Term.App Quan.Q1 (Term.Ref "Word") (Term.Var 2))))),
    (Term.Prj (Term.Mat "Zero" (Term.Mat "()" (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WNil") (Term.Lab "()")))) Term.Efq) (Term.Mat "Succ" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Prj (Term.Mat "WCon" (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Prj (Term.Mat "WCon" (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Bool.and") (Term.Var 3)) (Term.Var 1)) (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Word.and") (Term.Var 4)) (Term.Var 2)) (Term.Var 0)) (Term.Lab "()")))) Term.Efq))))) Term.Efq)) Term.Efq))))) Term.Efq)) Term.Efq))) Term.Efq))),
    false⟩

def «opsDefs.U32.and» : Def :=
  ⟨"U32.and",
    (Term.All Quan.Q1 (Term.Ref "U32") (Term.All Quan.Q1 (Term.Ref "U32") (Term.Ref "U32"))),
    (Term.Prj (Term.Mat "U32" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Prj (Term.Mat "U32" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "U32") (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Word.and") (Form.nat 32)) (Term.Var 1)) (Term.Var 0)) (Term.Lab "()"))) Term.Efq))) Term.Efq)) Term.Efq))) Term.Efq)),
    false⟩

def «opsDefs.Word.shl.put» : Def :=
  ⟨"Word.shl.put",
    (Term.All Quan.Q1 (Term.Ref "Nat") (Term.All Quan.Q1 (Term.Ref "Bool") (Term.All Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Word") (Term.Var 1)) (Term.App Quan.Q1 (Term.Ref "Word") (Term.Var 2))))),
    (Term.Prj (Term.Mat "Zero" (Term.Mat "()" (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WNil") (Term.Lab "()")))) Term.Efq) (Term.Mat "Succ" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Lam Quan.Q1 (Term.Prj (Term.Mat "WCon" (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Var 2) (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Word.shl.put") (Term.Var 3)) (Term.Var 1)) (Term.Var 0)) (Term.Lab "()")))) Term.Efq))))) Term.Efq))) Term.Efq))) Term.Efq))),
    false⟩

def «opsDefs.Word.shl» : Def :=
  ⟨"Word.shl",
    (Term.All Quan.Q1 (Term.Ref "Nat") (Term.All Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Word") (Term.Var 0)) (Term.App Quan.Q1 (Term.Ref "Word") (Term.Var 1)))),
    (Term.Prj (Term.Mat "Zero" (Term.Mat "()" (Term.Lam Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WNil") (Term.Lab "()"))) Term.Efq) (Term.Mat "Succ" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Prj (Term.Mat "WCon" (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Word.shl.put") (Term.Var 2)) (Term.Var 1)) (Term.Var 0)) (Term.Lab "()")))) Term.Efq))))) Term.Efq)) Term.Efq))) Term.Efq))),
    false⟩

def «opsDefs.U32.shl» : Def :=
  ⟨"U32.shl",
    (Term.All Quan.Q1 (Term.Ref "U32") (Term.Ref "U32")),
    (Term.Prj (Term.Mat "U32" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "U32") (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Word.shl") (Form.nat 32)) (Term.Var 0)) (Term.Lab "()"))) Term.Efq))) Term.Efq)),
    false⟩

def «opsDefs.U32.shln» : Def :=
  ⟨"U32.shln",
    (Term.All Quan.Q1 (Term.Ref "U32") (Term.All Quan.Q1 (Term.Ref "Nat") (Term.Ref "U32"))),
    (Term.Lam Quan.Q2 (Term.Prj (Term.Mat "Zero" (Term.Mat "()" (Term.Var 0) Term.Efq) (Term.Mat "Succ" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.App Quan.Q1 (Term.Ref "U32.shl") (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "U32.shln") (Term.Var 1)) (Term.Var 0))) Term.Efq))) Term.Efq)))),
    false⟩

def «opsDefs.U32.is_lt» : Def :=
  ⟨"U32.is_lt",
    (Term.All Quan.Q1 (Term.Ref "U32") (Term.All Quan.Q1 (Term.Ref "U32") (Term.Ref "Bool"))),
    (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Cmp.is_lt") (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "U32.cmp") (Term.Var 1)) (Term.Var 0))))),
    false⟩

def «opsDefs.Cmp.is_ge» : Def :=
  ⟨"Cmp.is_ge",
    (Term.All Quan.Q1 (Term.Ref "Cmp") (Term.Ref "Bool")),
    (Term.Prj (Term.Mat "LT" (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) Term.Efq) (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "True") (Term.Lab "()")))))),
    false⟩

def «opsDefs.U32.is_ge» : Def :=
  ⟨"U32.is_ge",
    (Term.All Quan.Q1 (Term.Ref "U32") (Term.All Quan.Q1 (Term.Ref "U32") (Term.Ref "Bool"))),
    (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Cmp.is_ge") (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "U32.cmp") (Term.Var 1)) (Term.Var 0))))),
    false⟩

def «opsDefs.Bool.xor» : Def :=
  ⟨"Bool.xor",
    (Term.All Quan.Q1 (Term.Ref "Bool") (Term.All Quan.Q1 (Term.Ref "Bool") (Term.Ref "Bool"))),
    (Term.Prj (Term.Mat "False" (Term.Mat "()" (Term.Lam Quan.Q1 (Term.Var 0)) Term.Efq) (Term.Mat "True" (Term.Mat "()" (Term.Lam Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Bool.not") (Term.Var 0))) Term.Efq) Term.Efq))),
    false⟩

def «opsDefs.Bool.full_add» : Def :=
  ⟨"Bool.full_add",
    (Term.All Quan.Q1 (Term.Ref "Bool") (Term.All Quan.Q2 (Term.Ref "Bool") (Term.All Quan.Q2 (Term.Ref "Bool") (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "Pair") (Term.Ref "Bool")) (Term.Ref "Bool"))))),
    (Term.Prj (Term.Mat "False" (Term.Mat "()" (Term.Lam Quan.Q2 (Term.Lam Quan.Q2 (Term.Tup Quan.Q1 (Term.Lab "Tuple") (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Bool.xor") (Term.Var 1)) (Term.Var 0)) (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Bool.and") (Term.Var 1)) (Term.Var 0)) (Term.Lab "()")))))) Term.Efq) (Term.Mat "True" (Term.Mat "()" (Term.Lam Quan.Q2 (Term.Lam Quan.Q2 (Term.Tup Quan.Q1 (Term.Lab "Tuple") (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Bool.not") (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Bool.xor") (Term.Var 1)) (Term.Var 0))) (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Bool.or") (Term.Var 1)) (Term.Var 0)) (Term.Lab "()")))))) Term.Efq) Term.Efq))),
    false⟩

def «opsDefs.Word.adc.group» : Def :=
  ⟨"Word.adc.group",
    (Term.All Quan.Q1 (Term.Ref "Nat") (Term.All Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Word") (Term.Var 0)) (Term.All Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Word") (Term.Var 1)) (Term.All Quan.Q1 (Term.Ref "Bool") (Term.All Quan.Q1 (Term.Sig Quan.Q1 (Term.Enu ["Word.adc", "Word.adc.con"]) (Term.App Quan.Q1 (Term.Mat "Word.adc" (Term.Enu ["()"]) (Term.Mat "Word.adc.con" (Term.Sig Quan.Q1 (Term.Sig Quan.Q1 (Term.Enu ["Word.adc"]) (Term.Enu ["()"])) (Term.Enu ["()"])) Term.Efq)) (Term.Var 0))) (Term.App Quan.Q1 (Term.Prj (Term.Mat "Word.adc" (Term.Mat "()" (Term.All Quan.Q1 (Term.Ref "Bool") (Term.App Quan.Q1 (Term.Ref "Word") (Term.Var 5))) Term.Efq) (Term.Mat "Word.adc.con" (Term.Prj (Term.Prj (Term.Mat "Word.adc" (Term.Mat "()" (Term.Mat "()" (Term.All Quan.Q1 (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "Pair") (Term.Ref "Bool")) (Term.Ref "Bool")) (Term.App Quan.Q1 (Term.Ref "Word") (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.Var 5) (Term.Lab "()"))))) Term.Efq) Term.Efq) Term.Efq))) Term.Efq))) (Term.Var 0))))))),
    (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Prj (Term.Mat "Word.adc" (Term.Mat "()" (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Prj (Term.Mat "Zero" (Term.Mat "()" (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WNil") (Term.Lab "()")))))) Term.Efq) (Term.Mat "Succ" (Term.Prj (Term.Lam Quan.Q2 (Term.Mat "()" (Term.Prj (Term.Mat "WCon" (Term.Prj (Term.Lam Quan.Q2 (Term.Prj (Term.Lam Quan.Q2 (Term.Mat "()" (Term.Prj (Term.Mat "WCon" (Term.Prj (Term.Lam Quan.Q2 (Term.Prj (Term.Lam Quan.Q2 (Term.Mat "()" (Term.Prj (Term.Mat "False" (Term.Mat "()" (Term.Lam Quan.Q1 (Term.Ann (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Word.adc.group") (Term.Var 5)) (Term.Var 3)) (Term.Var 1)) (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()"))) (Term.Tup Quan.Q1 (Term.Lab "Word.adc.con") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "Word.adc") (Term.Lab "()")) (Term.Lab "()")))) (Term.App Quan.Q2 (Term.App Quan.Q2 (Term.App Quan.Q1 (Term.Ref "Bool.full_add") (Term.Var 4)) (Term.Var 2)) (Term.Var 0))) (Term.App Quan.Q1 (Term.Ref "Word") (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.Var 5) (Term.Lab "()")))))) Term.Efq) (Term.Mat "True" (Term.Mat "()" (Term.Lam Quan.Q1 (Term.Ann (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Word.adc.group") (Term.Var 5)) (Term.Var 3)) (Term.Var 1)) (Term.Tup Quan.Q1 (Term.Lab "True") (Term.Lab "()"))) (Term.Tup Quan.Q1 (Term.Lab "Word.adc.con") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "Word.adc") (Term.Lab "()")) (Term.Lab "()")))) (Term.App Quan.Q2 (Term.App Quan.Q2 (Term.App Quan.Q1 (Term.Ref "Bool.full_add") (Term.Var 4)) (Term.App Quan.Q1 (Term.Ref "Bool.not") (Term.Var 2))) (Term.Var 0))) (Term.App Quan.Q1 (Term.Ref "Word") (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.Var 5) (Term.Lab "()")))))) Term.Efq) Term.Efq))) Term.Efq))))) Term.Efq)) Term.Efq))))) Term.Efq)) Term.Efq))) Term.Efq))) (Term.Var 4)) (Term.Var 3)) (Term.Var 2)) (Term.Var 1)) (Term.Var 0))))))) Term.Efq) (Term.Mat "Word.adc.con" (Term.Prj (Term.Prj (Term.Mat "Word.adc" (Term.Mat "()" (Term.Mat "()" (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.App Quan.Q1 (Term.Prj (Term.Mat "Tuple" (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Var 1) (Term.Tup Quan.Q1 (Term.Ann (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Word.adc.group") (Term.Var 6)) (Term.Var 5)) (Term.Var 4)) (Term.Var 3)) (Term.Tup Quan.Q1 (Term.Lab "Word.adc") (Term.Lab "()"))) (Term.Var 0)) (Term.App Quan.Q1 (Term.Ref "Word") (Term.Var 6))) (Term.Lab "()")))) Term.Efq))))) Term.Efq)) (Term.Var 0))))))) Term.Efq) Term.Efq) Term.Efq))) Term.Efq))) (Term.Var 0)) (Term.Var 4)) (Term.Var 3)) (Term.Var 2)) (Term.Var 1))))))),
    false⟩

def «opsDefs.Word.sub» : Def :=
  ⟨"Word.sub",
    (Term.All Quan.Q1 (Term.Ref "Nat") (Term.All Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Word") (Term.Var 0)) (Term.All Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Word") (Term.Var 1)) (Term.App Quan.Q1 (Term.Ref "Word") (Term.Var 2))))),
    (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.Ann (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Word.adc.group") (Term.Var 2)) (Term.Var 1)) (Term.Var 0)) (Term.Tup Quan.Q1 (Term.Lab "True") (Term.Lab "()"))) (Term.Tup Quan.Q1 (Term.Lab "Word.adc") (Term.Lab "()"))) (Term.Tup Quan.Q1 (Term.Lab "True") (Term.Lab "()"))) (Term.App Quan.Q1 (Term.Ref "Word") (Term.Var 2)))))),
    false⟩

def «opsDefs.U32.sub» : Def :=
  ⟨"U32.sub",
    (Term.All Quan.Q1 (Term.Ref "U32") (Term.All Quan.Q1 (Term.Ref "U32") (Term.Ref "U32"))),
    (Term.Prj (Term.Mat "U32" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Prj (Term.Mat "U32" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "U32") (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Word.sub") (Form.nat 32)) (Term.Var 1)) (Term.Var 0)) (Term.Lab "()"))) Term.Efq))) Term.Efq)) Term.Efq))) Term.Efq)),
    false⟩

def «opsDefs.Word.inc» : Def :=
  ⟨"Word.inc",
    (Term.All Quan.Q1 (Term.Ref "Nat") (Term.All Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Word") (Term.Var 0)) (Term.App Quan.Q1 (Term.Ref "Word") (Term.Var 1)))),
    (Term.Prj (Term.Mat "Zero" (Term.Mat "()" (Term.Lam Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WNil") (Term.Lab "()"))) Term.Efq) (Term.Mat "Succ" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Prj (Term.Mat "WCon" (Term.Prj (Term.Prj (Term.Mat "False" (Term.Mat "()" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "True") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Var 0) (Term.Lab "()")))) Term.Efq))) Term.Efq) (Term.Mat "True" (Term.Mat "()" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Word.inc") (Term.Var 1)) (Term.Var 0)) (Term.Lab "()")))) Term.Efq))) Term.Efq) Term.Efq)))) Term.Efq)) Term.Efq))) Term.Efq))),
    false⟩

def «opsDefs.U32.inc» : Def :=
  ⟨"U32.inc",
    (Term.All Quan.Q1 (Term.Ref "U32") (Term.Ref "U32")),
    (Term.Prj (Term.Mat "U32" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "U32") (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Word.inc") (Form.nat 32)) (Term.Var 0)) (Term.Lab "()"))) Term.Efq))) Term.Efq)),
    false⟩

def «opsDefs.U32.lit0» : Def :=
  ⟨"U32.lit0",
    (Term.Ref "U32"),
    (Term.Tup Quan.Q1 (Term.Lab "U32") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WNil") (Term.Lab "()")) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()"))),
    false⟩

def «opsDefs.U32.is_zero» : Def :=
  ⟨"U32.is_zero",
    (Term.All Quan.Q1 (Term.Ref "U32") (Term.Ref "Bool")),
    (Term.Lam Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "U32.is_eq") (Term.Var 0)) (Term.Ref "U32.lit0"))),
    false⟩

def «opsDefs.Cmp.is_le» : Def :=
  ⟨"Cmp.is_le",
    (Term.All Quan.Q1 (Term.Ref "Cmp") (Term.Ref "Bool")),
    (Term.Prj (Term.Mat "GT" (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) Term.Efq) (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "True") (Term.Lab "()")))))),
    false⟩

def «opsDefs.U32.is_le» : Def :=
  ⟨"U32.is_le",
    (Term.All Quan.Q1 (Term.Ref "U32") (Term.All Quan.Q1 (Term.Ref "U32") (Term.Ref "Bool"))),
    (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Cmp.is_le") (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "U32.cmp") (Term.Var 1)) (Term.Var 0))))),
    false⟩

def «opsDefs.Word.add» : Def :=
  ⟨"Word.add",
    (Term.All Quan.Q1 (Term.Ref "Nat") (Term.All Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Word") (Term.Var 0)) (Term.All Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Word") (Term.Var 1)) (Term.App Quan.Q1 (Term.Ref "Word") (Term.Var 2))))),
    (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.Ann (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Word.adc.group") (Term.Var 2)) (Term.Var 1)) (Term.Var 0)) (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()"))) (Term.Tup Quan.Q1 (Term.Lab "Word.adc") (Term.Lab "()"))) (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()"))) (Term.App Quan.Q1 (Term.Ref "Word") (Term.Var 2)))))),
    false⟩

def «opsDefs.U32.add» : Def :=
  ⟨"U32.add",
    (Term.All Quan.Q1 (Term.Ref "U32") (Term.All Quan.Q1 (Term.Ref "U32") (Term.Ref "U32"))),
    (Term.Prj (Term.Mat "U32" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Prj (Term.Mat "U32" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "U32") (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Word.add") (Form.nat 32)) (Term.Var 1)) (Term.Var 0)) (Term.Lab "()"))) Term.Efq))) Term.Efq)) Term.Efq))) Term.Efq)),
    false⟩

def «opsDefs.Cmp.is_gt» : Def :=
  ⟨"Cmp.is_gt",
    (Term.All Quan.Q1 (Term.Ref "Cmp") (Term.Ref "Bool")),
    (Term.Prj (Term.Mat "GT" (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "True") (Term.Lab "()")) Term.Efq) (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")))))),
    false⟩

def «opsDefs.U32.is_gt» : Def :=
  ⟨"U32.is_gt",
    (Term.All Quan.Q1 (Term.Ref "U32") (Term.All Quan.Q1 (Term.Ref "U32") (Term.Ref "Bool"))),
    (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Cmp.is_gt") (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "U32.cmp") (Term.Var 1)) (Term.Var 0))))),
    false⟩

def «opsDefs.U32.from_nat» : Def :=
  ⟨"U32.from_nat",
    (Term.All Quan.Q1 (Term.Ref "Nat") (Term.Ref "U32")),
    (Term.Prj (Term.Mat "Zero" (Term.Mat "()" (Term.Ref "U32.lit0") Term.Efq) (Term.Mat "Succ" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.App Quan.Q1 (Term.Ref "U32.inc") (Term.App Quan.Q1 (Term.Ref "U32.from_nat") (Term.Var 0))) Term.Efq))) Term.Efq))),
    false⟩

def «opsDefs.Word.shr.pad» : Def :=
  ⟨"Word.shr.pad",
    (Term.All Quan.Q1 (Term.Ref "Nat") (Term.All Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Word") (Term.Var 0)) (Term.App Quan.Q1 (Term.Ref "Word") (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.Var 1) (Term.Lab "()")))))),
    (Term.Prj (Term.Mat "Zero" (Term.Mat "()" (Term.Lam Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Var 0) (Term.Lab "()"))))) Term.Efq) (Term.Mat "Succ" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Prj (Term.Mat "WCon" (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Var 1) (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Word.shr.pad") (Term.Var 2)) (Term.Var 0)) (Term.Lab "()")))) Term.Efq))))) Term.Efq)) Term.Efq))) Term.Efq))),
    false⟩

def «opsDefs.Word.shr» : Def :=
  ⟨"Word.shr",
    (Term.All Quan.Q1 (Term.Ref "Nat") (Term.All Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Word") (Term.Var 0)) (Term.App Quan.Q1 (Term.Ref "Word") (Term.Var 1)))),
    (Term.Prj (Term.Mat "Zero" (Term.Mat "()" (Term.Lam Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WNil") (Term.Lab "()"))) Term.Efq) (Term.Mat "Succ" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Prj (Term.Mat "WCon" (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Word.shr.pad") (Term.Var 2)) (Term.Var 0)) Term.Efq))))) Term.Efq)) Term.Efq))) Term.Efq))),
    false⟩

def «opsDefs.U32.shr» : Def :=
  ⟨"U32.shr",
    (Term.All Quan.Q1 (Term.Ref "U32") (Term.Ref "U32")),
    (Term.Prj (Term.Mat "U32" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "U32") (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Word.shr") (Form.nat 32)) (Term.Var 0)) (Term.Lab "()"))) Term.Efq))) Term.Efq)),
    false⟩

def «opsDefs.U32.shrn» : Def :=
  ⟨"U32.shrn",
    (Term.All Quan.Q1 (Term.Ref "U32") (Term.All Quan.Q1 (Term.Ref "Nat") (Term.Ref "U32"))),
    (Term.Lam Quan.Q2 (Term.Prj (Term.Mat "Zero" (Term.Mat "()" (Term.Var 0) Term.Efq) (Term.Mat "Succ" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.App Quan.Q1 (Term.Ref "U32.shr") (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "U32.shrn") (Term.Var 1)) (Term.Var 0))) Term.Efq))) Term.Efq)))),
    false⟩

def «opsDefs.U32.is_ne» : Def :=
  ⟨"U32.is_ne",
    (Term.All Quan.Q1 (Term.Ref "U32") (Term.All Quan.Q1 (Term.Ref "U32") (Term.Ref "Bool"))),
    (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Bool.not") (Term.App Quan.Q1 (Term.Ref "Cmp.is_eq") (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "U32.cmp") (Term.Var 1)) (Term.Var 0)))))),
    false⟩

def opsDefs : List Def :=
  [«opsDefs.Nat.double»,
   «opsDefs.Word.to_nat»,
   «opsDefs.U32.to_nat»,
   «opsDefs.Bool.and»,
   «opsDefs.Cmp.is_eq»,
   «opsDefs.Bool.cmp»,
   «opsDefs.Word.cmp.fin»,
   «opsDefs.Word.cmp»,
   «opsDefs.U32.cmp»,
   «opsDefs.U32.is_eq»,
   «opsDefs.Bool.or»,
   «opsDefs.Bool.not»,
   «opsDefs.Cmp.is_lt»,
   «opsDefs.Word.or»,
   «opsDefs.U32.or»,
   «opsDefs.Word.and»,
   «opsDefs.U32.and»,
   «opsDefs.Word.shl.put»,
   «opsDefs.Word.shl»,
   «opsDefs.U32.shl»,
   «opsDefs.U32.shln»,
   «opsDefs.U32.is_lt»,
   «opsDefs.Cmp.is_ge»,
   «opsDefs.U32.is_ge»,
   «opsDefs.Bool.xor»,
   «opsDefs.Bool.full_add»,
   «opsDefs.Word.adc.group»,
   «opsDefs.Word.sub»,
   «opsDefs.U32.sub»,
   «opsDefs.Word.inc»,
   «opsDefs.U32.inc»,
   «opsDefs.U32.lit0»,
   «opsDefs.U32.is_zero»,
   «opsDefs.Cmp.is_le»,
   «opsDefs.U32.is_le»,
   «opsDefs.Word.add»,
   «opsDefs.U32.add»,
   «opsDefs.Cmp.is_gt»,
   «opsDefs.U32.is_gt»,
   «opsDefs.U32.from_nat»,
   «opsDefs.Word.shr.pad»,
   «opsDefs.Word.shr»,
   «opsDefs.U32.shr»,
   «opsDefs.U32.shrn»,
   «opsDefs.U32.is_ne»]
