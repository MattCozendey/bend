import Bootstrap.Book

-- Made by scripts/Defs.lean from the `bend -o` output of bootstrap/bend/src/compiler/impl.bend.
-- Do not edit it.

open Quan Term

set_option maxRecDepth 100000

def «needCopy.List.length» : Def :=
  ⟨"List.length",
    (Term.All Quan.Q0 (Term.Enu ["Q0", "Q1", "Q2"]) (Term.All Quan.Q0 (Term.Typ (Term.Var 0)) (Term.All Quan.Q1 (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "List") (Term.Var 1)) (Term.Var 0)) (Term.Ref "Nat")))),
    (Term.Lam Quan.Q0 (Term.Lam Quan.Q0 (Term.Prj (Term.Mat "Nil" (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "Zero") (Term.Lab "()")) Term.Efq) (Term.Mat "Con" (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "List.length") (Term.Var 3)) (Term.Var 2)) (Term.Var 0)) (Term.Lab "()"))) Term.Efq))))) Term.Efq))))),
    false⟩

def «needCopy.Cmp.is_le» : Def :=
  ⟨"Cmp.is_le",
    (Term.All Quan.Q1 (Term.Ref "Cmp") (Term.Ref "Bool")),
    (Term.Prj (Term.Mat "GT" (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) Term.Efq) (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "True") (Term.Lab "()")))))),
    false⟩

def «needCopy.U32.is_le» : Def :=
  ⟨"U32.is_le",
    (Term.All Quan.Q1 (Term.Ref "U32") (Term.All Quan.Q1 (Term.Ref "U32") (Term.Ref "Bool"))),
    (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Cmp.is_le") (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "U32.cmp") (Term.Var 1)) (Term.Var 0))))),
    false⟩

def «needCopy.U32.lit65536» : Def :=
  ⟨"U32.lit65536",
    (Term.Ref "U32"),
    (Term.Tup Quan.Q1 (Term.Lab "U32") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "True") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WNil") (Term.Lab "()")) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()"))),
    false⟩

def «needCopy.Wasm.min.if» : Def :=
  ⟨"Wasm.min.if",
    (Term.All Quan.Q1 (Term.Ref "Bool") (Term.All Quan.Q1 (Term.Ref "U32") (Term.All Quan.Q1 (Term.Ref "U32") (Term.Ref "U32")))),
    (Term.Prj (Term.Mat "True" (Term.Mat "()" (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.Var 1))) Term.Efq) (Term.Mat "False" (Term.Mat "()" (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.Var 0))) Term.Efq) Term.Efq))),
    false⟩

def «needCopy.Wasm.min» : Def :=
  ⟨"Wasm.min",
    (Term.All Quan.Q2 (Term.Ref "U32") (Term.All Quan.Q2 (Term.Ref "U32") (Term.Ref "U32"))),
    (Term.Lam Quan.Q2 (Term.Lam Quan.Q2 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Wasm.min.if") (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "U32.is_le") (Term.Var 1)) (Term.Var 0))) (Term.Var 1)) (Term.Var 0)))),
    false⟩

def «needCopy.Term.size» : Def :=
  ⟨"Term.size",
    (Term.All Quan.Q1 (Term.Ref "Term") (Term.Ref "Nat")),
    (Term.Prj (Term.Mat "Term.Var" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "Zero") (Term.Lab "()")) (Term.Lab "()"))) Term.Efq))) (Term.Mat "Term.Ref" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "Zero") (Term.Lab "()")) (Term.Lab "()"))) Term.Efq))) (Term.Mat "Term.Ann" (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.add") (Term.App Quan.Q1 (Term.Ref "Term.size") (Term.Var 1))) (Term.App Quan.Q1 (Term.Ref "Term.size") (Term.Var 0))) (Term.Lab "()"))) Term.Efq))))) (Term.Mat "Term.Let" (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.add") (Term.App Quan.Q1 (Term.Ref "Term.size") (Term.Var 1))) (Term.App Quan.Q1 (Term.Ref "Term.size") (Term.Var 0))) (Term.Lab "()"))) Term.Efq))))))) (Term.Mat "Term.Typ" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Term.size") (Term.Var 0)) (Term.Lab "()"))) Term.Efq))) (Term.Mat "Term.Min" (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.add") (Term.App Quan.Q1 (Term.Ref "Term.size") (Term.Var 1))) (Term.App Quan.Q1 (Term.Ref "Term.size") (Term.Var 0))) (Term.Lab "()"))) Term.Efq))))) (Term.Mat "Term.All" (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.add") (Term.App Quan.Q1 (Term.Ref "Term.size") (Term.Var 1))) (Term.App Quan.Q1 (Term.Ref "Term.size") (Term.Var 0))) (Term.Lab "()"))) Term.Efq))))))) (Term.Mat "Term.Lam" (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Term.size") (Term.Var 0)) (Term.Lab "()"))) Term.Efq))))) (Term.Mat "Term.App" (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.add") (Term.App Quan.Q1 (Term.Ref "Term.size") (Term.Var 1))) (Term.App Quan.Q1 (Term.Ref "Term.size") (Term.Var 0))) (Term.Lab "()"))) Term.Efq))))))) (Term.Mat "Term.Sig" (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.add") (Term.App Quan.Q1 (Term.Ref "Term.size") (Term.Var 1))) (Term.App Quan.Q1 (Term.Ref "Term.size") (Term.Var 0))) (Term.Lab "()"))) Term.Efq))))))) (Term.Mat "Term.Tup" (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.add") (Term.App Quan.Q1 (Term.Ref "Term.size") (Term.Var 1))) (Term.App Quan.Q1 (Term.Ref "Term.size") (Term.Var 0))) (Term.Lab "()"))) Term.Efq))))))) (Term.Mat "Term.Prj" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Term.size") (Term.Var 0)) (Term.Lab "()"))) Term.Efq))) (Term.Mat "Term.Enu" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "Zero") (Term.Lab "()")) (Term.Lab "()"))) Term.Efq))) (Term.Mat "Term.Lab" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "Zero") (Term.Lab "()")) (Term.Lab "()"))) Term.Efq))) (Term.Mat "Term.Mat" (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.add") (Term.App Quan.Q1 (Term.Ref "Term.size") (Term.Var 1))) (Term.App Quan.Q1 (Term.Ref "Term.size") (Term.Var 0))) (Term.Lab "()"))) Term.Efq))))))) (Term.Mat "Term.Efq" (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "Zero") (Term.Lab "()")) (Term.Lab "()"))) Term.Efq) (Term.Mat "Term.Eql" (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.add") (Term.App Quan.Q1 (Term.Ref "Term.size") (Term.Var 2))) (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.add") (Term.App Quan.Q1 (Term.Ref "Term.size") (Term.Var 1))) (Term.App Quan.Q1 (Term.Ref "Term.size") (Term.Var 0)))) (Term.Lab "()"))) Term.Efq))))))) (Term.Mat "Term.Rfl" (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "Zero") (Term.Lab "()")) (Term.Lab "()"))) Term.Efq) (Term.Mat "Term.Rwt" (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.add") (Term.App Quan.Q1 (Term.Ref "Term.size") (Term.Var 2))) (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.add") (Term.App Quan.Q1 (Term.Ref "Term.size") (Term.Var 1))) (Term.App Quan.Q1 (Term.Ref "Term.size") (Term.Var 0)))) (Term.Lab "()"))) Term.Efq))))))) Term.Efq)))))))))))))))))))),
    false⟩

def «needCopy.Program.largest.next» : Def :=
  ⟨"Program.largest.next",
    (Term.All Quan.Q1 (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "Maybe") (Term.Lab "Q1")) (Term.Ref "Term")) (Term.All Quan.Q1 (Term.All Quan.Q1 (Term.Ref "Term") (Term.Ref "Nat")) (Term.Ref "Nat"))),
    (Term.Prj (Term.Mat "None" (Term.Mat "()" (Term.Lam Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "Zero") (Term.Lab "()"))) Term.Efq) (Term.Mat "Some" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Lam Quan.Q1 (Term.App Quan.Q1 (Term.Var 0) (Term.Var 1))) Term.Efq))) Term.Efq))),
    false⟩

def «needCopy.Nat.max» : Def :=
  ⟨"Nat.max",
    (Term.All Quan.Q2 (Term.Ref "Nat") (Term.All Quan.Q2 (Term.Ref "Nat") (Term.Ref "Nat"))),
    (Term.Prj (Term.Mat "Zero" (Term.Mat "()" (Term.Lam Quan.Q2 (Term.Var 0)) Term.Efq) (Term.Mat "Succ" (Term.Prj (Term.Lam Quan.Q2 (Term.Mat "()" (Term.Prj (Term.Mat "Zero" (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.Var 0) (Term.Lab "()"))) Term.Efq) (Term.Mat "Succ" (Term.Prj (Term.Lam Quan.Q2 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.App Quan.Q2 (Term.App Quan.Q2 (Term.Ref "Nat.max") (Term.Var 1)) (Term.Var 0)) (Term.Lab "()"))) Term.Efq))) Term.Efq))) Term.Efq))) Term.Efq))),
    false⟩

def «needCopy.Program.largest.go» : Def :=
  ⟨"Program.largest.go",
    (Term.All Quan.Q1 (Term.Ref "Nat") (Term.All Quan.Q2 (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "Def")) (Term.All Quan.Q2 (Term.Ref "Term") (Term.Ref "Nat")))),
    (Term.Prj (Term.Mat "Zero" (Term.Mat "()" (Term.Lam Quan.Q2 (Term.Lam Quan.Q2 (Term.App Quan.Q1 (Term.Ref "Term.size") (Term.Var 0)))) Term.Efq) (Term.Mat "Succ" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Lam Quan.Q2 (Term.Lam Quan.Q2 (Term.App Quan.Q2 (Term.App Quan.Q2 (Term.Ref "Nat.max") (Term.App Quan.Q1 (Term.Ref "Term.size") (Term.Var 0))) (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Program.largest.next") (Term.App Quan.Q2 (Term.App Quan.Q2 (Term.Ref "Eval.step") (Term.Var 1)) (Term.Var 0))) (Term.Lam Quan.Q1 (Term.App Quan.Q2 (Term.App Quan.Q2 (Term.App Quan.Q1 (Term.Ref "Program.largest.go") (Term.Var 3)) (Term.Var 2)) (Term.Var 0))))))) Term.Efq))) Term.Efq))),
    false⟩

def «needCopy.Program.largest.of» : Def :=
  ⟨"Program.largest.of",
    (Term.All Quan.Q1 (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "Maybe") (Term.Lab "Q1")) (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "Def"))) (Term.All Quan.Q1 (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "U32")) (Term.All Quan.Q1 (Term.Ref "Nat") (Term.Ref "Nat")))),
    (Term.Prj (Term.Mat "None" (Term.Mat "()" (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "Zero") (Term.Lab "()")))) Term.Efq) (Term.Mat "Some" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.App Quan.Q2 (Term.App Quan.Q2 (Term.App Quan.Q1 (Term.Ref "Program.largest.go") (Term.Var 0)) (Term.Var 2)) (Term.App Quan.Q1 (Term.Ref "Program.start") (Term.Var 1))))) Term.Efq))) Term.Efq))),
    false⟩

def «needCopy.Program.largest» : Def :=
  ⟨"Program.largest",
    (Term.All Quan.Q1 (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "U32")) (Term.All Quan.Q1 (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "U32")) (Term.All Quan.Q1 (Term.Ref "Nat") (Term.Ref "Nat")))),
    (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Program.largest.of") (Term.App Quan.Q1 (Term.Ref "Book.read") (Term.Var 2))) (Term.Var 1)) (Term.Var 0))))),
    false⟩

def «needCopy.Nat.mul» : Def :=
  ⟨"Nat.mul",
    (Term.All Quan.Q1 (Term.Ref "Nat") (Term.All Quan.Q2 (Term.Ref "Nat") (Term.Ref "Nat"))),
    (Term.Prj (Term.Mat "Zero" (Term.Mat "()" (Term.Lam Quan.Q2 (Term.Tup Quan.Q1 (Term.Lab "Zero") (Term.Lab "()"))) Term.Efq) (Term.Mat "Succ" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Lam Quan.Q2 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.add") (Term.Var 0)) (Term.App Quan.Q2 (Term.App Quan.Q1 (Term.Ref "Nat.mul") (Term.Var 1)) (Term.Var 0)))) Term.Efq))) Term.Efq))),
    false⟩

def «needCopy.Program.need» : Def :=
  ⟨"Program.need",
    (Term.All Quan.Q2 (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "U32")) (Term.All Quan.Q1 (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "U32")) (Term.All Quan.Q1 (Term.Ref "Nat") (Term.Ref "Nat")))),
    (Term.Lam Quan.Q2 (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.add") (Term.App Quan.Q2 (Term.App Quan.Q1 (Term.Ref "Nat.mul") (Form.nat 64)) (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.add") (Term.App Quan.Q1 (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "List.length") (Term.Lab "Q2")) (Term.Ref "U32")) (Term.Var 2))) (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Program.largest") (Term.Var 2)) (Term.Var 1)) (Term.Var 0))))) (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.add") (Term.App Quan.Q2 (Term.App Quan.Q1 (Term.Ref "Nat.mul") (Form.nat 4096)) (Form.nat 4096))) (Term.Tup Quan.Q1 (Term.Lab "Zero") (Term.Lab "()"))))))),
    false⟩

def «needCopy.Program.memory» : Def :=
  ⟨"Program.memory",
    (Term.All Quan.Q1 (Term.Ref "U32") (Term.Ref "Nat")),
    (Term.Lam Quan.Q1 (Term.App Quan.Q2 (Term.App Quan.Q1 (Term.Ref "Nat.mul") (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.add") (Term.App Quan.Q2 (Term.App Quan.Q1 (Term.Ref "Nat.mul") (Form.nat 16)) (Form.nat 4096))) (Term.Tup Quan.Q1 (Term.Lab "Zero") (Term.Lab "()")))) (Term.App Quan.Q1 (Term.Ref "U32.to_nat") (Term.App Quan.Q2 (Term.App Quan.Q2 (Term.Ref "Wasm.min") (Term.Var 0)) (Term.Ref "U32.lit65536"))))),
    false⟩

def needCopy : List Def :=
  [«needCopy.List.length»,
   «needCopy.Cmp.is_le»,
   «needCopy.U32.is_le»,
   «needCopy.U32.lit65536»,
   «needCopy.Wasm.min.if»,
   «needCopy.Wasm.min»,
   «needCopy.Term.size»,
   «needCopy.Program.largest.next»,
   «needCopy.Nat.max»,
   «needCopy.Program.largest.go»,
   «needCopy.Program.largest.of»,
   «needCopy.Program.largest»,
   «needCopy.Nat.mul»,
   «needCopy.Program.need»,
   «needCopy.Program.memory»]
