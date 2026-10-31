import bendtt

-- Made by scripts/Copy.lean from the `bend -o` output of bootstrap/bend/src/book/impl.bend,
-- for the roots Book.read, and the defs that they need. Do not edit it.

open Quan Term

def «reader.Quan.arms» : Def :=
  ⟨"Quan.arms",
    Term.All (Quan.Q1) (Term.Enu ["Quan.Q0", "Quan.Q1", "Quan.Q2"]) (Term.Typ (Term.Lab "Q2")),
    Term.Mat
      "Quan.Q0"
      (Term.Enu ["()"])
      (Term.Mat "Quan.Q1" (Term.Enu ["()"]) (Term.Mat "Quan.Q2" (Term.Enu ["()"]) (Term.Efq))),
    false⟩

def «reader.Quan» : Def :=
  ⟨"Quan",
    Term.Typ (Term.Lab "Q2"),
    Term.Sig
      (Quan.Q1)
      (Term.Enu ["Quan.Q0", "Quan.Q1", "Quan.Q2"])
      (Term.App (Quan.Q1) (Term.Ref "Quan.arms") (Term.Var 0)),
    false⟩

def «reader.Term.arms» : Def :=
  ⟨"Term.arms",
    Term.All
      (Quan.Q1)
      (Term.Enu
        ["Term.Var", "Term.Ref", "Term.Ann", "Term.Let", "Term.Typ", "Term.Min", "Term.All",
         "Term.Lam", "Term.App", "Term.Sig", "Term.Tup", "Term.Prj", "Term.Enu", "Term.Lab",
         "Term.Mat", "Term.Efq", "Term.Eql", "Term.Rfl", "Term.Rwt"])
      (Term.Typ (Term.Lab "Q2")),
    Term.Mat
      "Term.Var"
      (Term.Sig (Quan.Q1) (Term.Ref "Nat") (Term.Enu ["()"]))
      (Term.Mat
        "Term.Ref"
        (Term.Sig
          (Quan.Q1)
          (Term.App
            (Quan.Q0)
            (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
            (Term.Ref "U32"))
          (Term.Enu ["()"]))
        (Term.Mat
          "Term.Ann"
          (Term.Sig
            (Quan.Q1)
            (Term.Ref "Term")
            (Term.Sig (Quan.Q1) (Term.Ref "Term") (Term.Enu ["()"])))
          (Term.Mat
            "Term.Let"
            (Term.Sig
              (Quan.Q1)
              (Term.Ref "Quan")
              (Term.Sig
                (Quan.Q1)
                (Term.Ref "Term")
                (Term.Sig (Quan.Q1) (Term.Ref "Term") (Term.Enu ["()"]))))
            (Term.Mat
              "Term.Typ"
              (Term.Sig (Quan.Q1) (Term.Ref "Term") (Term.Enu ["()"]))
              (Term.Mat
                "Term.Min"
                (Term.Sig
                  (Quan.Q1)
                  (Term.Ref "Term")
                  (Term.Sig (Quan.Q1) (Term.Ref "Term") (Term.Enu ["()"])))
                (Term.Mat
                  "Term.All"
                  (Term.Sig
                    (Quan.Q1)
                    (Term.Ref "Quan")
                    (Term.Sig
                      (Quan.Q1)
                      (Term.Ref "Term")
                      (Term.Sig (Quan.Q1) (Term.Ref "Term") (Term.Enu ["()"]))))
                  (Term.Mat
                    "Term.Lam"
                    (Term.Sig
                      (Quan.Q1)
                      (Term.Ref "Quan")
                      (Term.Sig (Quan.Q1) (Term.Ref "Term") (Term.Enu ["()"])))
                    (Term.Mat
                      "Term.App"
                      (Term.Sig
                        (Quan.Q1)
                        (Term.Ref "Quan")
                        (Term.Sig
                          (Quan.Q1)
                          (Term.Ref "Term")
                          (Term.Sig (Quan.Q1) (Term.Ref "Term") (Term.Enu ["()"]))))
                      (Term.Mat
                        "Term.Sig"
                        (Term.Sig
                          (Quan.Q1)
                          (Term.Ref "Quan")
                          (Term.Sig
                            (Quan.Q1)
                            (Term.Ref "Term")
                            (Term.Sig (Quan.Q1) (Term.Ref "Term") (Term.Enu ["()"]))))
                        (Term.Mat
                          "Term.Tup"
                          (Term.Sig
                            (Quan.Q1)
                            (Term.Ref "Quan")
                            (Term.Sig
                              (Quan.Q1)
                              (Term.Ref "Term")
                              (Term.Sig (Quan.Q1) (Term.Ref "Term") (Term.Enu ["()"]))))
                          (Term.Mat
                            "Term.Prj"
                            (Term.Sig (Quan.Q1) (Term.Ref "Term") (Term.Enu ["()"]))
                            (Term.Mat
                              "Term.Enu"
                              (Term.Sig
                                (Quan.Q1)
                                (Term.App
                                  (Quan.Q0)
                                  (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
                                  (Term.App
                                    (Quan.Q0)
                                    (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
                                    (Term.Ref "U32")))
                                (Term.Enu ["()"]))
                              (Term.Mat
                                "Term.Lab"
                                (Term.Sig
                                  (Quan.Q1)
                                  (Term.App
                                    (Quan.Q0)
                                    (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
                                    (Term.Ref "U32"))
                                  (Term.Enu ["()"]))
                                (Term.Mat
                                  "Term.Mat"
                                  (Term.Sig
                                    (Quan.Q1)
                                    (Term.App
                                      (Quan.Q0)
                                      (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
                                      (Term.Ref "U32"))
                                    (Term.Sig
                                      (Quan.Q1)
                                      (Term.Ref "Term")
                                      (Term.Sig (Quan.Q1) (Term.Ref "Term") (Term.Enu ["()"]))))
                                  (Term.Mat
                                    "Term.Efq"
                                    (Term.Enu ["()"])
                                    (Term.Mat
                                      "Term.Eql"
                                      (Term.Sig
                                        (Quan.Q1)
                                        (Term.Ref "Term")
                                        (Term.Sig
                                          (Quan.Q1)
                                          (Term.Ref "Term")
                                          (Term.Sig (Quan.Q1) (Term.Ref "Term") (Term.Enu ["()"]))))
                                      (Term.Mat
                                        "Term.Rfl"
                                        (Term.Enu ["()"])
                                        (Term.Mat
                                          "Term.Rwt"
                                          (Term.Sig
                                            (Quan.Q1)
                                            (Term.Ref "Term")
                                            (Term.Sig
                                              (Quan.Q1)
                                              (Term.Ref "Term")
                                              (Term.Sig
                                                (Quan.Q1)
                                                (Term.Ref "Term")
                                                (Term.Enu ["()"]))))
                                          (Term.Efq))))))))))))))))))),
    false⟩

def «reader.Term» : Def :=
  ⟨"Term",
    Term.Typ (Term.Lab "Q2"),
    Term.Sig
      (Quan.Q1)
      (Term.Enu
        ["Term.Var", "Term.Ref", "Term.Ann", "Term.Let", "Term.Typ", "Term.Min", "Term.All",
         "Term.Lam", "Term.App", "Term.Sig", "Term.Tup", "Term.Prj", "Term.Enu", "Term.Lab",
         "Term.Mat", "Term.Efq", "Term.Eql", "Term.Rfl", "Term.Rwt"])
      (Term.App (Quan.Q1) (Term.Ref "Term.arms") (Term.Var 0)),
    false⟩

def «reader.Def.arms» : Def :=
  ⟨"Def.arms",
    Term.All (Quan.Q1) (Term.Enu ["Def"]) (Term.Typ (Term.Lab "Q2")),
    Term.Mat
      "Def"
      (Term.Sig
        (Quan.Q1)
        (Term.App (Quan.Q0) (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "U32"))
        (Term.Sig
          (Quan.Q1)
          (Term.Ref "Term")
          (Term.Sig
            (Quan.Q1)
            (Term.Ref "Term")
            (Term.Sig (Quan.Q1) (Term.Ref "Bool") (Term.Enu ["()"])))))
      (Term.Efq),
    false⟩

def «reader.Def» : Def :=
  ⟨"Def",
    Term.Typ (Term.Lab "Q2"),
    Term.Sig (Quan.Q1) (Term.Enu ["Def"]) (Term.App (Quan.Q1) (Term.Ref "Def.arms") (Term.Var 0)),
    false⟩

def «reader.Item.arms» : Def :=
  ⟨"Item.arms",
    Term.All
      (Quan.Q1)
      (Term.Enu
        ["Item.quan", "Item.nat", "Item.name", "Item.names", "Item.bool", "Item.term", "Item.def",
         "Item.defs"])
      (Term.Typ (Term.Lab "Q2")),
    Term.Mat
      "Item.quan"
      (Term.Sig (Quan.Q1) (Term.Ref "Quan") (Term.Enu ["()"]))
      (Term.Mat
        "Item.nat"
        (Term.Sig (Quan.Q1) (Term.Ref "Nat") (Term.Enu ["()"]))
        (Term.Mat
          "Item.name"
          (Term.Sig
            (Quan.Q1)
            (Term.App
              (Quan.Q0)
              (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
              (Term.Ref "U32"))
            (Term.Enu ["()"]))
          (Term.Mat
            "Item.names"
            (Term.Sig
              (Quan.Q1)
              (Term.App
                (Quan.Q0)
                (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
                (Term.App
                  (Quan.Q0)
                  (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
                  (Term.Ref "U32")))
              (Term.Enu ["()"]))
            (Term.Mat
              "Item.bool"
              (Term.Sig (Quan.Q1) (Term.Ref "Bool") (Term.Enu ["()"]))
              (Term.Mat
                "Item.term"
                (Term.Sig (Quan.Q1) (Term.Ref "Term") (Term.Enu ["()"]))
                (Term.Mat
                  "Item.def"
                  (Term.Sig (Quan.Q1) (Term.Ref "Def") (Term.Enu ["()"]))
                  (Term.Mat
                    "Item.defs"
                    (Term.Sig
                      (Quan.Q1)
                      (Term.App
                        (Quan.Q0)
                        (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
                        (Term.Ref "Def"))
                      (Term.Enu ["()"]))
                    (Term.Efq)))))))),
    false⟩

def «reader.Item» : Def :=
  ⟨"Item",
    Term.Typ (Term.Lab "Q2"),
    Term.Sig
      (Quan.Q1)
      (Term.Enu
        ["Item.quan", "Item.nat", "Item.name", "Item.names", "Item.bool", "Item.term", "Item.def",
         "Item.defs"])
      (Term.App (Quan.Q1) (Term.Ref "Item.arms") (Term.Var 0)),
    false⟩

def «reader.Book.read.succ» : Def :=
  ⟨"Book.read.succ",
    Term.All
      (Quan.Q1)
      (Term.App (Quan.Q0) (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "Item"))
      (Term.App
        (Quan.Q0)
        (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
          (Term.Ref "Item"))),
    Term.Prj
      (Term.Mat
        "Con"
        (Term.Prj
          (Term.Prj
            (Term.Mat
              "Item.nat"
              (Term.Prj
                (Term.Lam
                  (Quan.Q1)
                  (Term.Mat
                    "()"
                    (Term.Prj
                      (Term.Lam
                        (Quan.Q1)
                        (Term.Mat
                          "()"
                          (Term.Tup
                            (Quan.Q1)
                            (Term.Lab "Some")
                            (Term.Tup
                              (Quan.Q1)
                              (Term.Tup
                                (Quan.Q1)
                                (Term.Lab "Con")
                                (Term.Tup
                                  (Quan.Q1)
                                  (Term.Tup
                                    (Quan.Q1)
                                    (Term.Lab "Item.nat")
                                    (Term.Tup
                                      (Quan.Q1)
                                      (Term.Tup
                                        (Quan.Q1)
                                        (Term.Lab "Succ")
                                        (Term.Tup (Quan.Q1) (Term.Var 1) (Term.Lab "()")))
                                      (Term.Lab "()")))
                                  (Term.Tup (Quan.Q1) (Term.Var 0) (Term.Lab "()"))))
                              (Term.Lab "()")))
                          (Term.Efq))))
                    (Term.Efq))))
              (Term.Lam
                (Quan.Q1)
                (Term.Lam
                  (Quan.Q1)
                  (Term.Prj
                    (Term.Lam
                      (Quan.Q1)
                      (Term.Mat
                        "()"
                        (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                        (Term.Efq)))))))))
        (Term.Lam
          (Quan.Q1)
          (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))))),
    false⟩

def «reader.Book.read.byte» : Def :=
  ⟨"Book.read.byte",
    Term.All
      (Quan.Q1)
      (Term.App (Quan.Q0) (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "Item"))
      (Term.All
        (Quan.Q1)
        (Term.Ref "U32")
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
          (Term.App
            (Quan.Q0)
            (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
            (Term.Ref "Item")))),
    Term.Prj
      (Term.Mat
        "Con"
        (Term.Prj
          (Term.Prj
            (Term.Mat
              "Item.name"
              (Term.Prj
                (Term.Lam
                  (Quan.Q1)
                  (Term.Mat
                    "()"
                    (Term.Prj
                      (Term.Lam
                        (Quan.Q1)
                        (Term.Mat
                          "()"
                          (Term.Lam
                            (Quan.Q1)
                            (Term.Tup
                              (Quan.Q1)
                              (Term.Lab "Some")
                              (Term.Tup
                                (Quan.Q1)
                                (Term.Tup
                                  (Quan.Q1)
                                  (Term.Lab "Con")
                                  (Term.Tup
                                    (Quan.Q1)
                                    (Term.Tup
                                      (Quan.Q1)
                                      (Term.Lab "Item.name")
                                      (Term.Tup
                                        (Quan.Q1)
                                        (Term.Tup
                                          (Quan.Q1)
                                          (Term.Lab "Con")
                                          (Term.Tup
                                            (Quan.Q1)
                                            (Term.Var 0)
                                            (Term.Tup (Quan.Q1) (Term.Var 2) (Term.Lab "()"))))
                                        (Term.Lab "()")))
                                    (Term.Tup (Quan.Q1) (Term.Var 1) (Term.Lab "()"))))
                                (Term.Lab "()"))))
                          (Term.Efq))))
                    (Term.Efq))))
              (Term.Lam
                (Quan.Q1)
                (Term.Lam
                  (Quan.Q1)
                  (Term.Prj
                    (Term.Lam
                      (Quan.Q1)
                      (Term.Mat
                        "()"
                        (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()")))
                        (Term.Efq)))))))))
        (Term.Lam
          (Quan.Q1)
          (Term.Lam
            (Quan.Q1)
            (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()")))))),
    false⟩

def «reader.Book.read.names» : Def :=
  ⟨"Book.read.names",
    Term.All
      (Quan.Q1)
      (Term.App (Quan.Q0) (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "Item"))
      (Term.App
        (Quan.Q0)
        (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
          (Term.Ref "Item"))),
    Term.Prj
      (Term.Mat
        "Con"
        (Term.Prj
          (Term.Prj
            (Term.Mat
              "Item.name"
              (Term.Prj
                (Term.Lam
                  (Quan.Q1)
                  (Term.Mat
                    "()"
                    (Term.Prj
                      (Term.Prj
                        (Term.Mat
                          "Con"
                          (Term.Prj
                            (Term.Prj
                              (Term.Mat
                                "Item.names"
                                (Term.Prj
                                  (Term.Lam
                                    (Quan.Q1)
                                    (Term.Mat
                                      "()"
                                      (Term.Prj
                                        (Term.Lam
                                          (Quan.Q1)
                                          (Term.Mat
                                            "()"
                                            (Term.Mat
                                              "()"
                                              (Term.Tup
                                                (Quan.Q1)
                                                (Term.Lab "Some")
                                                (Term.Tup
                                                  (Quan.Q1)
                                                  (Term.Tup
                                                    (Quan.Q1)
                                                    (Term.Lab "Con")
                                                    (Term.Tup
                                                      (Quan.Q1)
                                                      (Term.Tup
                                                        (Quan.Q1)
                                                        (Term.Lab "Item.names")
                                                        (Term.Tup
                                                          (Quan.Q1)
                                                          (Term.Tup
                                                            (Quan.Q1)
                                                            (Term.Lab "Con")
                                                            (Term.Tup
                                                              (Quan.Q1)
                                                              (Term.Var 2)
                                                              (Term.Tup
                                                                (Quan.Q1)
                                                                (Term.Var 1)
                                                                (Term.Lab "()"))))
                                                          (Term.Lab "()")))
                                                      (Term.Tup
                                                        (Quan.Q1)
                                                        (Term.Var 0)
                                                        (Term.Lab "()"))))
                                                  (Term.Lab "()")))
                                              (Term.Efq))
                                            (Term.Efq))))
                                      (Term.Efq))))
                                (Term.Lam
                                  (Quan.Q1)
                                  (Term.Lam
                                    (Quan.Q1)
                                    (Term.Prj
                                      (Term.Lam
                                        (Quan.Q1)
                                        (Term.Mat
                                          "()"
                                          (Term.Mat
                                            "()"
                                            (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                                            (Term.Efq))
                                          (Term.Efq)))))))))
                          (Term.Lam
                            (Quan.Q1)
                            (Term.Lam
                              (Quan.Q1)
                              (Term.Mat
                                "()"
                                (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                                (Term.Efq)))))))
                    (Term.Efq))))
              (Term.Lam
                (Quan.Q1)
                (Term.Lam
                  (Quan.Q1)
                  (Term.Prj
                    (Term.Lam
                      (Quan.Q1)
                      (Term.Mat
                        "()"
                        (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                        (Term.Efq)))))))))
        (Term.Lam
          (Quan.Q1)
          (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))))),
    false⟩

def «reader.Book.read.defs» : Def :=
  ⟨"Book.read.defs",
    Term.All
      (Quan.Q1)
      (Term.App (Quan.Q0) (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "Item"))
      (Term.App
        (Quan.Q0)
        (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
          (Term.Ref "Item"))),
    Term.Prj
      (Term.Mat
        "Con"
        (Term.Prj
          (Term.Prj
            (Term.Mat
              "Item.def"
              (Term.Prj
                (Term.Lam
                  (Quan.Q1)
                  (Term.Mat
                    "()"
                    (Term.Prj
                      (Term.Prj
                        (Term.Mat
                          "Con"
                          (Term.Prj
                            (Term.Prj
                              (Term.Mat
                                "Item.defs"
                                (Term.Prj
                                  (Term.Lam
                                    (Quan.Q1)
                                    (Term.Mat
                                      "()"
                                      (Term.Prj
                                        (Term.Lam
                                          (Quan.Q1)
                                          (Term.Mat
                                            "()"
                                            (Term.Mat
                                              "()"
                                              (Term.Tup
                                                (Quan.Q1)
                                                (Term.Lab "Some")
                                                (Term.Tup
                                                  (Quan.Q1)
                                                  (Term.Tup
                                                    (Quan.Q1)
                                                    (Term.Lab "Con")
                                                    (Term.Tup
                                                      (Quan.Q1)
                                                      (Term.Tup
                                                        (Quan.Q1)
                                                        (Term.Lab "Item.defs")
                                                        (Term.Tup
                                                          (Quan.Q1)
                                                          (Term.Tup
                                                            (Quan.Q1)
                                                            (Term.Lab "Con")
                                                            (Term.Tup
                                                              (Quan.Q1)
                                                              (Term.Var 2)
                                                              (Term.Tup
                                                                (Quan.Q1)
                                                                (Term.Var 1)
                                                                (Term.Lab "()"))))
                                                          (Term.Lab "()")))
                                                      (Term.Tup
                                                        (Quan.Q1)
                                                        (Term.Var 0)
                                                        (Term.Lab "()"))))
                                                  (Term.Lab "()")))
                                              (Term.Efq))
                                            (Term.Efq))))
                                      (Term.Efq))))
                                (Term.Lam
                                  (Quan.Q1)
                                  (Term.Lam
                                    (Quan.Q1)
                                    (Term.Prj
                                      (Term.Lam
                                        (Quan.Q1)
                                        (Term.Mat
                                          "()"
                                          (Term.Mat
                                            "()"
                                            (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                                            (Term.Efq))
                                          (Term.Efq)))))))))
                          (Term.Lam
                            (Quan.Q1)
                            (Term.Lam
                              (Quan.Q1)
                              (Term.Mat
                                "()"
                                (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                                (Term.Efq)))))))
                    (Term.Efq))))
              (Term.Lam
                (Quan.Q1)
                (Term.Lam
                  (Quan.Q1)
                  (Term.Prj
                    (Term.Lam
                      (Quan.Q1)
                      (Term.Mat
                        "()"
                        (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                        (Term.Efq)))))))))
        (Term.Lam
          (Quan.Q1)
          (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))))),
    false⟩

def «reader.Book.read.def» : Def :=
  ⟨"Book.read.def",
    Term.All
      (Quan.Q1)
      (Term.App (Quan.Q0) (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "Item"))
      (Term.App
        (Quan.Q0)
        (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
          (Term.Ref "Item"))),
    Term.Prj
      (Term.Mat
        "Con"
        (Term.Prj
          (Term.Prj
            (Term.Mat
              "Item.bool"
              (Term.Prj
                (Term.Lam
                  (Quan.Q1)
                  (Term.Mat
                    "()"
                    (Term.Prj
                      (Term.Prj
                        (Term.Mat
                          "Con"
                          (Term.Prj
                            (Term.Prj
                              (Term.Mat
                                "Item.term"
                                (Term.Prj
                                  (Term.Lam
                                    (Quan.Q1)
                                    (Term.Mat
                                      "()"
                                      (Term.Prj
                                        (Term.Prj
                                          (Term.Mat
                                            "Con"
                                            (Term.Prj
                                              (Term.Prj
                                                (Term.Mat
                                                  "Item.term"
                                                  (Term.Prj
                                                    (Term.Lam
                                                      (Quan.Q1)
                                                      (Term.Mat
                                                        "()"
                                                        (Term.Prj
                                                          (Term.Prj
                                                            (Term.Mat
                                                              "Con"
                                                              (Term.Prj
                                                                (Term.Prj
                                                                  (Term.Mat
                                                                    "Item.name"
                                                                    (Term.Prj
                                                                      (Term.Lam
                                                                        (Quan.Q1)
                                                                        (Term.Mat
                                                                          "()"
                                                                          (Term.Prj
                                                                            (Term.Lam
                                                                              (Quan.Q1)
                                                                              (Term.Mat
                                                                                "()"
                                                                                (Term.Mat
                                                                                  "()"
                                                                                  (Term.Mat
                                                                                    "()"
                                                                                    (Term.Mat
                                                                                      "()"
                                                                                      (Term.Tup
                                                                                        (Quan.Q1)
                                                                                        (Term.Lab
                                                                                          "Some")
                                                                                        (Term.Tup
                                                                                          (Quan.Q1)
                                                                                          (Term.Tup
                                                                                            (Quan.Q1)
                                                                                            (Term.Lab
                                                                                              "Con")
                                                                                            (Term.Tup
                                                                                              (Quan.Q1)
                                                                                              (Term.Tup
                                                                                                (Quan.Q1)
                                                                                                (Term.Lab
                                                                                                  "Item.def")
                                                                                                (Term.Tup
                                                                                                  (Quan.Q1)
                                                                                                  (Term.Tup
                                                                                                    (Quan.Q1)
                                                                                                    (Term.Lab
                                                                                                      "Def")
                                                                                                    (Term.Tup
                                                                                                      (Quan.Q1)
                                                                                                      (Term.Var
                                                                                                        1)
                                                                                                      (Term.Tup
                                                                                                        (Quan.Q1)
                                                                                                        (Term.Var
                                                                                                          2)
                                                                                                        (Term.Tup
                                                                                                          (Quan.Q1)
                                                                                                          (Term.Var
                                                                                                            3)
                                                                                                          (Term.Tup
                                                                                                            (Quan.Q1)
                                                                                                            (Term.Var
                                                                                                              4)
                                                                                                            (Term.Lab
                                                                                                              "()"))))))
                                                                                                  (Term.Lab
                                                                                                    "()")))
                                                                                              (Term.Tup
                                                                                                (Quan.Q1)
                                                                                                (Term.Var
                                                                                                  0)
                                                                                                (Term.Lab
                                                                                                  "()"))))
                                                                                          (Term.Lab
                                                                                            "()")))
                                                                                      (Term.Efq))
                                                                                    (Term.Efq))
                                                                                  (Term.Efq))
                                                                                (Term.Efq))))
                                                                          (Term.Efq))))
                                                                    (Term.Lam
                                                                      (Quan.Q1)
                                                                      (Term.Lam
                                                                        (Quan.Q1)
                                                                        (Term.Prj
                                                                          (Term.Lam
                                                                            (Quan.Q1)
                                                                            (Term.Mat
                                                                              "()"
                                                                              (Term.Mat
                                                                                "()"
                                                                                (Term.Mat
                                                                                  "()"
                                                                                  (Term.Mat
                                                                                    "()"
                                                                                    (Term.Tup
                                                                                      (Quan.Q1)
                                                                                      (Term.Lab
                                                                                        "None")
                                                                                      (Term.Lab
                                                                                        "()"))
                                                                                    (Term.Efq))
                                                                                  (Term.Efq))
                                                                                (Term.Efq))
                                                                              (Term.Efq)))))))))
                                                              (Term.Lam
                                                                (Quan.Q1)
                                                                (Term.Lam
                                                                  (Quan.Q1)
                                                                  (Term.Mat
                                                                    "()"
                                                                    (Term.Mat
                                                                      "()"
                                                                      (Term.Mat
                                                                        "()"
                                                                        (Term.Tup
                                                                          (Quan.Q1)
                                                                          (Term.Lab "None")
                                                                          (Term.Lab "()"))
                                                                        (Term.Efq))
                                                                      (Term.Efq))
                                                                    (Term.Efq)))))))
                                                        (Term.Efq))))
                                                  (Term.Lam
                                                    (Quan.Q1)
                                                    (Term.Lam
                                                      (Quan.Q1)
                                                      (Term.Prj
                                                        (Term.Lam
                                                          (Quan.Q1)
                                                          (Term.Mat
                                                            "()"
                                                            (Term.Mat
                                                              "()"
                                                              (Term.Mat
                                                                "()"
                                                                (Term.Tup
                                                                  (Quan.Q1)
                                                                  (Term.Lab "None")
                                                                  (Term.Lab "()"))
                                                                (Term.Efq))
                                                              (Term.Efq))
                                                            (Term.Efq)))))))))
                                            (Term.Lam
                                              (Quan.Q1)
                                              (Term.Lam
                                                (Quan.Q1)
                                                (Term.Mat
                                                  "()"
                                                  (Term.Mat
                                                    "()"
                                                    (Term.Tup
                                                      (Quan.Q1)
                                                      (Term.Lab "None")
                                                      (Term.Lab "()"))
                                                    (Term.Efq))
                                                  (Term.Efq)))))))
                                      (Term.Efq))))
                                (Term.Lam
                                  (Quan.Q1)
                                  (Term.Lam
                                    (Quan.Q1)
                                    (Term.Prj
                                      (Term.Lam
                                        (Quan.Q1)
                                        (Term.Mat
                                          "()"
                                          (Term.Mat
                                            "()"
                                            (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                                            (Term.Efq))
                                          (Term.Efq)))))))))
                          (Term.Lam
                            (Quan.Q1)
                            (Term.Lam
                              (Quan.Q1)
                              (Term.Mat
                                "()"
                                (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                                (Term.Efq)))))))
                    (Term.Efq))))
              (Term.Lam
                (Quan.Q1)
                (Term.Lam
                  (Quan.Q1)
                  (Term.Prj
                    (Term.Lam
                      (Quan.Q1)
                      (Term.Mat
                        "()"
                        (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                        (Term.Efq)))))))))
        (Term.Lam
          (Quan.Q1)
          (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))))),
    false⟩

def «reader.Book.read.var» : Def :=
  ⟨"Book.read.var",
    Term.All
      (Quan.Q1)
      (Term.App (Quan.Q0) (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "Item"))
      (Term.App
        (Quan.Q0)
        (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
          (Term.Ref "Item"))),
    Term.Prj
      (Term.Mat
        "Con"
        (Term.Prj
          (Term.Prj
            (Term.Mat
              "Item.nat"
              (Term.Prj
                (Term.Lam
                  (Quan.Q1)
                  (Term.Mat
                    "()"
                    (Term.Prj
                      (Term.Lam
                        (Quan.Q1)
                        (Term.Mat
                          "()"
                          (Term.Tup
                            (Quan.Q1)
                            (Term.Lab "Some")
                            (Term.Tup
                              (Quan.Q1)
                              (Term.Tup
                                (Quan.Q1)
                                (Term.Lab "Con")
                                (Term.Tup
                                  (Quan.Q1)
                                  (Term.Tup
                                    (Quan.Q1)
                                    (Term.Lab "Item.term")
                                    (Term.Tup
                                      (Quan.Q1)
                                      (Term.Tup
                                        (Quan.Q1)
                                        (Term.Lab "Term.Var")
                                        (Term.Tup (Quan.Q1) (Term.Var 1) (Term.Lab "()")))
                                      (Term.Lab "()")))
                                  (Term.Tup (Quan.Q1) (Term.Var 0) (Term.Lab "()"))))
                              (Term.Lab "()")))
                          (Term.Efq))))
                    (Term.Efq))))
              (Term.Lam
                (Quan.Q1)
                (Term.Lam
                  (Quan.Q1)
                  (Term.Prj
                    (Term.Lam
                      (Quan.Q1)
                      (Term.Mat
                        "()"
                        (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                        (Term.Efq)))))))))
        (Term.Lam
          (Quan.Q1)
          (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))))),
    false⟩

def «reader.Book.read.ref» : Def :=
  ⟨"Book.read.ref",
    Term.All
      (Quan.Q1)
      (Term.App (Quan.Q0) (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "Item"))
      (Term.App
        (Quan.Q0)
        (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
          (Term.Ref "Item"))),
    Term.Prj
      (Term.Mat
        "Con"
        (Term.Prj
          (Term.Prj
            (Term.Mat
              "Item.name"
              (Term.Prj
                (Term.Lam
                  (Quan.Q1)
                  (Term.Mat
                    "()"
                    (Term.Prj
                      (Term.Lam
                        (Quan.Q1)
                        (Term.Mat
                          "()"
                          (Term.Tup
                            (Quan.Q1)
                            (Term.Lab "Some")
                            (Term.Tup
                              (Quan.Q1)
                              (Term.Tup
                                (Quan.Q1)
                                (Term.Lab "Con")
                                (Term.Tup
                                  (Quan.Q1)
                                  (Term.Tup
                                    (Quan.Q1)
                                    (Term.Lab "Item.term")
                                    (Term.Tup
                                      (Quan.Q1)
                                      (Term.Tup
                                        (Quan.Q1)
                                        (Term.Lab "Term.Ref")
                                        (Term.Tup (Quan.Q1) (Term.Var 1) (Term.Lab "()")))
                                      (Term.Lab "()")))
                                  (Term.Tup (Quan.Q1) (Term.Var 0) (Term.Lab "()"))))
                              (Term.Lab "()")))
                          (Term.Efq))))
                    (Term.Efq))))
              (Term.Lam
                (Quan.Q1)
                (Term.Lam
                  (Quan.Q1)
                  (Term.Prj
                    (Term.Lam
                      (Quan.Q1)
                      (Term.Mat
                        "()"
                        (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                        (Term.Efq)))))))))
        (Term.Lam
          (Quan.Q1)
          (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))))),
    false⟩

def «reader.Book.read.ann» : Def :=
  ⟨"Book.read.ann",
    Term.All
      (Quan.Q1)
      (Term.App (Quan.Q0) (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "Item"))
      (Term.App
        (Quan.Q0)
        (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
          (Term.Ref "Item"))),
    Term.Prj
      (Term.Mat
        "Con"
        (Term.Prj
          (Term.Prj
            (Term.Mat
              "Item.term"
              (Term.Prj
                (Term.Lam
                  (Quan.Q1)
                  (Term.Mat
                    "()"
                    (Term.Prj
                      (Term.Prj
                        (Term.Mat
                          "Con"
                          (Term.Prj
                            (Term.Prj
                              (Term.Mat
                                "Item.term"
                                (Term.Prj
                                  (Term.Lam
                                    (Quan.Q1)
                                    (Term.Mat
                                      "()"
                                      (Term.Prj
                                        (Term.Lam
                                          (Quan.Q1)
                                          (Term.Mat
                                            "()"
                                            (Term.Mat
                                              "()"
                                              (Term.Tup
                                                (Quan.Q1)
                                                (Term.Lab "Some")
                                                (Term.Tup
                                                  (Quan.Q1)
                                                  (Term.Tup
                                                    (Quan.Q1)
                                                    (Term.Lab "Con")
                                                    (Term.Tup
                                                      (Quan.Q1)
                                                      (Term.Tup
                                                        (Quan.Q1)
                                                        (Term.Lab "Item.term")
                                                        (Term.Tup
                                                          (Quan.Q1)
                                                          (Term.Tup
                                                            (Quan.Q1)
                                                            (Term.Lab "Term.Ann")
                                                            (Term.Tup
                                                              (Quan.Q1)
                                                              (Term.Var 1)
                                                              (Term.Tup
                                                                (Quan.Q1)
                                                                (Term.Var 2)
                                                                (Term.Lab "()"))))
                                                          (Term.Lab "()")))
                                                      (Term.Tup
                                                        (Quan.Q1)
                                                        (Term.Var 0)
                                                        (Term.Lab "()"))))
                                                  (Term.Lab "()")))
                                              (Term.Efq))
                                            (Term.Efq))))
                                      (Term.Efq))))
                                (Term.Lam
                                  (Quan.Q1)
                                  (Term.Lam
                                    (Quan.Q1)
                                    (Term.Prj
                                      (Term.Lam
                                        (Quan.Q1)
                                        (Term.Mat
                                          "()"
                                          (Term.Mat
                                            "()"
                                            (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                                            (Term.Efq))
                                          (Term.Efq)))))))))
                          (Term.Lam
                            (Quan.Q1)
                            (Term.Lam
                              (Quan.Q1)
                              (Term.Mat
                                "()"
                                (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                                (Term.Efq)))))))
                    (Term.Efq))))
              (Term.Lam
                (Quan.Q1)
                (Term.Lam
                  (Quan.Q1)
                  (Term.Prj
                    (Term.Lam
                      (Quan.Q1)
                      (Term.Mat
                        "()"
                        (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                        (Term.Efq)))))))))
        (Term.Lam
          (Quan.Q1)
          (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))))),
    false⟩

def «reader.Book.read.let» : Def :=
  ⟨"Book.read.let",
    Term.All
      (Quan.Q1)
      (Term.App (Quan.Q0) (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "Item"))
      (Term.App
        (Quan.Q0)
        (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
          (Term.Ref "Item"))),
    Term.Prj
      (Term.Mat
        "Con"
        (Term.Prj
          (Term.Prj
            (Term.Mat
              "Item.term"
              (Term.Prj
                (Term.Lam
                  (Quan.Q1)
                  (Term.Mat
                    "()"
                    (Term.Prj
                      (Term.Prj
                        (Term.Mat
                          "Con"
                          (Term.Prj
                            (Term.Prj
                              (Term.Mat
                                "Item.term"
                                (Term.Prj
                                  (Term.Lam
                                    (Quan.Q1)
                                    (Term.Mat
                                      "()"
                                      (Term.Prj
                                        (Term.Prj
                                          (Term.Mat
                                            "Con"
                                            (Term.Prj
                                              (Term.Prj
                                                (Term.Mat
                                                  "Item.quan"
                                                  (Term.Prj
                                                    (Term.Lam
                                                      (Quan.Q1)
                                                      (Term.Mat
                                                        "()"
                                                        (Term.Prj
                                                          (Term.Lam
                                                            (Quan.Q1)
                                                            (Term.Mat
                                                              "()"
                                                              (Term.Mat
                                                                "()"
                                                                (Term.Mat
                                                                  "()"
                                                                  (Term.Tup
                                                                    (Quan.Q1)
                                                                    (Term.Lab "Some")
                                                                    (Term.Tup
                                                                      (Quan.Q1)
                                                                      (Term.Tup
                                                                        (Quan.Q1)
                                                                        (Term.Lab "Con")
                                                                        (Term.Tup
                                                                          (Quan.Q1)
                                                                          (Term.Tup
                                                                            (Quan.Q1)
                                                                            (Term.Lab "Item.term")
                                                                            (Term.Tup
                                                                              (Quan.Q1)
                                                                              (Term.Tup
                                                                                (Quan.Q1)
                                                                                (Term.Lab
                                                                                  "Term.Let")
                                                                                (Term.Tup
                                                                                  (Quan.Q1)
                                                                                  (Term.Var 1)
                                                                                  (Term.Tup
                                                                                    (Quan.Q1)
                                                                                    (Term.Var 2)
                                                                                    (Term.Tup
                                                                                      (Quan.Q1)
                                                                                      (Term.Var 3)
                                                                                      (Term.Lab
                                                                                        "()")))))
                                                                              (Term.Lab "()")))
                                                                          (Term.Tup
                                                                            (Quan.Q1)
                                                                            (Term.Var 0)
                                                                            (Term.Lab "()"))))
                                                                      (Term.Lab "()")))
                                                                  (Term.Efq))
                                                                (Term.Efq))
                                                              (Term.Efq))))
                                                        (Term.Efq))))
                                                  (Term.Lam
                                                    (Quan.Q1)
                                                    (Term.Lam
                                                      (Quan.Q1)
                                                      (Term.Prj
                                                        (Term.Lam
                                                          (Quan.Q1)
                                                          (Term.Mat
                                                            "()"
                                                            (Term.Mat
                                                              "()"
                                                              (Term.Mat
                                                                "()"
                                                                (Term.Tup
                                                                  (Quan.Q1)
                                                                  (Term.Lab "None")
                                                                  (Term.Lab "()"))
                                                                (Term.Efq))
                                                              (Term.Efq))
                                                            (Term.Efq)))))))))
                                            (Term.Lam
                                              (Quan.Q1)
                                              (Term.Lam
                                                (Quan.Q1)
                                                (Term.Mat
                                                  "()"
                                                  (Term.Mat
                                                    "()"
                                                    (Term.Tup
                                                      (Quan.Q1)
                                                      (Term.Lab "None")
                                                      (Term.Lab "()"))
                                                    (Term.Efq))
                                                  (Term.Efq)))))))
                                      (Term.Efq))))
                                (Term.Lam
                                  (Quan.Q1)
                                  (Term.Lam
                                    (Quan.Q1)
                                    (Term.Prj
                                      (Term.Lam
                                        (Quan.Q1)
                                        (Term.Mat
                                          "()"
                                          (Term.Mat
                                            "()"
                                            (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                                            (Term.Efq))
                                          (Term.Efq)))))))))
                          (Term.Lam
                            (Quan.Q1)
                            (Term.Lam
                              (Quan.Q1)
                              (Term.Mat
                                "()"
                                (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                                (Term.Efq)))))))
                    (Term.Efq))))
              (Term.Lam
                (Quan.Q1)
                (Term.Lam
                  (Quan.Q1)
                  (Term.Prj
                    (Term.Lam
                      (Quan.Q1)
                      (Term.Mat
                        "()"
                        (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                        (Term.Efq)))))))))
        (Term.Lam
          (Quan.Q1)
          (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))))),
    false⟩

def «reader.Book.read.typ» : Def :=
  ⟨"Book.read.typ",
    Term.All
      (Quan.Q1)
      (Term.App (Quan.Q0) (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "Item"))
      (Term.App
        (Quan.Q0)
        (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
          (Term.Ref "Item"))),
    Term.Prj
      (Term.Mat
        "Con"
        (Term.Prj
          (Term.Prj
            (Term.Mat
              "Item.term"
              (Term.Prj
                (Term.Lam
                  (Quan.Q1)
                  (Term.Mat
                    "()"
                    (Term.Prj
                      (Term.Lam
                        (Quan.Q1)
                        (Term.Mat
                          "()"
                          (Term.Tup
                            (Quan.Q1)
                            (Term.Lab "Some")
                            (Term.Tup
                              (Quan.Q1)
                              (Term.Tup
                                (Quan.Q1)
                                (Term.Lab "Con")
                                (Term.Tup
                                  (Quan.Q1)
                                  (Term.Tup
                                    (Quan.Q1)
                                    (Term.Lab "Item.term")
                                    (Term.Tup
                                      (Quan.Q1)
                                      (Term.Tup
                                        (Quan.Q1)
                                        (Term.Lab "Term.Typ")
                                        (Term.Tup (Quan.Q1) (Term.Var 1) (Term.Lab "()")))
                                      (Term.Lab "()")))
                                  (Term.Tup (Quan.Q1) (Term.Var 0) (Term.Lab "()"))))
                              (Term.Lab "()")))
                          (Term.Efq))))
                    (Term.Efq))))
              (Term.Lam
                (Quan.Q1)
                (Term.Lam
                  (Quan.Q1)
                  (Term.Prj
                    (Term.Lam
                      (Quan.Q1)
                      (Term.Mat
                        "()"
                        (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                        (Term.Efq)))))))))
        (Term.Lam
          (Quan.Q1)
          (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))))),
    false⟩

def «reader.Book.read.min» : Def :=
  ⟨"Book.read.min",
    Term.All
      (Quan.Q1)
      (Term.App (Quan.Q0) (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "Item"))
      (Term.App
        (Quan.Q0)
        (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
          (Term.Ref "Item"))),
    Term.Prj
      (Term.Mat
        "Con"
        (Term.Prj
          (Term.Prj
            (Term.Mat
              "Item.term"
              (Term.Prj
                (Term.Lam
                  (Quan.Q1)
                  (Term.Mat
                    "()"
                    (Term.Prj
                      (Term.Prj
                        (Term.Mat
                          "Con"
                          (Term.Prj
                            (Term.Prj
                              (Term.Mat
                                "Item.term"
                                (Term.Prj
                                  (Term.Lam
                                    (Quan.Q1)
                                    (Term.Mat
                                      "()"
                                      (Term.Prj
                                        (Term.Lam
                                          (Quan.Q1)
                                          (Term.Mat
                                            "()"
                                            (Term.Mat
                                              "()"
                                              (Term.Tup
                                                (Quan.Q1)
                                                (Term.Lab "Some")
                                                (Term.Tup
                                                  (Quan.Q1)
                                                  (Term.Tup
                                                    (Quan.Q1)
                                                    (Term.Lab "Con")
                                                    (Term.Tup
                                                      (Quan.Q1)
                                                      (Term.Tup
                                                        (Quan.Q1)
                                                        (Term.Lab "Item.term")
                                                        (Term.Tup
                                                          (Quan.Q1)
                                                          (Term.Tup
                                                            (Quan.Q1)
                                                            (Term.Lab "Term.Min")
                                                            (Term.Tup
                                                              (Quan.Q1)
                                                              (Term.Var 1)
                                                              (Term.Tup
                                                                (Quan.Q1)
                                                                (Term.Var 2)
                                                                (Term.Lab "()"))))
                                                          (Term.Lab "()")))
                                                      (Term.Tup
                                                        (Quan.Q1)
                                                        (Term.Var 0)
                                                        (Term.Lab "()"))))
                                                  (Term.Lab "()")))
                                              (Term.Efq))
                                            (Term.Efq))))
                                      (Term.Efq))))
                                (Term.Lam
                                  (Quan.Q1)
                                  (Term.Lam
                                    (Quan.Q1)
                                    (Term.Prj
                                      (Term.Lam
                                        (Quan.Q1)
                                        (Term.Mat
                                          "()"
                                          (Term.Mat
                                            "()"
                                            (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                                            (Term.Efq))
                                          (Term.Efq)))))))))
                          (Term.Lam
                            (Quan.Q1)
                            (Term.Lam
                              (Quan.Q1)
                              (Term.Mat
                                "()"
                                (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                                (Term.Efq)))))))
                    (Term.Efq))))
              (Term.Lam
                (Quan.Q1)
                (Term.Lam
                  (Quan.Q1)
                  (Term.Prj
                    (Term.Lam
                      (Quan.Q1)
                      (Term.Mat
                        "()"
                        (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                        (Term.Efq)))))))))
        (Term.Lam
          (Quan.Q1)
          (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))))),
    false⟩

def «reader.Book.read.all» : Def :=
  ⟨"Book.read.all",
    Term.All
      (Quan.Q1)
      (Term.App (Quan.Q0) (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "Item"))
      (Term.App
        (Quan.Q0)
        (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
          (Term.Ref "Item"))),
    Term.Prj
      (Term.Mat
        "Con"
        (Term.Prj
          (Term.Prj
            (Term.Mat
              "Item.term"
              (Term.Prj
                (Term.Lam
                  (Quan.Q1)
                  (Term.Mat
                    "()"
                    (Term.Prj
                      (Term.Prj
                        (Term.Mat
                          "Con"
                          (Term.Prj
                            (Term.Prj
                              (Term.Mat
                                "Item.term"
                                (Term.Prj
                                  (Term.Lam
                                    (Quan.Q1)
                                    (Term.Mat
                                      "()"
                                      (Term.Prj
                                        (Term.Prj
                                          (Term.Mat
                                            "Con"
                                            (Term.Prj
                                              (Term.Prj
                                                (Term.Mat
                                                  "Item.quan"
                                                  (Term.Prj
                                                    (Term.Lam
                                                      (Quan.Q1)
                                                      (Term.Mat
                                                        "()"
                                                        (Term.Prj
                                                          (Term.Lam
                                                            (Quan.Q1)
                                                            (Term.Mat
                                                              "()"
                                                              (Term.Mat
                                                                "()"
                                                                (Term.Mat
                                                                  "()"
                                                                  (Term.Tup
                                                                    (Quan.Q1)
                                                                    (Term.Lab "Some")
                                                                    (Term.Tup
                                                                      (Quan.Q1)
                                                                      (Term.Tup
                                                                        (Quan.Q1)
                                                                        (Term.Lab "Con")
                                                                        (Term.Tup
                                                                          (Quan.Q1)
                                                                          (Term.Tup
                                                                            (Quan.Q1)
                                                                            (Term.Lab "Item.term")
                                                                            (Term.Tup
                                                                              (Quan.Q1)
                                                                              (Term.Tup
                                                                                (Quan.Q1)
                                                                                (Term.Lab
                                                                                  "Term.All")
                                                                                (Term.Tup
                                                                                  (Quan.Q1)
                                                                                  (Term.Var 1)
                                                                                  (Term.Tup
                                                                                    (Quan.Q1)
                                                                                    (Term.Var 2)
                                                                                    (Term.Tup
                                                                                      (Quan.Q1)
                                                                                      (Term.Var 3)
                                                                                      (Term.Lab
                                                                                        "()")))))
                                                                              (Term.Lab "()")))
                                                                          (Term.Tup
                                                                            (Quan.Q1)
                                                                            (Term.Var 0)
                                                                            (Term.Lab "()"))))
                                                                      (Term.Lab "()")))
                                                                  (Term.Efq))
                                                                (Term.Efq))
                                                              (Term.Efq))))
                                                        (Term.Efq))))
                                                  (Term.Lam
                                                    (Quan.Q1)
                                                    (Term.Lam
                                                      (Quan.Q1)
                                                      (Term.Prj
                                                        (Term.Lam
                                                          (Quan.Q1)
                                                          (Term.Mat
                                                            "()"
                                                            (Term.Mat
                                                              "()"
                                                              (Term.Mat
                                                                "()"
                                                                (Term.Tup
                                                                  (Quan.Q1)
                                                                  (Term.Lab "None")
                                                                  (Term.Lab "()"))
                                                                (Term.Efq))
                                                              (Term.Efq))
                                                            (Term.Efq)))))))))
                                            (Term.Lam
                                              (Quan.Q1)
                                              (Term.Lam
                                                (Quan.Q1)
                                                (Term.Mat
                                                  "()"
                                                  (Term.Mat
                                                    "()"
                                                    (Term.Tup
                                                      (Quan.Q1)
                                                      (Term.Lab "None")
                                                      (Term.Lab "()"))
                                                    (Term.Efq))
                                                  (Term.Efq)))))))
                                      (Term.Efq))))
                                (Term.Lam
                                  (Quan.Q1)
                                  (Term.Lam
                                    (Quan.Q1)
                                    (Term.Prj
                                      (Term.Lam
                                        (Quan.Q1)
                                        (Term.Mat
                                          "()"
                                          (Term.Mat
                                            "()"
                                            (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                                            (Term.Efq))
                                          (Term.Efq)))))))))
                          (Term.Lam
                            (Quan.Q1)
                            (Term.Lam
                              (Quan.Q1)
                              (Term.Mat
                                "()"
                                (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                                (Term.Efq)))))))
                    (Term.Efq))))
              (Term.Lam
                (Quan.Q1)
                (Term.Lam
                  (Quan.Q1)
                  (Term.Prj
                    (Term.Lam
                      (Quan.Q1)
                      (Term.Mat
                        "()"
                        (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                        (Term.Efq)))))))))
        (Term.Lam
          (Quan.Q1)
          (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))))),
    false⟩

def «reader.Book.read.lam» : Def :=
  ⟨"Book.read.lam",
    Term.All
      (Quan.Q1)
      (Term.App (Quan.Q0) (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "Item"))
      (Term.App
        (Quan.Q0)
        (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
          (Term.Ref "Item"))),
    Term.Prj
      (Term.Mat
        "Con"
        (Term.Prj
          (Term.Prj
            (Term.Mat
              "Item.term"
              (Term.Prj
                (Term.Lam
                  (Quan.Q1)
                  (Term.Mat
                    "()"
                    (Term.Prj
                      (Term.Prj
                        (Term.Mat
                          "Con"
                          (Term.Prj
                            (Term.Prj
                              (Term.Mat
                                "Item.quan"
                                (Term.Prj
                                  (Term.Lam
                                    (Quan.Q1)
                                    (Term.Mat
                                      "()"
                                      (Term.Prj
                                        (Term.Lam
                                          (Quan.Q1)
                                          (Term.Mat
                                            "()"
                                            (Term.Mat
                                              "()"
                                              (Term.Tup
                                                (Quan.Q1)
                                                (Term.Lab "Some")
                                                (Term.Tup
                                                  (Quan.Q1)
                                                  (Term.Tup
                                                    (Quan.Q1)
                                                    (Term.Lab "Con")
                                                    (Term.Tup
                                                      (Quan.Q1)
                                                      (Term.Tup
                                                        (Quan.Q1)
                                                        (Term.Lab "Item.term")
                                                        (Term.Tup
                                                          (Quan.Q1)
                                                          (Term.Tup
                                                            (Quan.Q1)
                                                            (Term.Lab "Term.Lam")
                                                            (Term.Tup
                                                              (Quan.Q1)
                                                              (Term.Var 1)
                                                              (Term.Tup
                                                                (Quan.Q1)
                                                                (Term.Var 2)
                                                                (Term.Lab "()"))))
                                                          (Term.Lab "()")))
                                                      (Term.Tup
                                                        (Quan.Q1)
                                                        (Term.Var 0)
                                                        (Term.Lab "()"))))
                                                  (Term.Lab "()")))
                                              (Term.Efq))
                                            (Term.Efq))))
                                      (Term.Efq))))
                                (Term.Lam
                                  (Quan.Q1)
                                  (Term.Lam
                                    (Quan.Q1)
                                    (Term.Prj
                                      (Term.Lam
                                        (Quan.Q1)
                                        (Term.Mat
                                          "()"
                                          (Term.Mat
                                            "()"
                                            (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                                            (Term.Efq))
                                          (Term.Efq)))))))))
                          (Term.Lam
                            (Quan.Q1)
                            (Term.Lam
                              (Quan.Q1)
                              (Term.Mat
                                "()"
                                (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                                (Term.Efq)))))))
                    (Term.Efq))))
              (Term.Lam
                (Quan.Q1)
                (Term.Lam
                  (Quan.Q1)
                  (Term.Prj
                    (Term.Lam
                      (Quan.Q1)
                      (Term.Mat
                        "()"
                        (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                        (Term.Efq)))))))))
        (Term.Lam
          (Quan.Q1)
          (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))))),
    false⟩

def «reader.Book.read.app» : Def :=
  ⟨"Book.read.app",
    Term.All
      (Quan.Q1)
      (Term.App (Quan.Q0) (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "Item"))
      (Term.App
        (Quan.Q0)
        (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
          (Term.Ref "Item"))),
    Term.Prj
      (Term.Mat
        "Con"
        (Term.Prj
          (Term.Prj
            (Term.Mat
              "Item.term"
              (Term.Prj
                (Term.Lam
                  (Quan.Q1)
                  (Term.Mat
                    "()"
                    (Term.Prj
                      (Term.Prj
                        (Term.Mat
                          "Con"
                          (Term.Prj
                            (Term.Prj
                              (Term.Mat
                                "Item.term"
                                (Term.Prj
                                  (Term.Lam
                                    (Quan.Q1)
                                    (Term.Mat
                                      "()"
                                      (Term.Prj
                                        (Term.Prj
                                          (Term.Mat
                                            "Con"
                                            (Term.Prj
                                              (Term.Prj
                                                (Term.Mat
                                                  "Item.quan"
                                                  (Term.Prj
                                                    (Term.Lam
                                                      (Quan.Q1)
                                                      (Term.Mat
                                                        "()"
                                                        (Term.Prj
                                                          (Term.Lam
                                                            (Quan.Q1)
                                                            (Term.Mat
                                                              "()"
                                                              (Term.Mat
                                                                "()"
                                                                (Term.Mat
                                                                  "()"
                                                                  (Term.Tup
                                                                    (Quan.Q1)
                                                                    (Term.Lab "Some")
                                                                    (Term.Tup
                                                                      (Quan.Q1)
                                                                      (Term.Tup
                                                                        (Quan.Q1)
                                                                        (Term.Lab "Con")
                                                                        (Term.Tup
                                                                          (Quan.Q1)
                                                                          (Term.Tup
                                                                            (Quan.Q1)
                                                                            (Term.Lab "Item.term")
                                                                            (Term.Tup
                                                                              (Quan.Q1)
                                                                              (Term.Tup
                                                                                (Quan.Q1)
                                                                                (Term.Lab
                                                                                  "Term.App")
                                                                                (Term.Tup
                                                                                  (Quan.Q1)
                                                                                  (Term.Var 1)
                                                                                  (Term.Tup
                                                                                    (Quan.Q1)
                                                                                    (Term.Var 2)
                                                                                    (Term.Tup
                                                                                      (Quan.Q1)
                                                                                      (Term.Var 3)
                                                                                      (Term.Lab
                                                                                        "()")))))
                                                                              (Term.Lab "()")))
                                                                          (Term.Tup
                                                                            (Quan.Q1)
                                                                            (Term.Var 0)
                                                                            (Term.Lab "()"))))
                                                                      (Term.Lab "()")))
                                                                  (Term.Efq))
                                                                (Term.Efq))
                                                              (Term.Efq))))
                                                        (Term.Efq))))
                                                  (Term.Lam
                                                    (Quan.Q1)
                                                    (Term.Lam
                                                      (Quan.Q1)
                                                      (Term.Prj
                                                        (Term.Lam
                                                          (Quan.Q1)
                                                          (Term.Mat
                                                            "()"
                                                            (Term.Mat
                                                              "()"
                                                              (Term.Mat
                                                                "()"
                                                                (Term.Tup
                                                                  (Quan.Q1)
                                                                  (Term.Lab "None")
                                                                  (Term.Lab "()"))
                                                                (Term.Efq))
                                                              (Term.Efq))
                                                            (Term.Efq)))))))))
                                            (Term.Lam
                                              (Quan.Q1)
                                              (Term.Lam
                                                (Quan.Q1)
                                                (Term.Mat
                                                  "()"
                                                  (Term.Mat
                                                    "()"
                                                    (Term.Tup
                                                      (Quan.Q1)
                                                      (Term.Lab "None")
                                                      (Term.Lab "()"))
                                                    (Term.Efq))
                                                  (Term.Efq)))))))
                                      (Term.Efq))))
                                (Term.Lam
                                  (Quan.Q1)
                                  (Term.Lam
                                    (Quan.Q1)
                                    (Term.Prj
                                      (Term.Lam
                                        (Quan.Q1)
                                        (Term.Mat
                                          "()"
                                          (Term.Mat
                                            "()"
                                            (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                                            (Term.Efq))
                                          (Term.Efq)))))))))
                          (Term.Lam
                            (Quan.Q1)
                            (Term.Lam
                              (Quan.Q1)
                              (Term.Mat
                                "()"
                                (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                                (Term.Efq)))))))
                    (Term.Efq))))
              (Term.Lam
                (Quan.Q1)
                (Term.Lam
                  (Quan.Q1)
                  (Term.Prj
                    (Term.Lam
                      (Quan.Q1)
                      (Term.Mat
                        "()"
                        (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                        (Term.Efq)))))))))
        (Term.Lam
          (Quan.Q1)
          (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))))),
    false⟩

def «reader.Book.read.sig» : Def :=
  ⟨"Book.read.sig",
    Term.All
      (Quan.Q1)
      (Term.App (Quan.Q0) (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "Item"))
      (Term.App
        (Quan.Q0)
        (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
          (Term.Ref "Item"))),
    Term.Prj
      (Term.Mat
        "Con"
        (Term.Prj
          (Term.Prj
            (Term.Mat
              "Item.term"
              (Term.Prj
                (Term.Lam
                  (Quan.Q1)
                  (Term.Mat
                    "()"
                    (Term.Prj
                      (Term.Prj
                        (Term.Mat
                          "Con"
                          (Term.Prj
                            (Term.Prj
                              (Term.Mat
                                "Item.term"
                                (Term.Prj
                                  (Term.Lam
                                    (Quan.Q1)
                                    (Term.Mat
                                      "()"
                                      (Term.Prj
                                        (Term.Prj
                                          (Term.Mat
                                            "Con"
                                            (Term.Prj
                                              (Term.Prj
                                                (Term.Mat
                                                  "Item.quan"
                                                  (Term.Prj
                                                    (Term.Lam
                                                      (Quan.Q1)
                                                      (Term.Mat
                                                        "()"
                                                        (Term.Prj
                                                          (Term.Lam
                                                            (Quan.Q1)
                                                            (Term.Mat
                                                              "()"
                                                              (Term.Mat
                                                                "()"
                                                                (Term.Mat
                                                                  "()"
                                                                  (Term.Tup
                                                                    (Quan.Q1)
                                                                    (Term.Lab "Some")
                                                                    (Term.Tup
                                                                      (Quan.Q1)
                                                                      (Term.Tup
                                                                        (Quan.Q1)
                                                                        (Term.Lab "Con")
                                                                        (Term.Tup
                                                                          (Quan.Q1)
                                                                          (Term.Tup
                                                                            (Quan.Q1)
                                                                            (Term.Lab "Item.term")
                                                                            (Term.Tup
                                                                              (Quan.Q1)
                                                                              (Term.Tup
                                                                                (Quan.Q1)
                                                                                (Term.Lab
                                                                                  "Term.Sig")
                                                                                (Term.Tup
                                                                                  (Quan.Q1)
                                                                                  (Term.Var 1)
                                                                                  (Term.Tup
                                                                                    (Quan.Q1)
                                                                                    (Term.Var 2)
                                                                                    (Term.Tup
                                                                                      (Quan.Q1)
                                                                                      (Term.Var 3)
                                                                                      (Term.Lab
                                                                                        "()")))))
                                                                              (Term.Lab "()")))
                                                                          (Term.Tup
                                                                            (Quan.Q1)
                                                                            (Term.Var 0)
                                                                            (Term.Lab "()"))))
                                                                      (Term.Lab "()")))
                                                                  (Term.Efq))
                                                                (Term.Efq))
                                                              (Term.Efq))))
                                                        (Term.Efq))))
                                                  (Term.Lam
                                                    (Quan.Q1)
                                                    (Term.Lam
                                                      (Quan.Q1)
                                                      (Term.Prj
                                                        (Term.Lam
                                                          (Quan.Q1)
                                                          (Term.Mat
                                                            "()"
                                                            (Term.Mat
                                                              "()"
                                                              (Term.Mat
                                                                "()"
                                                                (Term.Tup
                                                                  (Quan.Q1)
                                                                  (Term.Lab "None")
                                                                  (Term.Lab "()"))
                                                                (Term.Efq))
                                                              (Term.Efq))
                                                            (Term.Efq)))))))))
                                            (Term.Lam
                                              (Quan.Q1)
                                              (Term.Lam
                                                (Quan.Q1)
                                                (Term.Mat
                                                  "()"
                                                  (Term.Mat
                                                    "()"
                                                    (Term.Tup
                                                      (Quan.Q1)
                                                      (Term.Lab "None")
                                                      (Term.Lab "()"))
                                                    (Term.Efq))
                                                  (Term.Efq)))))))
                                      (Term.Efq))))
                                (Term.Lam
                                  (Quan.Q1)
                                  (Term.Lam
                                    (Quan.Q1)
                                    (Term.Prj
                                      (Term.Lam
                                        (Quan.Q1)
                                        (Term.Mat
                                          "()"
                                          (Term.Mat
                                            "()"
                                            (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                                            (Term.Efq))
                                          (Term.Efq)))))))))
                          (Term.Lam
                            (Quan.Q1)
                            (Term.Lam
                              (Quan.Q1)
                              (Term.Mat
                                "()"
                                (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                                (Term.Efq)))))))
                    (Term.Efq))))
              (Term.Lam
                (Quan.Q1)
                (Term.Lam
                  (Quan.Q1)
                  (Term.Prj
                    (Term.Lam
                      (Quan.Q1)
                      (Term.Mat
                        "()"
                        (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                        (Term.Efq)))))))))
        (Term.Lam
          (Quan.Q1)
          (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))))),
    false⟩

def «reader.Book.read.tup» : Def :=
  ⟨"Book.read.tup",
    Term.All
      (Quan.Q1)
      (Term.App (Quan.Q0) (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "Item"))
      (Term.App
        (Quan.Q0)
        (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
          (Term.Ref "Item"))),
    Term.Prj
      (Term.Mat
        "Con"
        (Term.Prj
          (Term.Prj
            (Term.Mat
              "Item.term"
              (Term.Prj
                (Term.Lam
                  (Quan.Q1)
                  (Term.Mat
                    "()"
                    (Term.Prj
                      (Term.Prj
                        (Term.Mat
                          "Con"
                          (Term.Prj
                            (Term.Prj
                              (Term.Mat
                                "Item.term"
                                (Term.Prj
                                  (Term.Lam
                                    (Quan.Q1)
                                    (Term.Mat
                                      "()"
                                      (Term.Prj
                                        (Term.Prj
                                          (Term.Mat
                                            "Con"
                                            (Term.Prj
                                              (Term.Prj
                                                (Term.Mat
                                                  "Item.quan"
                                                  (Term.Prj
                                                    (Term.Lam
                                                      (Quan.Q1)
                                                      (Term.Mat
                                                        "()"
                                                        (Term.Prj
                                                          (Term.Lam
                                                            (Quan.Q1)
                                                            (Term.Mat
                                                              "()"
                                                              (Term.Mat
                                                                "()"
                                                                (Term.Mat
                                                                  "()"
                                                                  (Term.Tup
                                                                    (Quan.Q1)
                                                                    (Term.Lab "Some")
                                                                    (Term.Tup
                                                                      (Quan.Q1)
                                                                      (Term.Tup
                                                                        (Quan.Q1)
                                                                        (Term.Lab "Con")
                                                                        (Term.Tup
                                                                          (Quan.Q1)
                                                                          (Term.Tup
                                                                            (Quan.Q1)
                                                                            (Term.Lab "Item.term")
                                                                            (Term.Tup
                                                                              (Quan.Q1)
                                                                              (Term.Tup
                                                                                (Quan.Q1)
                                                                                (Term.Lab
                                                                                  "Term.Tup")
                                                                                (Term.Tup
                                                                                  (Quan.Q1)
                                                                                  (Term.Var 1)
                                                                                  (Term.Tup
                                                                                    (Quan.Q1)
                                                                                    (Term.Var 2)
                                                                                    (Term.Tup
                                                                                      (Quan.Q1)
                                                                                      (Term.Var 3)
                                                                                      (Term.Lab
                                                                                        "()")))))
                                                                              (Term.Lab "()")))
                                                                          (Term.Tup
                                                                            (Quan.Q1)
                                                                            (Term.Var 0)
                                                                            (Term.Lab "()"))))
                                                                      (Term.Lab "()")))
                                                                  (Term.Efq))
                                                                (Term.Efq))
                                                              (Term.Efq))))
                                                        (Term.Efq))))
                                                  (Term.Lam
                                                    (Quan.Q1)
                                                    (Term.Lam
                                                      (Quan.Q1)
                                                      (Term.Prj
                                                        (Term.Lam
                                                          (Quan.Q1)
                                                          (Term.Mat
                                                            "()"
                                                            (Term.Mat
                                                              "()"
                                                              (Term.Mat
                                                                "()"
                                                                (Term.Tup
                                                                  (Quan.Q1)
                                                                  (Term.Lab "None")
                                                                  (Term.Lab "()"))
                                                                (Term.Efq))
                                                              (Term.Efq))
                                                            (Term.Efq)))))))))
                                            (Term.Lam
                                              (Quan.Q1)
                                              (Term.Lam
                                                (Quan.Q1)
                                                (Term.Mat
                                                  "()"
                                                  (Term.Mat
                                                    "()"
                                                    (Term.Tup
                                                      (Quan.Q1)
                                                      (Term.Lab "None")
                                                      (Term.Lab "()"))
                                                    (Term.Efq))
                                                  (Term.Efq)))))))
                                      (Term.Efq))))
                                (Term.Lam
                                  (Quan.Q1)
                                  (Term.Lam
                                    (Quan.Q1)
                                    (Term.Prj
                                      (Term.Lam
                                        (Quan.Q1)
                                        (Term.Mat
                                          "()"
                                          (Term.Mat
                                            "()"
                                            (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                                            (Term.Efq))
                                          (Term.Efq)))))))))
                          (Term.Lam
                            (Quan.Q1)
                            (Term.Lam
                              (Quan.Q1)
                              (Term.Mat
                                "()"
                                (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                                (Term.Efq)))))))
                    (Term.Efq))))
              (Term.Lam
                (Quan.Q1)
                (Term.Lam
                  (Quan.Q1)
                  (Term.Prj
                    (Term.Lam
                      (Quan.Q1)
                      (Term.Mat
                        "()"
                        (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                        (Term.Efq)))))))))
        (Term.Lam
          (Quan.Q1)
          (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))))),
    false⟩

def «reader.Book.read.prj» : Def :=
  ⟨"Book.read.prj",
    Term.All
      (Quan.Q1)
      (Term.App (Quan.Q0) (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "Item"))
      (Term.App
        (Quan.Q0)
        (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
          (Term.Ref "Item"))),
    Term.Prj
      (Term.Mat
        "Con"
        (Term.Prj
          (Term.Prj
            (Term.Mat
              "Item.term"
              (Term.Prj
                (Term.Lam
                  (Quan.Q1)
                  (Term.Mat
                    "()"
                    (Term.Prj
                      (Term.Lam
                        (Quan.Q1)
                        (Term.Mat
                          "()"
                          (Term.Tup
                            (Quan.Q1)
                            (Term.Lab "Some")
                            (Term.Tup
                              (Quan.Q1)
                              (Term.Tup
                                (Quan.Q1)
                                (Term.Lab "Con")
                                (Term.Tup
                                  (Quan.Q1)
                                  (Term.Tup
                                    (Quan.Q1)
                                    (Term.Lab "Item.term")
                                    (Term.Tup
                                      (Quan.Q1)
                                      (Term.Tup
                                        (Quan.Q1)
                                        (Term.Lab "Term.Prj")
                                        (Term.Tup (Quan.Q1) (Term.Var 1) (Term.Lab "()")))
                                      (Term.Lab "()")))
                                  (Term.Tup (Quan.Q1) (Term.Var 0) (Term.Lab "()"))))
                              (Term.Lab "()")))
                          (Term.Efq))))
                    (Term.Efq))))
              (Term.Lam
                (Quan.Q1)
                (Term.Lam
                  (Quan.Q1)
                  (Term.Prj
                    (Term.Lam
                      (Quan.Q1)
                      (Term.Mat
                        "()"
                        (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                        (Term.Efq)))))))))
        (Term.Lam
          (Quan.Q1)
          (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))))),
    false⟩

def «reader.Book.read.enu» : Def :=
  ⟨"Book.read.enu",
    Term.All
      (Quan.Q1)
      (Term.App (Quan.Q0) (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "Item"))
      (Term.App
        (Quan.Q0)
        (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
          (Term.Ref "Item"))),
    Term.Prj
      (Term.Mat
        "Con"
        (Term.Prj
          (Term.Prj
            (Term.Mat
              "Item.names"
              (Term.Prj
                (Term.Lam
                  (Quan.Q1)
                  (Term.Mat
                    "()"
                    (Term.Prj
                      (Term.Lam
                        (Quan.Q1)
                        (Term.Mat
                          "()"
                          (Term.Tup
                            (Quan.Q1)
                            (Term.Lab "Some")
                            (Term.Tup
                              (Quan.Q1)
                              (Term.Tup
                                (Quan.Q1)
                                (Term.Lab "Con")
                                (Term.Tup
                                  (Quan.Q1)
                                  (Term.Tup
                                    (Quan.Q1)
                                    (Term.Lab "Item.term")
                                    (Term.Tup
                                      (Quan.Q1)
                                      (Term.Tup
                                        (Quan.Q1)
                                        (Term.Lab "Term.Enu")
                                        (Term.Tup (Quan.Q1) (Term.Var 1) (Term.Lab "()")))
                                      (Term.Lab "()")))
                                  (Term.Tup (Quan.Q1) (Term.Var 0) (Term.Lab "()"))))
                              (Term.Lab "()")))
                          (Term.Efq))))
                    (Term.Efq))))
              (Term.Lam
                (Quan.Q1)
                (Term.Lam
                  (Quan.Q1)
                  (Term.Prj
                    (Term.Lam
                      (Quan.Q1)
                      (Term.Mat
                        "()"
                        (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                        (Term.Efq)))))))))
        (Term.Lam
          (Quan.Q1)
          (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))))),
    false⟩

def «reader.Book.read.lab» : Def :=
  ⟨"Book.read.lab",
    Term.All
      (Quan.Q1)
      (Term.App (Quan.Q0) (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "Item"))
      (Term.App
        (Quan.Q0)
        (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
          (Term.Ref "Item"))),
    Term.Prj
      (Term.Mat
        "Con"
        (Term.Prj
          (Term.Prj
            (Term.Mat
              "Item.name"
              (Term.Prj
                (Term.Lam
                  (Quan.Q1)
                  (Term.Mat
                    "()"
                    (Term.Prj
                      (Term.Lam
                        (Quan.Q1)
                        (Term.Mat
                          "()"
                          (Term.Tup
                            (Quan.Q1)
                            (Term.Lab "Some")
                            (Term.Tup
                              (Quan.Q1)
                              (Term.Tup
                                (Quan.Q1)
                                (Term.Lab "Con")
                                (Term.Tup
                                  (Quan.Q1)
                                  (Term.Tup
                                    (Quan.Q1)
                                    (Term.Lab "Item.term")
                                    (Term.Tup
                                      (Quan.Q1)
                                      (Term.Tup
                                        (Quan.Q1)
                                        (Term.Lab "Term.Lab")
                                        (Term.Tup (Quan.Q1) (Term.Var 1) (Term.Lab "()")))
                                      (Term.Lab "()")))
                                  (Term.Tup (Quan.Q1) (Term.Var 0) (Term.Lab "()"))))
                              (Term.Lab "()")))
                          (Term.Efq))))
                    (Term.Efq))))
              (Term.Lam
                (Quan.Q1)
                (Term.Lam
                  (Quan.Q1)
                  (Term.Prj
                    (Term.Lam
                      (Quan.Q1)
                      (Term.Mat
                        "()"
                        (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                        (Term.Efq)))))))))
        (Term.Lam
          (Quan.Q1)
          (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))))),
    false⟩

def «reader.Book.read.mat» : Def :=
  ⟨"Book.read.mat",
    Term.All
      (Quan.Q1)
      (Term.App (Quan.Q0) (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "Item"))
      (Term.App
        (Quan.Q0)
        (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
          (Term.Ref "Item"))),
    Term.Prj
      (Term.Mat
        "Con"
        (Term.Prj
          (Term.Prj
            (Term.Mat
              "Item.term"
              (Term.Prj
                (Term.Lam
                  (Quan.Q1)
                  (Term.Mat
                    "()"
                    (Term.Prj
                      (Term.Prj
                        (Term.Mat
                          "Con"
                          (Term.Prj
                            (Term.Prj
                              (Term.Mat
                                "Item.term"
                                (Term.Prj
                                  (Term.Lam
                                    (Quan.Q1)
                                    (Term.Mat
                                      "()"
                                      (Term.Prj
                                        (Term.Prj
                                          (Term.Mat
                                            "Con"
                                            (Term.Prj
                                              (Term.Prj
                                                (Term.Mat
                                                  "Item.name"
                                                  (Term.Prj
                                                    (Term.Lam
                                                      (Quan.Q1)
                                                      (Term.Mat
                                                        "()"
                                                        (Term.Prj
                                                          (Term.Lam
                                                            (Quan.Q1)
                                                            (Term.Mat
                                                              "()"
                                                              (Term.Mat
                                                                "()"
                                                                (Term.Mat
                                                                  "()"
                                                                  (Term.Tup
                                                                    (Quan.Q1)
                                                                    (Term.Lab "Some")
                                                                    (Term.Tup
                                                                      (Quan.Q1)
                                                                      (Term.Tup
                                                                        (Quan.Q1)
                                                                        (Term.Lab "Con")
                                                                        (Term.Tup
                                                                          (Quan.Q1)
                                                                          (Term.Tup
                                                                            (Quan.Q1)
                                                                            (Term.Lab "Item.term")
                                                                            (Term.Tup
                                                                              (Quan.Q1)
                                                                              (Term.Tup
                                                                                (Quan.Q1)
                                                                                (Term.Lab
                                                                                  "Term.Mat")
                                                                                (Term.Tup
                                                                                  (Quan.Q1)
                                                                                  (Term.Var 1)
                                                                                  (Term.Tup
                                                                                    (Quan.Q1)
                                                                                    (Term.Var 2)
                                                                                    (Term.Tup
                                                                                      (Quan.Q1)
                                                                                      (Term.Var 3)
                                                                                      (Term.Lab
                                                                                        "()")))))
                                                                              (Term.Lab "()")))
                                                                          (Term.Tup
                                                                            (Quan.Q1)
                                                                            (Term.Var 0)
                                                                            (Term.Lab "()"))))
                                                                      (Term.Lab "()")))
                                                                  (Term.Efq))
                                                                (Term.Efq))
                                                              (Term.Efq))))
                                                        (Term.Efq))))
                                                  (Term.Lam
                                                    (Quan.Q1)
                                                    (Term.Lam
                                                      (Quan.Q1)
                                                      (Term.Prj
                                                        (Term.Lam
                                                          (Quan.Q1)
                                                          (Term.Mat
                                                            "()"
                                                            (Term.Mat
                                                              "()"
                                                              (Term.Mat
                                                                "()"
                                                                (Term.Tup
                                                                  (Quan.Q1)
                                                                  (Term.Lab "None")
                                                                  (Term.Lab "()"))
                                                                (Term.Efq))
                                                              (Term.Efq))
                                                            (Term.Efq)))))))))
                                            (Term.Lam
                                              (Quan.Q1)
                                              (Term.Lam
                                                (Quan.Q1)
                                                (Term.Mat
                                                  "()"
                                                  (Term.Mat
                                                    "()"
                                                    (Term.Tup
                                                      (Quan.Q1)
                                                      (Term.Lab "None")
                                                      (Term.Lab "()"))
                                                    (Term.Efq))
                                                  (Term.Efq)))))))
                                      (Term.Efq))))
                                (Term.Lam
                                  (Quan.Q1)
                                  (Term.Lam
                                    (Quan.Q1)
                                    (Term.Prj
                                      (Term.Lam
                                        (Quan.Q1)
                                        (Term.Mat
                                          "()"
                                          (Term.Mat
                                            "()"
                                            (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                                            (Term.Efq))
                                          (Term.Efq)))))))))
                          (Term.Lam
                            (Quan.Q1)
                            (Term.Lam
                              (Quan.Q1)
                              (Term.Mat
                                "()"
                                (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                                (Term.Efq)))))))
                    (Term.Efq))))
              (Term.Lam
                (Quan.Q1)
                (Term.Lam
                  (Quan.Q1)
                  (Term.Prj
                    (Term.Lam
                      (Quan.Q1)
                      (Term.Mat
                        "()"
                        (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                        (Term.Efq)))))))))
        (Term.Lam
          (Quan.Q1)
          (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))))),
    false⟩

def «reader.Book.read.eql» : Def :=
  ⟨"Book.read.eql",
    Term.All
      (Quan.Q1)
      (Term.App (Quan.Q0) (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "Item"))
      (Term.App
        (Quan.Q0)
        (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
          (Term.Ref "Item"))),
    Term.Prj
      (Term.Mat
        "Con"
        (Term.Prj
          (Term.Prj
            (Term.Mat
              "Item.term"
              (Term.Prj
                (Term.Lam
                  (Quan.Q1)
                  (Term.Mat
                    "()"
                    (Term.Prj
                      (Term.Prj
                        (Term.Mat
                          "Con"
                          (Term.Prj
                            (Term.Prj
                              (Term.Mat
                                "Item.term"
                                (Term.Prj
                                  (Term.Lam
                                    (Quan.Q1)
                                    (Term.Mat
                                      "()"
                                      (Term.Prj
                                        (Term.Prj
                                          (Term.Mat
                                            "Con"
                                            (Term.Prj
                                              (Term.Prj
                                                (Term.Mat
                                                  "Item.term"
                                                  (Term.Prj
                                                    (Term.Lam
                                                      (Quan.Q1)
                                                      (Term.Mat
                                                        "()"
                                                        (Term.Prj
                                                          (Term.Lam
                                                            (Quan.Q1)
                                                            (Term.Mat
                                                              "()"
                                                              (Term.Mat
                                                                "()"
                                                                (Term.Mat
                                                                  "()"
                                                                  (Term.Tup
                                                                    (Quan.Q1)
                                                                    (Term.Lab "Some")
                                                                    (Term.Tup
                                                                      (Quan.Q1)
                                                                      (Term.Tup
                                                                        (Quan.Q1)
                                                                        (Term.Lab "Con")
                                                                        (Term.Tup
                                                                          (Quan.Q1)
                                                                          (Term.Tup
                                                                            (Quan.Q1)
                                                                            (Term.Lab "Item.term")
                                                                            (Term.Tup
                                                                              (Quan.Q1)
                                                                              (Term.Tup
                                                                                (Quan.Q1)
                                                                                (Term.Lab
                                                                                  "Term.Eql")
                                                                                (Term.Tup
                                                                                  (Quan.Q1)
                                                                                  (Term.Var 1)
                                                                                  (Term.Tup
                                                                                    (Quan.Q1)
                                                                                    (Term.Var 2)
                                                                                    (Term.Tup
                                                                                      (Quan.Q1)
                                                                                      (Term.Var 3)
                                                                                      (Term.Lab
                                                                                        "()")))))
                                                                              (Term.Lab "()")))
                                                                          (Term.Tup
                                                                            (Quan.Q1)
                                                                            (Term.Var 0)
                                                                            (Term.Lab "()"))))
                                                                      (Term.Lab "()")))
                                                                  (Term.Efq))
                                                                (Term.Efq))
                                                              (Term.Efq))))
                                                        (Term.Efq))))
                                                  (Term.Lam
                                                    (Quan.Q1)
                                                    (Term.Lam
                                                      (Quan.Q1)
                                                      (Term.Prj
                                                        (Term.Lam
                                                          (Quan.Q1)
                                                          (Term.Mat
                                                            "()"
                                                            (Term.Mat
                                                              "()"
                                                              (Term.Mat
                                                                "()"
                                                                (Term.Tup
                                                                  (Quan.Q1)
                                                                  (Term.Lab "None")
                                                                  (Term.Lab "()"))
                                                                (Term.Efq))
                                                              (Term.Efq))
                                                            (Term.Efq)))))))))
                                            (Term.Lam
                                              (Quan.Q1)
                                              (Term.Lam
                                                (Quan.Q1)
                                                (Term.Mat
                                                  "()"
                                                  (Term.Mat
                                                    "()"
                                                    (Term.Tup
                                                      (Quan.Q1)
                                                      (Term.Lab "None")
                                                      (Term.Lab "()"))
                                                    (Term.Efq))
                                                  (Term.Efq)))))))
                                      (Term.Efq))))
                                (Term.Lam
                                  (Quan.Q1)
                                  (Term.Lam
                                    (Quan.Q1)
                                    (Term.Prj
                                      (Term.Lam
                                        (Quan.Q1)
                                        (Term.Mat
                                          "()"
                                          (Term.Mat
                                            "()"
                                            (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                                            (Term.Efq))
                                          (Term.Efq)))))))))
                          (Term.Lam
                            (Quan.Q1)
                            (Term.Lam
                              (Quan.Q1)
                              (Term.Mat
                                "()"
                                (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                                (Term.Efq)))))))
                    (Term.Efq))))
              (Term.Lam
                (Quan.Q1)
                (Term.Lam
                  (Quan.Q1)
                  (Term.Prj
                    (Term.Lam
                      (Quan.Q1)
                      (Term.Mat
                        "()"
                        (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                        (Term.Efq)))))))))
        (Term.Lam
          (Quan.Q1)
          (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))))),
    false⟩

def «reader.Book.read.rwt» : Def :=
  ⟨"Book.read.rwt",
    Term.All
      (Quan.Q1)
      (Term.App (Quan.Q0) (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "Item"))
      (Term.App
        (Quan.Q0)
        (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
          (Term.Ref "Item"))),
    Term.Prj
      (Term.Mat
        "Con"
        (Term.Prj
          (Term.Prj
            (Term.Mat
              "Item.term"
              (Term.Prj
                (Term.Lam
                  (Quan.Q1)
                  (Term.Mat
                    "()"
                    (Term.Prj
                      (Term.Prj
                        (Term.Mat
                          "Con"
                          (Term.Prj
                            (Term.Prj
                              (Term.Mat
                                "Item.term"
                                (Term.Prj
                                  (Term.Lam
                                    (Quan.Q1)
                                    (Term.Mat
                                      "()"
                                      (Term.Prj
                                        (Term.Prj
                                          (Term.Mat
                                            "Con"
                                            (Term.Prj
                                              (Term.Prj
                                                (Term.Mat
                                                  "Item.term"
                                                  (Term.Prj
                                                    (Term.Lam
                                                      (Quan.Q1)
                                                      (Term.Mat
                                                        "()"
                                                        (Term.Prj
                                                          (Term.Lam
                                                            (Quan.Q1)
                                                            (Term.Mat
                                                              "()"
                                                              (Term.Mat
                                                                "()"
                                                                (Term.Mat
                                                                  "()"
                                                                  (Term.Tup
                                                                    (Quan.Q1)
                                                                    (Term.Lab "Some")
                                                                    (Term.Tup
                                                                      (Quan.Q1)
                                                                      (Term.Tup
                                                                        (Quan.Q1)
                                                                        (Term.Lab "Con")
                                                                        (Term.Tup
                                                                          (Quan.Q1)
                                                                          (Term.Tup
                                                                            (Quan.Q1)
                                                                            (Term.Lab "Item.term")
                                                                            (Term.Tup
                                                                              (Quan.Q1)
                                                                              (Term.Tup
                                                                                (Quan.Q1)
                                                                                (Term.Lab
                                                                                  "Term.Rwt")
                                                                                (Term.Tup
                                                                                  (Quan.Q1)
                                                                                  (Term.Var 1)
                                                                                  (Term.Tup
                                                                                    (Quan.Q1)
                                                                                    (Term.Var 2)
                                                                                    (Term.Tup
                                                                                      (Quan.Q1)
                                                                                      (Term.Var 3)
                                                                                      (Term.Lab
                                                                                        "()")))))
                                                                              (Term.Lab "()")))
                                                                          (Term.Tup
                                                                            (Quan.Q1)
                                                                            (Term.Var 0)
                                                                            (Term.Lab "()"))))
                                                                      (Term.Lab "()")))
                                                                  (Term.Efq))
                                                                (Term.Efq))
                                                              (Term.Efq))))
                                                        (Term.Efq))))
                                                  (Term.Lam
                                                    (Quan.Q1)
                                                    (Term.Lam
                                                      (Quan.Q1)
                                                      (Term.Prj
                                                        (Term.Lam
                                                          (Quan.Q1)
                                                          (Term.Mat
                                                            "()"
                                                            (Term.Mat
                                                              "()"
                                                              (Term.Mat
                                                                "()"
                                                                (Term.Tup
                                                                  (Quan.Q1)
                                                                  (Term.Lab "None")
                                                                  (Term.Lab "()"))
                                                                (Term.Efq))
                                                              (Term.Efq))
                                                            (Term.Efq)))))))))
                                            (Term.Lam
                                              (Quan.Q1)
                                              (Term.Lam
                                                (Quan.Q1)
                                                (Term.Mat
                                                  "()"
                                                  (Term.Mat
                                                    "()"
                                                    (Term.Tup
                                                      (Quan.Q1)
                                                      (Term.Lab "None")
                                                      (Term.Lab "()"))
                                                    (Term.Efq))
                                                  (Term.Efq)))))))
                                      (Term.Efq))))
                                (Term.Lam
                                  (Quan.Q1)
                                  (Term.Lam
                                    (Quan.Q1)
                                    (Term.Prj
                                      (Term.Lam
                                        (Quan.Q1)
                                        (Term.Mat
                                          "()"
                                          (Term.Mat
                                            "()"
                                            (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                                            (Term.Efq))
                                          (Term.Efq)))))))))
                          (Term.Lam
                            (Quan.Q1)
                            (Term.Lam
                              (Quan.Q1)
                              (Term.Mat
                                "()"
                                (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                                (Term.Efq)))))))
                    (Term.Efq))))
              (Term.Lam
                (Quan.Q1)
                (Term.Lam
                  (Quan.Q1)
                  (Term.Prj
                    (Term.Lam
                      (Quan.Q1)
                      (Term.Mat
                        "()"
                        (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                        (Term.Efq)))))))))
        (Term.Lam
          (Quan.Q1)
          (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))))),
    false⟩

def «reader.Book.read.token32» : Def :=
  ⟨"Book.read.token32",
    Term.All
      (Quan.Q1)
      (Term.Ref "Nat")
      (Term.All
        (Quan.Q1)
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
          (Term.Ref "Item"))
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
          (Term.App
            (Quan.Q0)
            (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
            (Term.Ref "Item")))),
    Term.Prj
      (Term.Mat
        "Zero"
        (Term.Mat
          "()"
          (Term.Lam (Quan.Q1) (Term.App (Quan.Q1) (Term.Ref "Book.read.rwt") (Term.Var 0)))
          (Term.Efq))
        (Term.Mat
          "Succ"
          (Term.Prj
            (Term.Lam
              (Quan.Q1)
              (Term.Mat
                "()"
                (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()")))
                (Term.Efq))))
          (Term.Efq))),
    false⟩

def «reader.Book.read.token24» : Def :=
  ⟨"Book.read.token24",
    Term.All
      (Quan.Q1)
      (Term.Ref "Nat")
      (Term.All
        (Quan.Q1)
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
          (Term.Ref "Item"))
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
          (Term.App
            (Quan.Q0)
            (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
            (Term.Ref "Item")))),
    Term.Prj
      (Term.Mat
        "Zero"
        (Term.Mat
          "()"
          (Term.Lam (Quan.Q1) (Term.App (Quan.Q1) (Term.Ref "Book.read.tup") (Term.Var 0)))
          (Term.Efq))
        (Term.Mat
          "Succ"
          (Term.Prj
            (Term.Prj
              (Term.Mat
                "Zero"
                (Term.Mat
                  "()"
                  (Term.Mat
                    "()"
                    (Term.Lam
                      (Quan.Q1)
                      (Term.App (Quan.Q1) (Term.Ref "Book.read.prj") (Term.Var 0)))
                    (Term.Efq))
                  (Term.Efq))
                (Term.Mat
                  "Succ"
                  (Term.Prj
                    (Term.Prj
                      (Term.Mat
                        "Zero"
                        (Term.Mat
                          "()"
                          (Term.Mat
                            "()"
                            (Term.Mat
                              "()"
                              (Term.Lam
                                (Quan.Q1)
                                (Term.App (Quan.Q1) (Term.Ref "Book.read.enu") (Term.Var 0)))
                              (Term.Efq))
                            (Term.Efq))
                          (Term.Efq))
                        (Term.Mat
                          "Succ"
                          (Term.Prj
                            (Term.Prj
                              (Term.Mat
                                "Zero"
                                (Term.Mat
                                  "()"
                                  (Term.Mat
                                    "()"
                                    (Term.Mat
                                      "()"
                                      (Term.Mat
                                        "()"
                                        (Term.Lam
                                          (Quan.Q1)
                                          (Term.App
                                            (Quan.Q1)
                                            (Term.Ref "Book.read.lab")
                                            (Term.Var 0)))
                                        (Term.Efq))
                                      (Term.Efq))
                                    (Term.Efq))
                                  (Term.Efq))
                                (Term.Mat
                                  "Succ"
                                  (Term.Prj
                                    (Term.Prj
                                      (Term.Mat
                                        "Zero"
                                        (Term.Mat
                                          "()"
                                          (Term.Mat
                                            "()"
                                            (Term.Mat
                                              "()"
                                              (Term.Mat
                                                "()"
                                                (Term.Mat
                                                  "()"
                                                  (Term.Lam
                                                    (Quan.Q1)
                                                    (Term.App
                                                      (Quan.Q1)
                                                      (Term.Ref "Book.read.mat")
                                                      (Term.Var 0)))
                                                  (Term.Efq))
                                                (Term.Efq))
                                              (Term.Efq))
                                            (Term.Efq))
                                          (Term.Efq))
                                        (Term.Mat
                                          "Succ"
                                          (Term.Prj
                                            (Term.Prj
                                              (Term.Mat
                                                "Zero"
                                                (Term.Mat
                                                  "()"
                                                  (Term.Mat
                                                    "()"
                                                    (Term.Mat
                                                      "()"
                                                      (Term.Mat
                                                        "()"
                                                        (Term.Mat
                                                          "()"
                                                          (Term.Mat
                                                            "()"
                                                            (Term.Lam
                                                              (Quan.Q1)
                                                              (Term.Tup
                                                                (Quan.Q1)
                                                                (Term.Lab "Some")
                                                                (Term.Tup
                                                                  (Quan.Q1)
                                                                  (Term.Tup
                                                                    (Quan.Q1)
                                                                    (Term.Lab "Con")
                                                                    (Term.Tup
                                                                      (Quan.Q1)
                                                                      (Term.Tup
                                                                        (Quan.Q1)
                                                                        (Term.Lab "Item.term")
                                                                        (Term.Tup
                                                                          (Quan.Q1)
                                                                          (Term.Tup
                                                                            (Quan.Q1)
                                                                            (Term.Lab "Term.Efq")
                                                                            (Term.Lab "()"))
                                                                          (Term.Lab "()")))
                                                                      (Term.Tup
                                                                        (Quan.Q1)
                                                                        (Term.Var 0)
                                                                        (Term.Lab "()"))))
                                                                  (Term.Lab "()"))))
                                                            (Term.Efq))
                                                          (Term.Efq))
                                                        (Term.Efq))
                                                      (Term.Efq))
                                                    (Term.Efq))
                                                  (Term.Efq))
                                                (Term.Mat
                                                  "Succ"
                                                  (Term.Prj
                                                    (Term.Prj
                                                      (Term.Mat
                                                        "Zero"
                                                        (Term.Mat
                                                          "()"
                                                          (Term.Mat
                                                            "()"
                                                            (Term.Mat
                                                              "()"
                                                              (Term.Mat
                                                                "()"
                                                                (Term.Mat
                                                                  "()"
                                                                  (Term.Mat
                                                                    "()"
                                                                    (Term.Mat
                                                                      "()"
                                                                      (Term.Lam
                                                                        (Quan.Q1)
                                                                        (Term.App
                                                                          (Quan.Q1)
                                                                          (Term.Ref "Book.read.eql")
                                                                          (Term.Var 0)))
                                                                      (Term.Efq))
                                                                    (Term.Efq))
                                                                  (Term.Efq))
                                                                (Term.Efq))
                                                              (Term.Efq))
                                                            (Term.Efq))
                                                          (Term.Efq))
                                                        (Term.Mat
                                                          "Succ"
                                                          (Term.Prj
                                                            (Term.Prj
                                                              (Term.Mat
                                                                "Zero"
                                                                (Term.Mat
                                                                  "()"
                                                                  (Term.Mat
                                                                    "()"
                                                                    (Term.Mat
                                                                      "()"
                                                                      (Term.Mat
                                                                        "()"
                                                                        (Term.Mat
                                                                          "()"
                                                                          (Term.Mat
                                                                            "()"
                                                                            (Term.Mat
                                                                              "()"
                                                                              (Term.Mat
                                                                                "()"
                                                                                (Term.Lam
                                                                                  (Quan.Q1)
                                                                                  (Term.Tup
                                                                                    (Quan.Q1)
                                                                                    (Term.Lab
                                                                                      "Some")
                                                                                    (Term.Tup
                                                                                      (Quan.Q1)
                                                                                      (Term.Tup
                                                                                        (Quan.Q1)
                                                                                        (Term.Lab
                                                                                          "Con")
                                                                                        (Term.Tup
                                                                                          (Quan.Q1)
                                                                                          (Term.Tup
                                                                                            (Quan.Q1)
                                                                                            (Term.Lab
                                                                                              "Item.term")
                                                                                            (Term.Tup
                                                                                              (Quan.Q1)
                                                                                              (Term.Tup
                                                                                                (Quan.Q1)
                                                                                                (Term.Lab
                                                                                                  "Term.Rfl")
                                                                                                (Term.Lab
                                                                                                  "()"))
                                                                                              (Term.Lab
                                                                                                "()")))
                                                                                          (Term.Tup
                                                                                            (Quan.Q1)
                                                                                            (Term.Var
                                                                                              0)
                                                                                            (Term.Lab
                                                                                              "()"))))
                                                                                      (Term.Lab
                                                                                        "()"))))
                                                                                (Term.Efq))
                                                                              (Term.Efq))
                                                                            (Term.Efq))
                                                                          (Term.Efq))
                                                                        (Term.Efq))
                                                                      (Term.Efq))
                                                                    (Term.Efq))
                                                                  (Term.Efq))
                                                                (Term.Mat
                                                                  "Succ"
                                                                  (Term.Prj
                                                                    (Term.Lam
                                                                      (Quan.Q1)
                                                                      (Term.Mat
                                                                        "()"
                                                                        (Term.Mat
                                                                          "()"
                                                                          (Term.Mat
                                                                            "()"
                                                                            (Term.Mat
                                                                              "()"
                                                                              (Term.Mat
                                                                                "()"
                                                                                (Term.Mat
                                                                                  "()"
                                                                                  (Term.Mat
                                                                                    "()"
                                                                                    (Term.Mat
                                                                                      "()"
                                                                                      (Term.Lam
                                                                                        (Quan.Q1)
                                                                                        (Term.App
                                                                                          (Quan.Q1)
                                                                                          (Term.App
                                                                                            (Quan.Q1)
                                                                                            (Term.Ref
                                                                                              "Book.read.token32")
                                                                                            (Term.Var
                                                                                              1))
                                                                                          (Term.Var
                                                                                            0)))
                                                                                      (Term.Efq))
                                                                                    (Term.Efq))
                                                                                  (Term.Efq))
                                                                                (Term.Efq))
                                                                              (Term.Efq))
                                                                            (Term.Efq))
                                                                          (Term.Efq))
                                                                        (Term.Efq))))
                                                                  (Term.Efq)))))
                                                          (Term.Efq)))))
                                                  (Term.Efq)))))
                                          (Term.Efq)))))
                                  (Term.Efq)))))
                          (Term.Efq)))))
                  (Term.Efq)))))
          (Term.Efq))),
    false⟩

def «reader.Book.read.token16» : Def :=
  ⟨"Book.read.token16",
    Term.All
      (Quan.Q1)
      (Term.Ref "Nat")
      (Term.All
        (Quan.Q1)
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
          (Term.Ref "Item"))
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
          (Term.App
            (Quan.Q0)
            (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
            (Term.Ref "Item")))),
    Term.Prj
      (Term.Mat
        "Zero"
        (Term.Mat
          "()"
          (Term.Lam (Quan.Q1) (Term.App (Quan.Q1) (Term.Ref "Book.read.ann") (Term.Var 0)))
          (Term.Efq))
        (Term.Mat
          "Succ"
          (Term.Prj
            (Term.Prj
              (Term.Mat
                "Zero"
                (Term.Mat
                  "()"
                  (Term.Mat
                    "()"
                    (Term.Lam
                      (Quan.Q1)
                      (Term.App (Quan.Q1) (Term.Ref "Book.read.let") (Term.Var 0)))
                    (Term.Efq))
                  (Term.Efq))
                (Term.Mat
                  "Succ"
                  (Term.Prj
                    (Term.Prj
                      (Term.Mat
                        "Zero"
                        (Term.Mat
                          "()"
                          (Term.Mat
                            "()"
                            (Term.Mat
                              "()"
                              (Term.Lam
                                (Quan.Q1)
                                (Term.App (Quan.Q1) (Term.Ref "Book.read.typ") (Term.Var 0)))
                              (Term.Efq))
                            (Term.Efq))
                          (Term.Efq))
                        (Term.Mat
                          "Succ"
                          (Term.Prj
                            (Term.Prj
                              (Term.Mat
                                "Zero"
                                (Term.Mat
                                  "()"
                                  (Term.Mat
                                    "()"
                                    (Term.Mat
                                      "()"
                                      (Term.Mat
                                        "()"
                                        (Term.Lam
                                          (Quan.Q1)
                                          (Term.App
                                            (Quan.Q1)
                                            (Term.Ref "Book.read.min")
                                            (Term.Var 0)))
                                        (Term.Efq))
                                      (Term.Efq))
                                    (Term.Efq))
                                  (Term.Efq))
                                (Term.Mat
                                  "Succ"
                                  (Term.Prj
                                    (Term.Prj
                                      (Term.Mat
                                        "Zero"
                                        (Term.Mat
                                          "()"
                                          (Term.Mat
                                            "()"
                                            (Term.Mat
                                              "()"
                                              (Term.Mat
                                                "()"
                                                (Term.Mat
                                                  "()"
                                                  (Term.Lam
                                                    (Quan.Q1)
                                                    (Term.App
                                                      (Quan.Q1)
                                                      (Term.Ref "Book.read.all")
                                                      (Term.Var 0)))
                                                  (Term.Efq))
                                                (Term.Efq))
                                              (Term.Efq))
                                            (Term.Efq))
                                          (Term.Efq))
                                        (Term.Mat
                                          "Succ"
                                          (Term.Prj
                                            (Term.Prj
                                              (Term.Mat
                                                "Zero"
                                                (Term.Mat
                                                  "()"
                                                  (Term.Mat
                                                    "()"
                                                    (Term.Mat
                                                      "()"
                                                      (Term.Mat
                                                        "()"
                                                        (Term.Mat
                                                          "()"
                                                          (Term.Mat
                                                            "()"
                                                            (Term.Lam
                                                              (Quan.Q1)
                                                              (Term.App
                                                                (Quan.Q1)
                                                                (Term.Ref "Book.read.lam")
                                                                (Term.Var 0)))
                                                            (Term.Efq))
                                                          (Term.Efq))
                                                        (Term.Efq))
                                                      (Term.Efq))
                                                    (Term.Efq))
                                                  (Term.Efq))
                                                (Term.Mat
                                                  "Succ"
                                                  (Term.Prj
                                                    (Term.Prj
                                                      (Term.Mat
                                                        "Zero"
                                                        (Term.Mat
                                                          "()"
                                                          (Term.Mat
                                                            "()"
                                                            (Term.Mat
                                                              "()"
                                                              (Term.Mat
                                                                "()"
                                                                (Term.Mat
                                                                  "()"
                                                                  (Term.Mat
                                                                    "()"
                                                                    (Term.Mat
                                                                      "()"
                                                                      (Term.Lam
                                                                        (Quan.Q1)
                                                                        (Term.App
                                                                          (Quan.Q1)
                                                                          (Term.Ref "Book.read.app")
                                                                          (Term.Var 0)))
                                                                      (Term.Efq))
                                                                    (Term.Efq))
                                                                  (Term.Efq))
                                                                (Term.Efq))
                                                              (Term.Efq))
                                                            (Term.Efq))
                                                          (Term.Efq))
                                                        (Term.Mat
                                                          "Succ"
                                                          (Term.Prj
                                                            (Term.Prj
                                                              (Term.Mat
                                                                "Zero"
                                                                (Term.Mat
                                                                  "()"
                                                                  (Term.Mat
                                                                    "()"
                                                                    (Term.Mat
                                                                      "()"
                                                                      (Term.Mat
                                                                        "()"
                                                                        (Term.Mat
                                                                          "()"
                                                                          (Term.Mat
                                                                            "()"
                                                                            (Term.Mat
                                                                              "()"
                                                                              (Term.Mat
                                                                                "()"
                                                                                (Term.Lam
                                                                                  (Quan.Q1)
                                                                                  (Term.App
                                                                                    (Quan.Q1)
                                                                                    (Term.Ref
                                                                                      "Book.read.sig")
                                                                                    (Term.Var 0)))
                                                                                (Term.Efq))
                                                                              (Term.Efq))
                                                                            (Term.Efq))
                                                                          (Term.Efq))
                                                                        (Term.Efq))
                                                                      (Term.Efq))
                                                                    (Term.Efq))
                                                                  (Term.Efq))
                                                                (Term.Mat
                                                                  "Succ"
                                                                  (Term.Prj
                                                                    (Term.Lam
                                                                      (Quan.Q1)
                                                                      (Term.Mat
                                                                        "()"
                                                                        (Term.Mat
                                                                          "()"
                                                                          (Term.Mat
                                                                            "()"
                                                                            (Term.Mat
                                                                              "()"
                                                                              (Term.Mat
                                                                                "()"
                                                                                (Term.Mat
                                                                                  "()"
                                                                                  (Term.Mat
                                                                                    "()"
                                                                                    (Term.Mat
                                                                                      "()"
                                                                                      (Term.Lam
                                                                                        (Quan.Q1)
                                                                                        (Term.App
                                                                                          (Quan.Q1)
                                                                                          (Term.App
                                                                                            (Quan.Q1)
                                                                                            (Term.Ref
                                                                                              "Book.read.token24")
                                                                                            (Term.Var
                                                                                              1))
                                                                                          (Term.Var
                                                                                            0)))
                                                                                      (Term.Efq))
                                                                                    (Term.Efq))
                                                                                  (Term.Efq))
                                                                                (Term.Efq))
                                                                              (Term.Efq))
                                                                            (Term.Efq))
                                                                          (Term.Efq))
                                                                        (Term.Efq))))
                                                                  (Term.Efq)))))
                                                          (Term.Efq)))))
                                                  (Term.Efq)))))
                                          (Term.Efq)))))
                                  (Term.Efq)))))
                          (Term.Efq)))))
                  (Term.Efq)))))
          (Term.Efq))),
    false⟩

def «reader.Book.read.token8» : Def :=
  ⟨"Book.read.token8",
    Term.All
      (Quan.Q1)
      (Term.Ref "Nat")
      (Term.All
        (Quan.Q1)
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
          (Term.Ref "Item"))
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
          (Term.App
            (Quan.Q0)
            (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
            (Term.Ref "Item")))),
    Term.Prj
      (Term.Mat
        "Zero"
        (Term.Mat
          "()"
          (Term.Lam (Quan.Q1) (Term.App (Quan.Q1) (Term.Ref "Book.read.names") (Term.Var 0)))
          (Term.Efq))
        (Term.Mat
          "Succ"
          (Term.Prj
            (Term.Prj
              (Term.Mat
                "Zero"
                (Term.Mat
                  "()"
                  (Term.Mat
                    "()"
                    (Term.Lam
                      (Quan.Q1)
                      (Term.Tup
                        (Quan.Q1)
                        (Term.Lab "Some")
                        (Term.Tup
                          (Quan.Q1)
                          (Term.Tup
                            (Quan.Q1)
                            (Term.Lab "Con")
                            (Term.Tup
                              (Quan.Q1)
                              (Term.Tup
                                (Quan.Q1)
                                (Term.Lab "Item.bool")
                                (Term.Tup
                                  (Quan.Q1)
                                  (Term.Tup (Quan.Q1) (Term.Lab "False") (Term.Lab "()"))
                                  (Term.Lab "()")))
                              (Term.Tup (Quan.Q1) (Term.Var 0) (Term.Lab "()"))))
                          (Term.Lab "()"))))
                    (Term.Efq))
                  (Term.Efq))
                (Term.Mat
                  "Succ"
                  (Term.Prj
                    (Term.Prj
                      (Term.Mat
                        "Zero"
                        (Term.Mat
                          "()"
                          (Term.Mat
                            "()"
                            (Term.Mat
                              "()"
                              (Term.Lam
                                (Quan.Q1)
                                (Term.Tup
                                  (Quan.Q1)
                                  (Term.Lab "Some")
                                  (Term.Tup
                                    (Quan.Q1)
                                    (Term.Tup
                                      (Quan.Q1)
                                      (Term.Lab "Con")
                                      (Term.Tup
                                        (Quan.Q1)
                                        (Term.Tup
                                          (Quan.Q1)
                                          (Term.Lab "Item.bool")
                                          (Term.Tup
                                            (Quan.Q1)
                                            (Term.Tup (Quan.Q1) (Term.Lab "True") (Term.Lab "()"))
                                            (Term.Lab "()")))
                                        (Term.Tup (Quan.Q1) (Term.Var 0) (Term.Lab "()"))))
                                    (Term.Lab "()"))))
                              (Term.Efq))
                            (Term.Efq))
                          (Term.Efq))
                        (Term.Mat
                          "Succ"
                          (Term.Prj
                            (Term.Prj
                              (Term.Mat
                                "Zero"
                                (Term.Mat
                                  "()"
                                  (Term.Mat
                                    "()"
                                    (Term.Mat
                                      "()"
                                      (Term.Mat
                                        "()"
                                        (Term.Lam
                                          (Quan.Q1)
                                          (Term.Tup
                                            (Quan.Q1)
                                            (Term.Lab "Some")
                                            (Term.Tup
                                              (Quan.Q1)
                                              (Term.Tup
                                                (Quan.Q1)
                                                (Term.Lab "Con")
                                                (Term.Tup
                                                  (Quan.Q1)
                                                  (Term.Tup
                                                    (Quan.Q1)
                                                    (Term.Lab "Item.defs")
                                                    (Term.Tup
                                                      (Quan.Q1)
                                                      (Term.Tup
                                                        (Quan.Q1)
                                                        (Term.Lab "Nil")
                                                        (Term.Lab "()"))
                                                      (Term.Lab "()")))
                                                  (Term.Tup
                                                    (Quan.Q1)
                                                    (Term.Var 0)
                                                    (Term.Lab "()"))))
                                              (Term.Lab "()"))))
                                        (Term.Efq))
                                      (Term.Efq))
                                    (Term.Efq))
                                  (Term.Efq))
                                (Term.Mat
                                  "Succ"
                                  (Term.Prj
                                    (Term.Prj
                                      (Term.Mat
                                        "Zero"
                                        (Term.Mat
                                          "()"
                                          (Term.Mat
                                            "()"
                                            (Term.Mat
                                              "()"
                                              (Term.Mat
                                                "()"
                                                (Term.Mat
                                                  "()"
                                                  (Term.Lam
                                                    (Quan.Q1)
                                                    (Term.App
                                                      (Quan.Q1)
                                                      (Term.Ref "Book.read.defs")
                                                      (Term.Var 0)))
                                                  (Term.Efq))
                                                (Term.Efq))
                                              (Term.Efq))
                                            (Term.Efq))
                                          (Term.Efq))
                                        (Term.Mat
                                          "Succ"
                                          (Term.Prj
                                            (Term.Prj
                                              (Term.Mat
                                                "Zero"
                                                (Term.Mat
                                                  "()"
                                                  (Term.Mat
                                                    "()"
                                                    (Term.Mat
                                                      "()"
                                                      (Term.Mat
                                                        "()"
                                                        (Term.Mat
                                                          "()"
                                                          (Term.Mat
                                                            "()"
                                                            (Term.Lam
                                                              (Quan.Q1)
                                                              (Term.App
                                                                (Quan.Q1)
                                                                (Term.Ref "Book.read.def")
                                                                (Term.Var 0)))
                                                            (Term.Efq))
                                                          (Term.Efq))
                                                        (Term.Efq))
                                                      (Term.Efq))
                                                    (Term.Efq))
                                                  (Term.Efq))
                                                (Term.Mat
                                                  "Succ"
                                                  (Term.Prj
                                                    (Term.Prj
                                                      (Term.Mat
                                                        "Zero"
                                                        (Term.Mat
                                                          "()"
                                                          (Term.Mat
                                                            "()"
                                                            (Term.Mat
                                                              "()"
                                                              (Term.Mat
                                                                "()"
                                                                (Term.Mat
                                                                  "()"
                                                                  (Term.Mat
                                                                    "()"
                                                                    (Term.Mat
                                                                      "()"
                                                                      (Term.Lam
                                                                        (Quan.Q1)
                                                                        (Term.App
                                                                          (Quan.Q1)
                                                                          (Term.Ref "Book.read.var")
                                                                          (Term.Var 0)))
                                                                      (Term.Efq))
                                                                    (Term.Efq))
                                                                  (Term.Efq))
                                                                (Term.Efq))
                                                              (Term.Efq))
                                                            (Term.Efq))
                                                          (Term.Efq))
                                                        (Term.Mat
                                                          "Succ"
                                                          (Term.Prj
                                                            (Term.Prj
                                                              (Term.Mat
                                                                "Zero"
                                                                (Term.Mat
                                                                  "()"
                                                                  (Term.Mat
                                                                    "()"
                                                                    (Term.Mat
                                                                      "()"
                                                                      (Term.Mat
                                                                        "()"
                                                                        (Term.Mat
                                                                          "()"
                                                                          (Term.Mat
                                                                            "()"
                                                                            (Term.Mat
                                                                              "()"
                                                                              (Term.Mat
                                                                                "()"
                                                                                (Term.Lam
                                                                                  (Quan.Q1)
                                                                                  (Term.App
                                                                                    (Quan.Q1)
                                                                                    (Term.Ref
                                                                                      "Book.read.ref")
                                                                                    (Term.Var 0)))
                                                                                (Term.Efq))
                                                                              (Term.Efq))
                                                                            (Term.Efq))
                                                                          (Term.Efq))
                                                                        (Term.Efq))
                                                                      (Term.Efq))
                                                                    (Term.Efq))
                                                                  (Term.Efq))
                                                                (Term.Mat
                                                                  "Succ"
                                                                  (Term.Prj
                                                                    (Term.Lam
                                                                      (Quan.Q1)
                                                                      (Term.Mat
                                                                        "()"
                                                                        (Term.Mat
                                                                          "()"
                                                                          (Term.Mat
                                                                            "()"
                                                                            (Term.Mat
                                                                              "()"
                                                                              (Term.Mat
                                                                                "()"
                                                                                (Term.Mat
                                                                                  "()"
                                                                                  (Term.Mat
                                                                                    "()"
                                                                                    (Term.Mat
                                                                                      "()"
                                                                                      (Term.Lam
                                                                                        (Quan.Q1)
                                                                                        (Term.App
                                                                                          (Quan.Q1)
                                                                                          (Term.App
                                                                                            (Quan.Q1)
                                                                                            (Term.Ref
                                                                                              "Book.read.token16")
                                                                                            (Term.Var
                                                                                              1))
                                                                                          (Term.Var
                                                                                            0)))
                                                                                      (Term.Efq))
                                                                                    (Term.Efq))
                                                                                  (Term.Efq))
                                                                                (Term.Efq))
                                                                              (Term.Efq))
                                                                            (Term.Efq))
                                                                          (Term.Efq))
                                                                        (Term.Efq))))
                                                                  (Term.Efq)))))
                                                          (Term.Efq)))))
                                                  (Term.Efq)))))
                                          (Term.Efq)))))
                                  (Term.Efq)))))
                          (Term.Efq)))))
                  (Term.Efq)))))
          (Term.Efq))),
    false⟩

def «reader.Book.read.token» : Def :=
  ⟨"Book.read.token",
    Term.All
      (Quan.Q1)
      (Term.Ref "Nat")
      (Term.All
        (Quan.Q1)
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
          (Term.Ref "Item"))
        (Term.All
          (Quan.Q1)
          (Term.Ref "U32")
          (Term.App
            (Quan.Q0)
            (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
            (Term.App
              (Quan.Q0)
              (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
              (Term.Ref "Item"))))),
    Term.Prj
      (Term.Mat
        "Zero"
        (Term.Mat
          "()"
          (Term.Lam
            (Quan.Q1)
            (Term.Lam
              (Quan.Q1)
              (Term.Tup
                (Quan.Q1)
                (Term.Lab "Some")
                (Term.Tup
                  (Quan.Q1)
                  (Term.Tup
                    (Quan.Q1)
                    (Term.Lab "Con")
                    (Term.Tup
                      (Quan.Q1)
                      (Term.Tup
                        (Quan.Q1)
                        (Term.Lab "Item.quan")
                        (Term.Tup
                          (Quan.Q1)
                          (Term.Tup (Quan.Q1) (Term.Lab "Quan.Q0") (Term.Lab "()"))
                          (Term.Lab "()")))
                      (Term.Tup (Quan.Q1) (Term.Var 1) (Term.Lab "()"))))
                  (Term.Lab "()")))))
          (Term.Efq))
        (Term.Mat
          "Succ"
          (Term.Prj
            (Term.Prj
              (Term.Mat
                "Zero"
                (Term.Mat
                  "()"
                  (Term.Mat
                    "()"
                    (Term.Lam
                      (Quan.Q1)
                      (Term.Lam
                        (Quan.Q1)
                        (Term.Tup
                          (Quan.Q1)
                          (Term.Lab "Some")
                          (Term.Tup
                            (Quan.Q1)
                            (Term.Tup
                              (Quan.Q1)
                              (Term.Lab "Con")
                              (Term.Tup
                                (Quan.Q1)
                                (Term.Tup
                                  (Quan.Q1)
                                  (Term.Lab "Item.quan")
                                  (Term.Tup
                                    (Quan.Q1)
                                    (Term.Tup (Quan.Q1) (Term.Lab "Quan.Q1") (Term.Lab "()"))
                                    (Term.Lab "()")))
                                (Term.Tup (Quan.Q1) (Term.Var 1) (Term.Lab "()"))))
                            (Term.Lab "()")))))
                    (Term.Efq))
                  (Term.Efq))
                (Term.Mat
                  "Succ"
                  (Term.Prj
                    (Term.Prj
                      (Term.Mat
                        "Zero"
                        (Term.Mat
                          "()"
                          (Term.Mat
                            "()"
                            (Term.Mat
                              "()"
                              (Term.Lam
                                (Quan.Q1)
                                (Term.Lam
                                  (Quan.Q1)
                                  (Term.Tup
                                    (Quan.Q1)
                                    (Term.Lab "Some")
                                    (Term.Tup
                                      (Quan.Q1)
                                      (Term.Tup
                                        (Quan.Q1)
                                        (Term.Lab "Con")
                                        (Term.Tup
                                          (Quan.Q1)
                                          (Term.Tup
                                            (Quan.Q1)
                                            (Term.Lab "Item.quan")
                                            (Term.Tup
                                              (Quan.Q1)
                                              (Term.Tup
                                                (Quan.Q1)
                                                (Term.Lab "Quan.Q2")
                                                (Term.Lab "()"))
                                              (Term.Lab "()")))
                                          (Term.Tup (Quan.Q1) (Term.Var 1) (Term.Lab "()"))))
                                      (Term.Lab "()")))))
                              (Term.Efq))
                            (Term.Efq))
                          (Term.Efq))
                        (Term.Mat
                          "Succ"
                          (Term.Prj
                            (Term.Prj
                              (Term.Mat
                                "Zero"
                                (Term.Mat
                                  "()"
                                  (Term.Mat
                                    "()"
                                    (Term.Mat
                                      "()"
                                      (Term.Mat
                                        "()"
                                        (Term.Lam
                                          (Quan.Q1)
                                          (Term.Lam
                                            (Quan.Q1)
                                            (Term.Tup
                                              (Quan.Q1)
                                              (Term.Lab "Some")
                                              (Term.Tup
                                                (Quan.Q1)
                                                (Term.Tup
                                                  (Quan.Q1)
                                                  (Term.Lab "Con")
                                                  (Term.Tup
                                                    (Quan.Q1)
                                                    (Term.Tup
                                                      (Quan.Q1)
                                                      (Term.Lab "Item.nat")
                                                      (Term.Tup
                                                        (Quan.Q1)
                                                        (Term.Tup
                                                          (Quan.Q1)
                                                          (Term.Lab "Zero")
                                                          (Term.Lab "()"))
                                                        (Term.Lab "()")))
                                                    (Term.Tup
                                                      (Quan.Q1)
                                                      (Term.Var 1)
                                                      (Term.Lab "()"))))
                                                (Term.Lab "()")))))
                                        (Term.Efq))
                                      (Term.Efq))
                                    (Term.Efq))
                                  (Term.Efq))
                                (Term.Mat
                                  "Succ"
                                  (Term.Prj
                                    (Term.Prj
                                      (Term.Mat
                                        "Zero"
                                        (Term.Mat
                                          "()"
                                          (Term.Mat
                                            "()"
                                            (Term.Mat
                                              "()"
                                              (Term.Mat
                                                "()"
                                                (Term.Mat
                                                  "()"
                                                  (Term.Lam
                                                    (Quan.Q1)
                                                    (Term.Lam
                                                      (Quan.Q1)
                                                      (Term.App
                                                        (Quan.Q1)
                                                        (Term.Ref "Book.read.succ")
                                                        (Term.Var 1))))
                                                  (Term.Efq))
                                                (Term.Efq))
                                              (Term.Efq))
                                            (Term.Efq))
                                          (Term.Efq))
                                        (Term.Mat
                                          "Succ"
                                          (Term.Prj
                                            (Term.Prj
                                              (Term.Mat
                                                "Zero"
                                                (Term.Mat
                                                  "()"
                                                  (Term.Mat
                                                    "()"
                                                    (Term.Mat
                                                      "()"
                                                      (Term.Mat
                                                        "()"
                                                        (Term.Mat
                                                          "()"
                                                          (Term.Mat
                                                            "()"
                                                            (Term.Lam
                                                              (Quan.Q1)
                                                              (Term.Lam
                                                                (Quan.Q1)
                                                                (Term.Tup
                                                                  (Quan.Q1)
                                                                  (Term.Lab "Some")
                                                                  (Term.Tup
                                                                    (Quan.Q1)
                                                                    (Term.Tup
                                                                      (Quan.Q1)
                                                                      (Term.Lab "Con")
                                                                      (Term.Tup
                                                                        (Quan.Q1)
                                                                        (Term.Tup
                                                                          (Quan.Q1)
                                                                          (Term.Lab "Item.name")
                                                                          (Term.Tup
                                                                            (Quan.Q1)
                                                                            (Term.Tup
                                                                              (Quan.Q1)
                                                                              (Term.Lab "Nil")
                                                                              (Term.Lab "()"))
                                                                            (Term.Lab "()")))
                                                                        (Term.Tup
                                                                          (Quan.Q1)
                                                                          (Term.Var 1)
                                                                          (Term.Lab "()"))))
                                                                    (Term.Lab "()")))))
                                                            (Term.Efq))
                                                          (Term.Efq))
                                                        (Term.Efq))
                                                      (Term.Efq))
                                                    (Term.Efq))
                                                  (Term.Efq))
                                                (Term.Mat
                                                  "Succ"
                                                  (Term.Prj
                                                    (Term.Prj
                                                      (Term.Mat
                                                        "Zero"
                                                        (Term.Mat
                                                          "()"
                                                          (Term.Mat
                                                            "()"
                                                            (Term.Mat
                                                              "()"
                                                              (Term.Mat
                                                                "()"
                                                                (Term.Mat
                                                                  "()"
                                                                  (Term.Mat
                                                                    "()"
                                                                    (Term.Mat
                                                                      "()"
                                                                      (Term.Lam
                                                                        (Quan.Q1)
                                                                        (Term.Lam
                                                                          (Quan.Q1)
                                                                          (Term.App
                                                                            (Quan.Q1)
                                                                            (Term.App
                                                                              (Quan.Q1)
                                                                              (Term.Ref
                                                                                "Book.read.byte")
                                                                              (Term.Var 1))
                                                                            (Term.Var 0))))
                                                                      (Term.Efq))
                                                                    (Term.Efq))
                                                                  (Term.Efq))
                                                                (Term.Efq))
                                                              (Term.Efq))
                                                            (Term.Efq))
                                                          (Term.Efq))
                                                        (Term.Mat
                                                          "Succ"
                                                          (Term.Prj
                                                            (Term.Prj
                                                              (Term.Mat
                                                                "Zero"
                                                                (Term.Mat
                                                                  "()"
                                                                  (Term.Mat
                                                                    "()"
                                                                    (Term.Mat
                                                                      "()"
                                                                      (Term.Mat
                                                                        "()"
                                                                        (Term.Mat
                                                                          "()"
                                                                          (Term.Mat
                                                                            "()"
                                                                            (Term.Mat
                                                                              "()"
                                                                              (Term.Mat
                                                                                "()"
                                                                                (Term.Lam
                                                                                  (Quan.Q1)
                                                                                  (Term.Lam
                                                                                    (Quan.Q1)
                                                                                    (Term.Tup
                                                                                      (Quan.Q1)
                                                                                      (Term.Lab
                                                                                        "Some")
                                                                                      (Term.Tup
                                                                                        (Quan.Q1)
                                                                                        (Term.Tup
                                                                                          (Quan.Q1)
                                                                                          (Term.Lab
                                                                                            "Con")
                                                                                          (Term.Tup
                                                                                            (Quan.Q1)
                                                                                            (Term.Tup
                                                                                              (Quan.Q1)
                                                                                              (Term.Lab
                                                                                                "Item.names")
                                                                                              (Term.Tup
                                                                                                (Quan.Q1)
                                                                                                (Term.Tup
                                                                                                  (Quan.Q1)
                                                                                                  (Term.Lab
                                                                                                    "Nil")
                                                                                                  (Term.Lab
                                                                                                    "()"))
                                                                                                (Term.Lab
                                                                                                  "()")))
                                                                                            (Term.Tup
                                                                                              (Quan.Q1)
                                                                                              (Term.Var
                                                                                                1)
                                                                                              (Term.Lab
                                                                                                "()"))))
                                                                                        (Term.Lab
                                                                                          "()")))))
                                                                                (Term.Efq))
                                                                              (Term.Efq))
                                                                            (Term.Efq))
                                                                          (Term.Efq))
                                                                        (Term.Efq))
                                                                      (Term.Efq))
                                                                    (Term.Efq))
                                                                  (Term.Efq))
                                                                (Term.Mat
                                                                  "Succ"
                                                                  (Term.Prj
                                                                    (Term.Lam
                                                                      (Quan.Q1)
                                                                      (Term.Mat
                                                                        "()"
                                                                        (Term.Mat
                                                                          "()"
                                                                          (Term.Mat
                                                                            "()"
                                                                            (Term.Mat
                                                                              "()"
                                                                              (Term.Mat
                                                                                "()"
                                                                                (Term.Mat
                                                                                  "()"
                                                                                  (Term.Mat
                                                                                    "()"
                                                                                    (Term.Mat
                                                                                      "()"
                                                                                      (Term.Lam
                                                                                        (Quan.Q1)
                                                                                        (Term.Lam
                                                                                          (Quan.Q1)
                                                                                          (Term.App
                                                                                            (Quan.Q1)
                                                                                            (Term.App
                                                                                              (Quan.Q1)
                                                                                              (Term.Ref
                                                                                                "Book.read.token8")
                                                                                              (Term.Var
                                                                                                2))
                                                                                            (Term.Var
                                                                                              1))))
                                                                                      (Term.Efq))
                                                                                    (Term.Efq))
                                                                                  (Term.Efq))
                                                                                (Term.Efq))
                                                                              (Term.Efq))
                                                                            (Term.Efq))
                                                                          (Term.Efq))
                                                                        (Term.Efq))))
                                                                  (Term.Efq)))))
                                                          (Term.Efq)))))
                                                  (Term.Efq)))))
                                          (Term.Efq)))))
                                  (Term.Efq)))))
                          (Term.Efq)))))
                  (Term.Efq)))))
          (Term.Efq))),
    false⟩

def «reader.Nat.double» : Def :=
  ⟨"Nat.double",
    Term.All (Quan.Q1) (Term.Ref "Nat") (Term.Ref "Nat"),
    Term.Prj
      (Term.Mat
        "Zero"
        (Term.Mat "()" (Term.Tup (Quan.Q1) (Term.Lab "Zero") (Term.Lab "()")) (Term.Efq))
        (Term.Mat
          "Succ"
          (Term.Prj
            (Term.Lam
              (Quan.Q1)
              (Term.Mat
                "()"
                (Term.Tup
                  (Quan.Q1)
                  (Term.Lab "Succ")
                  (Term.Tup
                    (Quan.Q1)
                    (Term.Tup
                      (Quan.Q1)
                      (Term.Lab "Succ")
                      (Term.Tup
                        (Quan.Q1)
                        (Term.App (Quan.Q1) (Term.Ref "Nat.double") (Term.Var 0))
                        (Term.Lab "()")))
                    (Term.Lab "()")))
                (Term.Efq))))
          (Term.Efq))),
    false⟩

def «reader.Word.to_nat» : Def :=
  ⟨"Word.to_nat",
    Term.All
      (Quan.Q1)
      (Term.Ref "Nat")
      (Term.All (Quan.Q1) (Term.App (Quan.Q1) (Term.Ref "Word") (Term.Var 0)) (Term.Ref "Nat")),
    Term.Prj
      (Term.Mat
        "Zero"
        (Term.Mat
          "()"
          (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "Zero") (Term.Lab "()")))
          (Term.Efq))
        (Term.Mat
          "Succ"
          (Term.Prj
            (Term.Lam
              (Quan.Q2)
              (Term.Mat
                "()"
                (Term.Prj
                  (Term.Mat
                    "WCon"
                    (Term.Prj
                      (Term.Prj
                        (Term.Mat
                          "False"
                          (Term.Mat
                            "()"
                            (Term.Prj
                              (Term.Lam
                                (Quan.Q1)
                                (Term.Mat
                                  "()"
                                  (Term.App
                                    (Quan.Q1)
                                    (Term.Ref "Nat.double")
                                    (Term.App
                                      (Quan.Q1)
                                      (Term.App (Quan.Q1) (Term.Ref "Word.to_nat") (Term.Var 1))
                                      (Term.Var 0)))
                                  (Term.Efq))))
                            (Term.Efq))
                          (Term.Mat
                            "True"
                            (Term.Mat
                              "()"
                              (Term.Prj
                                (Term.Lam
                                  (Quan.Q1)
                                  (Term.Mat
                                    "()"
                                    (Term.Tup
                                      (Quan.Q1)
                                      (Term.Lab "Succ")
                                      (Term.Tup
                                        (Quan.Q1)
                                        (Term.App
                                          (Quan.Q1)
                                          (Term.Ref "Nat.double")
                                          (Term.App
                                            (Quan.Q1)
                                            (Term.App
                                              (Quan.Q1)
                                              (Term.Ref "Word.to_nat")
                                              (Term.Var 1))
                                            (Term.Var 0)))
                                        (Term.Lab "()")))
                                    (Term.Efq))))
                              (Term.Efq))
                            (Term.Efq)))))
                    (Term.Efq)))
                (Term.Efq))))
          (Term.Efq))),
    false⟩

def «reader.U32.to_nat» : Def :=
  ⟨"U32.to_nat",
    Term.All (Quan.Q1) (Term.Ref "U32") (Term.Ref "Nat"),
    Term.Prj
      (Term.Mat
        "U32"
        (Term.Prj
          (Term.Lam
            (Quan.Q1)
            (Term.Mat
              "()"
              (Term.App
                (Quan.Q1)
                (Term.App
                  (Quan.Q1)
                  (Term.Ref "Word.to_nat")
                  (Term.Tup
                    (Quan.Q1)
                    (Term.Lab "Succ")
                    (Term.Tup
                      (Quan.Q1)
                      (Term.Tup
                        (Quan.Q1)
                        (Term.Lab "Succ")
                        (Term.Tup
                          (Quan.Q1)
                          (Term.Tup
                            (Quan.Q1)
                            (Term.Lab "Succ")
                            (Term.Tup
                              (Quan.Q1)
                              (Term.Tup
                                (Quan.Q1)
                                (Term.Lab "Succ")
                                (Term.Tup
                                  (Quan.Q1)
                                  (Term.Tup
                                    (Quan.Q1)
                                    (Term.Lab "Succ")
                                    (Term.Tup
                                      (Quan.Q1)
                                      (Term.Tup
                                        (Quan.Q1)
                                        (Term.Lab "Succ")
                                        (Term.Tup
                                          (Quan.Q1)
                                          (Term.Tup
                                            (Quan.Q1)
                                            (Term.Lab "Succ")
                                            (Term.Tup
                                              (Quan.Q1)
                                              (Term.Tup
                                                (Quan.Q1)
                                                (Term.Lab "Succ")
                                                (Term.Tup
                                                  (Quan.Q1)
                                                  (Term.Tup
                                                    (Quan.Q1)
                                                    (Term.Lab "Succ")
                                                    (Term.Tup
                                                      (Quan.Q1)
                                                      (Term.Tup
                                                        (Quan.Q1)
                                                        (Term.Lab "Succ")
                                                        (Term.Tup
                                                          (Quan.Q1)
                                                          (Term.Tup
                                                            (Quan.Q1)
                                                            (Term.Lab "Succ")
                                                            (Term.Tup
                                                              (Quan.Q1)
                                                              (Term.Tup
                                                                (Quan.Q1)
                                                                (Term.Lab "Succ")
                                                                (Term.Tup
                                                                  (Quan.Q1)
                                                                  (Term.Tup
                                                                    (Quan.Q1)
                                                                    (Term.Lab "Succ")
                                                                    (Term.Tup
                                                                      (Quan.Q1)
                                                                      (Term.Tup
                                                                        (Quan.Q1)
                                                                        (Term.Lab "Succ")
                                                                        (Term.Tup
                                                                          (Quan.Q1)
                                                                          (Term.Tup
                                                                            (Quan.Q1)
                                                                            (Term.Lab "Succ")
                                                                            (Term.Tup
                                                                              (Quan.Q1)
                                                                              (Term.Tup
                                                                                (Quan.Q1)
                                                                                (Term.Lab "Succ")
                                                                                (Term.Tup
                                                                                  (Quan.Q1)
                                                                                  (Term.Tup
                                                                                    (Quan.Q1)
                                                                                    (Term.Lab
                                                                                      "Succ")
                                                                                    (Term.Tup
                                                                                      (Quan.Q1)
                                                                                      (Term.Tup
                                                                                        (Quan.Q1)
                                                                                        (Term.Lab
                                                                                          "Succ")
                                                                                        (Term.Tup
                                                                                          (Quan.Q1)
                                                                                          (Term.Tup
                                                                                            (Quan.Q1)
                                                                                            (Term.Lab
                                                                                              "Succ")
                                                                                            (Term.Tup
                                                                                              (Quan.Q1)
                                                                                              (Term.Tup
                                                                                                (Quan.Q1)
                                                                                                (Term.Lab
                                                                                                  "Succ")
                                                                                                (Term.Tup
                                                                                                  (Quan.Q1)
                                                                                                  (Term.Tup
                                                                                                    (Quan.Q1)
                                                                                                    (Term.Lab
                                                                                                      "Succ")
                                                                                                    (Term.Tup
                                                                                                      (Quan.Q1)
                                                                                                      (Term.Tup
                                                                                                        (Quan.Q1)
                                                                                                        (Term.Lab
                                                                                                          "Succ")
                                                                                                        (Term.Tup
                                                                                                          (Quan.Q1)
                                                                                                          (Term.Tup
                                                                                                            (Quan.Q1)
                                                                                                            (Term.Lab
                                                                                                              "Succ")
                                                                                                            (Term.Tup
                                                                                                              (Quan.Q1)
                                                                                                              (Term.Tup
                                                                                                                (Quan.Q1)
                                                                                                                (Term.Lab
                                                                                                                  "Succ")
                                                                                                                (Term.Tup
                                                                                                                  (Quan.Q1)
                                                                                                                  (Term.Tup
                                                                                                                    (Quan.Q1)
                                                                                                                    (Term.Lab
                                                                                                                      "Succ")
                                                                                                                    (Term.Tup
                                                                                                                      (Quan.Q1)
                                                                                                                      (Term.Tup
                                                                                                                        (Quan.Q1)
                                                                                                                        (Term.Lab
                                                                                                                          "Succ")
                                                                                                                        (Term.Tup
                                                                                                                          (Quan.Q1)
                                                                                                                          (Term.Tup
                                                                                                                            (Quan.Q1)
                                                                                                                            (Term.Lab
                                                                                                                              "Succ")
                                                                                                                            (Term.Tup
                                                                                                                              (Quan.Q1)
                                                                                                                              (Term.Tup
                                                                                                                                (Quan.Q1)
                                                                                                                                (Term.Lab
                                                                                                                                  "Succ")
                                                                                                                                (Term.Tup
                                                                                                                                  (Quan.Q1)
                                                                                                                                  (Term.Tup
                                                                                                                                    (Quan.Q1)
                                                                                                                                    (Term.Lab
                                                                                                                                      "Succ")
                                                                                                                                    (Term.Tup
                                                                                                                                      (Quan.Q1)
                                                                                                                                      (Term.Tup
                                                                                                                                        (Quan.Q1)
                                                                                                                                        (Term.Lab
                                                                                                                                          "Succ")
                                                                                                                                        (Term.Tup
                                                                                                                                          (Quan.Q1)
                                                                                                                                          (Term.Tup
                                                                                                                                            (Quan.Q1)
                                                                                                                                            (Term.Lab
                                                                                                                                              "Succ")
                                                                                                                                            (Term.Tup
                                                                                                                                              (Quan.Q1)
                                                                                                                                              (Term.Tup
                                                                                                                                                (Quan.Q1)
                                                                                                                                                (Term.Lab
                                                                                                                                                  "Succ")
                                                                                                                                                (Term.Tup
                                                                                                                                                  (Quan.Q1)
                                                                                                                                                  (Term.Tup
                                                                                                                                                    (Quan.Q1)
                                                                                                                                                    (Term.Lab
                                                                                                                                                      "Zero")
                                                                                                                                                    (Term.Lab
                                                                                                                                                      "()"))
                                                                                                                                                  (Term.Lab
                                                                                                                                                    "()")))
                                                                                                                                              (Term.Lab
                                                                                                                                                "()")))
                                                                                                                                          (Term.Lab
                                                                                                                                            "()")))
                                                                                                                                      (Term.Lab
                                                                                                                                        "()")))
                                                                                                                                  (Term.Lab
                                                                                                                                    "()")))
                                                                                                                              (Term.Lab
                                                                                                                                "()")))
                                                                                                                          (Term.Lab
                                                                                                                            "()")))
                                                                                                                      (Term.Lab
                                                                                                                        "()")))
                                                                                                                  (Term.Lab
                                                                                                                    "()")))
                                                                                                              (Term.Lab
                                                                                                                "()")))
                                                                                                          (Term.Lab
                                                                                                            "()")))
                                                                                                      (Term.Lab
                                                                                                        "()")))
                                                                                                  (Term.Lab
                                                                                                    "()")))
                                                                                              (Term.Lab
                                                                                                "()")))
                                                                                          (Term.Lab
                                                                                            "()")))
                                                                                      (Term.Lab
                                                                                        "()")))
                                                                                  (Term.Lab "()")))
                                                                              (Term.Lab "()")))
                                                                          (Term.Lab "()")))
                                                                      (Term.Lab "()")))
                                                                  (Term.Lab "()")))
                                                              (Term.Lab "()")))
                                                          (Term.Lab "()")))
                                                      (Term.Lab "()")))
                                                  (Term.Lab "()")))
                                              (Term.Lab "()")))
                                          (Term.Lab "()")))
                                      (Term.Lab "()")))
                                  (Term.Lab "()")))
                              (Term.Lab "()")))
                          (Term.Lab "()")))
                      (Term.Lab "()"))))
                (Term.Var 0))
              (Term.Efq))))
        (Term.Efq)),
    false⟩

def «reader.Book.read.step» : Def :=
  ⟨"Book.read.step",
    Term.All
      (Quan.Q1)
      (Term.App
        (Quan.Q0)
        (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
          (Term.Ref "Item")))
      (Term.All
        (Quan.Q1)
        (Term.Ref "U32")
        (Term.All
          (Quan.Q1)
          (Term.Ref "U32")
          (Term.App
            (Quan.Q0)
            (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
            (Term.App
              (Quan.Q0)
              (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
              (Term.Ref "Item"))))),
    Term.Prj
      (Term.Mat
        "None"
        (Term.Mat
          "()"
          (Term.Lam
            (Quan.Q1)
            (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))))
          (Term.Efq))
        (Term.Mat
          "Some"
          (Term.Prj
            (Term.Lam
              (Quan.Q1)
              (Term.Mat
                "()"
                (Term.Lam
                  (Quan.Q1)
                  (Term.Lam
                    (Quan.Q1)
                    (Term.App
                      (Quan.Q1)
                      (Term.App
                        (Quan.Q1)
                        (Term.App
                          (Quan.Q1)
                          (Term.Ref "Book.read.token")
                          (Term.App (Quan.Q1) (Term.Ref "U32.to_nat") (Term.Var 1)))
                        (Term.Var 2))
                      (Term.Var 0))))
                (Term.Efq))))
          (Term.Efq))),
    false⟩

def «reader.Book.read.done» : Def :=
  ⟨"Book.read.done",
    Term.All
      (Quan.Q1)
      (Term.App
        (Quan.Q0)
        (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
          (Term.Ref "Item")))
      (Term.App
        (Quan.Q0)
        (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
          (Term.Ref "Def"))),
    Term.Prj
      (Term.Mat
        "Some"
        (Term.Prj
          (Term.Prj
            (Term.Mat
              "Con"
              (Term.Prj
                (Term.Prj
                  (Term.Mat
                    "Item.defs"
                    (Term.Prj
                      (Term.Lam
                        (Quan.Q1)
                        (Term.Mat
                          "()"
                          (Term.Prj
                            (Term.Prj
                              (Term.Mat
                                "Nil"
                                (Term.Mat
                                  "()"
                                  (Term.Mat
                                    "()"
                                    (Term.Mat
                                      "()"
                                      (Term.Tup
                                        (Quan.Q1)
                                        (Term.Lab "Some")
                                        (Term.Tup (Quan.Q1) (Term.Var 0) (Term.Lab "()")))
                                      (Term.Efq))
                                    (Term.Efq))
                                  (Term.Efq))
                                (Term.Lam
                                  (Quan.Q1)
                                  (Term.Lam
                                    (Quan.Q1)
                                    (Term.Mat
                                      "()"
                                      (Term.Mat
                                        "()"
                                        (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                                        (Term.Efq))
                                      (Term.Efq)))))))
                          (Term.Efq))))
                    (Term.Lam
                      (Quan.Q1)
                      (Term.Lam
                        (Quan.Q1)
                        (Term.Prj
                          (Term.Lam
                            (Quan.Q1)
                            (Term.Mat
                              "()"
                              (Term.Mat
                                "()"
                                (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                                (Term.Efq))
                              (Term.Efq)))))))))
              (Term.Lam
                (Quan.Q1)
                (Term.Lam
                  (Quan.Q1)
                  (Term.Mat
                    "()"
                    (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                    (Term.Efq)))))))
        (Term.Lam
          (Quan.Q1)
          (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))))),
    false⟩

def «reader.Book.read.go» : Def :=
  ⟨"Book.read.go",
    Term.All
      (Quan.Q1)
      (Term.App (Quan.Q0) (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "U32"))
      (Term.All
        (Quan.Q1)
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
          (Term.App
            (Quan.Q0)
            (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
            (Term.Ref "Item")))
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
          (Term.App
            (Quan.Q0)
            (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
            (Term.Ref "Def")))),
    Term.Prj
      (Term.Mat
        "Nil"
        (Term.Mat
          "()"
          (Term.Lam (Quan.Q1) (Term.App (Quan.Q1) (Term.Ref "Book.read.done") (Term.Var 0)))
          (Term.Efq))
        (Term.Mat
          "Con"
          (Term.Prj
            (Term.Lam
              (Quan.Q1)
              (Term.Prj
                (Term.Prj
                  (Term.Mat
                    "Nil"
                    (Term.Mat
                      "()"
                      (Term.Mat
                        "()"
                        (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()")))
                        (Term.Efq))
                      (Term.Efq))
                    (Term.Mat
                      "Con"
                      (Term.Prj
                        (Term.Lam
                          (Quan.Q1)
                          (Term.Prj
                            (Term.Lam
                              (Quan.Q1)
                              (Term.Mat
                                "()"
                                (Term.Mat
                                  "()"
                                  (Term.Lam
                                    (Quan.Q1)
                                    (Term.App
                                      (Quan.Q1)
                                      (Term.App (Quan.Q1) (Term.Ref "Book.read.go") (Term.Var 1))
                                      (Term.App
                                        (Quan.Q1)
                                        (Term.App
                                          (Quan.Q1)
                                          (Term.App
                                            (Quan.Q1)
                                            (Term.Ref "Book.read.step")
                                            (Term.Var 0))
                                          (Term.Var 3))
                                        (Term.Var 2))))
                                  (Term.Efq))
                                (Term.Efq))))))
                      (Term.Efq)))))))
          (Term.Efq))),
    false⟩

def «reader.Book.read» : Def :=
  ⟨"Book.read",
    Term.All
      (Quan.Q1)
      (Term.App (Quan.Q0) (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "U32"))
      (Term.App
        (Quan.Q0)
        (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
          (Term.Ref "Def"))),
    Term.Lam
      (Quan.Q1)
      (Term.App
        (Quan.Q1)
        (Term.App (Quan.Q1) (Term.Ref "Book.read.go") (Term.Var 0))
        (Term.Tup
          (Quan.Q1)
          (Term.Lab "Some")
          (Term.Tup
            (Quan.Q1)
            (Term.Tup (Quan.Q1) (Term.Lab "Nil") (Term.Lab "()"))
            (Term.Lab "()")))),
    false⟩

def «reader.Word.Nil.arms» : Def :=
  ⟨"Word.Nil.arms",
    Term.All (Quan.Q1) (Term.Enu ["WNil"]) (Term.Typ (Term.Lab "Q2")),
    Term.Mat "WNil" (Term.Enu ["()"]) (Term.Efq),
    false⟩

def «reader.Word.Nil» : Def :=
  ⟨"Word.Nil",
    Term.Typ (Term.Lab "Q2"),
    Term.Sig (Quan.Q1) (Term.Enu ["WNil"]) (Term.App (Quan.Q1) (Term.Ref "Word.Nil.arms") (Term.Var 0)),
    false⟩

def «reader.Word.Con.arms» : Def :=
  ⟨"Word.Con.arms",
    Term.All
      (Quan.Q0)
      (Term.Ref "Nat")
      (Term.All (Quan.Q1) (Term.Enu ["WCon"]) (Term.Typ (Term.Lab "Q2"))),
    Term.Lam
      (Quan.Q0)
      (Term.Mat
        "WCon"
        (Term.Sig
          (Quan.Q1)
          (Term.Ref "Bool")
          (Term.Sig
            (Quan.Q1)
            (Term.App (Quan.Q1) (Term.Ref "Word") (Term.Var 1))
            (Term.Enu ["()"])))
        (Term.Efq)),
    false⟩

def «reader.Word.Con» : Def :=
  ⟨"Word.Con",
    Term.All (Quan.Q0) (Term.Ref "Nat") (Term.Typ (Term.Lab "Q2")),
    Term.Lam
      (Quan.Q0)
      (Term.Sig
        (Quan.Q1)
        (Term.Enu ["WCon"])
        (Term.App
          (Quan.Q1)
          (Term.App (Quan.Q0) (Term.Ref "Word.Con.arms") (Term.Var 1))
          (Term.Var 0))),
    false⟩

def «reader.Word» : Def :=
  ⟨"Word",
    Term.All (Quan.Q1) (Term.Ref "Nat") (Term.Typ (Term.Lab "Q2")),
    Term.Prj
      (Term.Mat
        "Zero"
        (Term.Mat "()" (Term.Ref "Word.Nil") (Term.Efq))
        (Term.Mat
          "Succ"
          (Term.Prj
            (Term.Lam
              (Quan.Q1)
              (Term.Mat "()" (Term.App (Quan.Q0) (Term.Ref "Word.Con") (Term.Var 0)) (Term.Efq))))
          (Term.Efq))),
    false⟩

def «reader.Maybe.arms» : Def :=
  ⟨"Maybe.arms",
    Term.All
      (Quan.Q0)
      (Term.Enu ["Q0", "Q1", "Q2"])
      (Term.All
        (Quan.Q0)
        (Term.Typ (Term.Var 0))
        (Term.All (Quan.Q1) (Term.Enu ["None", "Some"]) (Term.Typ (Term.Var 2)))),
    Term.Lam
      (Quan.Q0)
      (Term.Lam
        (Quan.Q0)
        (Term.Mat
          "None"
          (Term.Enu ["()"])
          (Term.Mat "Some" (Term.Sig (Quan.Q1) (Term.Var 0) (Term.Enu ["()"])) (Term.Efq)))),
    false⟩

def «reader.Maybe» : Def :=
  ⟨"Maybe",
    Term.All
      (Quan.Q0)
      (Term.Enu ["Q0", "Q1", "Q2"])
      (Term.All (Quan.Q0) (Term.Typ (Term.Var 0)) (Term.Typ (Term.Var 1))),
    Term.Lam
      (Quan.Q0)
      (Term.Lam
        (Quan.Q0)
        (Term.Sig
          (Quan.Q1)
          (Term.Enu ["None", "Some"])
          (Term.App
            (Quan.Q1)
            (Term.App
              (Quan.Q0)
              (Term.App (Quan.Q0) (Term.Ref "Maybe.arms") (Term.Var 2))
              (Term.Var 1))
            (Term.Var 0)))),
    false⟩

def «reader.Bool.arms» : Def :=
  ⟨"Bool.arms",
    Term.All (Quan.Q1) (Term.Enu ["False", "True"]) (Term.Typ (Term.Lab "Q2")),
    Term.Mat "False" (Term.Enu ["()"]) (Term.Mat "True" (Term.Enu ["()"]) (Term.Efq)),
    false⟩

def «reader.Bool» : Def :=
  ⟨"Bool",
    Term.Typ (Term.Lab "Q2"),
    Term.Sig
      (Quan.Q1)
      (Term.Enu ["False", "True"])
      (Term.App (Quan.Q1) (Term.Ref "Bool.arms") (Term.Var 0)),
    false⟩

def «reader.Nat.arms» : Def :=
  ⟨"Nat.arms",
    Term.All (Quan.Q1) (Term.Enu ["Zero", "Succ"]) (Term.Typ (Term.Lab "Q2")),
    Term.Mat
      "Zero"
      (Term.Enu ["()"])
      (Term.Mat "Succ" (Term.Sig (Quan.Q1) (Term.Ref "Nat") (Term.Enu ["()"])) (Term.Efq)),
    false⟩

def «reader.Nat» : Def :=
  ⟨"Nat",
    Term.Typ (Term.Lab "Q2"),
    Term.Sig
      (Quan.Q1)
      (Term.Enu ["Zero", "Succ"])
      (Term.App (Quan.Q1) (Term.Ref "Nat.arms") (Term.Var 0)),
    false⟩

def «reader.U32.arms» : Def :=
  ⟨"U32.arms",
    Term.All (Quan.Q1) (Term.Enu ["U32"]) (Term.Typ (Term.Lab "Q2")),
    Term.Mat
      "U32"
      (Term.Sig
        (Quan.Q1)
        (Term.App
          (Quan.Q1)
          (Term.Ref "Word")
          (Term.Tup
            (Quan.Q1)
            (Term.Lab "Succ")
            (Term.Tup
              (Quan.Q1)
              (Term.Tup
                (Quan.Q1)
                (Term.Lab "Succ")
                (Term.Tup
                  (Quan.Q1)
                  (Term.Tup
                    (Quan.Q1)
                    (Term.Lab "Succ")
                    (Term.Tup
                      (Quan.Q1)
                      (Term.Tup
                        (Quan.Q1)
                        (Term.Lab "Succ")
                        (Term.Tup
                          (Quan.Q1)
                          (Term.Tup
                            (Quan.Q1)
                            (Term.Lab "Succ")
                            (Term.Tup
                              (Quan.Q1)
                              (Term.Tup
                                (Quan.Q1)
                                (Term.Lab "Succ")
                                (Term.Tup
                                  (Quan.Q1)
                                  (Term.Tup
                                    (Quan.Q1)
                                    (Term.Lab "Succ")
                                    (Term.Tup
                                      (Quan.Q1)
                                      (Term.Tup
                                        (Quan.Q1)
                                        (Term.Lab "Succ")
                                        (Term.Tup
                                          (Quan.Q1)
                                          (Term.Tup
                                            (Quan.Q1)
                                            (Term.Lab "Succ")
                                            (Term.Tup
                                              (Quan.Q1)
                                              (Term.Tup
                                                (Quan.Q1)
                                                (Term.Lab "Succ")
                                                (Term.Tup
                                                  (Quan.Q1)
                                                  (Term.Tup
                                                    (Quan.Q1)
                                                    (Term.Lab "Succ")
                                                    (Term.Tup
                                                      (Quan.Q1)
                                                      (Term.Tup
                                                        (Quan.Q1)
                                                        (Term.Lab "Succ")
                                                        (Term.Tup
                                                          (Quan.Q1)
                                                          (Term.Tup
                                                            (Quan.Q1)
                                                            (Term.Lab "Succ")
                                                            (Term.Tup
                                                              (Quan.Q1)
                                                              (Term.Tup
                                                                (Quan.Q1)
                                                                (Term.Lab "Succ")
                                                                (Term.Tup
                                                                  (Quan.Q1)
                                                                  (Term.Tup
                                                                    (Quan.Q1)
                                                                    (Term.Lab "Succ")
                                                                    (Term.Tup
                                                                      (Quan.Q1)
                                                                      (Term.Tup
                                                                        (Quan.Q1)
                                                                        (Term.Lab "Succ")
                                                                        (Term.Tup
                                                                          (Quan.Q1)
                                                                          (Term.Tup
                                                                            (Quan.Q1)
                                                                            (Term.Lab "Succ")
                                                                            (Term.Tup
                                                                              (Quan.Q1)
                                                                              (Term.Tup
                                                                                (Quan.Q1)
                                                                                (Term.Lab "Succ")
                                                                                (Term.Tup
                                                                                  (Quan.Q1)
                                                                                  (Term.Tup
                                                                                    (Quan.Q1)
                                                                                    (Term.Lab
                                                                                      "Succ")
                                                                                    (Term.Tup
                                                                                      (Quan.Q1)
                                                                                      (Term.Tup
                                                                                        (Quan.Q1)
                                                                                        (Term.Lab
                                                                                          "Succ")
                                                                                        (Term.Tup
                                                                                          (Quan.Q1)
                                                                                          (Term.Tup
                                                                                            (Quan.Q1)
                                                                                            (Term.Lab
                                                                                              "Succ")
                                                                                            (Term.Tup
                                                                                              (Quan.Q1)
                                                                                              (Term.Tup
                                                                                                (Quan.Q1)
                                                                                                (Term.Lab
                                                                                                  "Succ")
                                                                                                (Term.Tup
                                                                                                  (Quan.Q1)
                                                                                                  (Term.Tup
                                                                                                    (Quan.Q1)
                                                                                                    (Term.Lab
                                                                                                      "Succ")
                                                                                                    (Term.Tup
                                                                                                      (Quan.Q1)
                                                                                                      (Term.Tup
                                                                                                        (Quan.Q1)
                                                                                                        (Term.Lab
                                                                                                          "Succ")
                                                                                                        (Term.Tup
                                                                                                          (Quan.Q1)
                                                                                                          (Term.Tup
                                                                                                            (Quan.Q1)
                                                                                                            (Term.Lab
                                                                                                              "Succ")
                                                                                                            (Term.Tup
                                                                                                              (Quan.Q1)
                                                                                                              (Term.Tup
                                                                                                                (Quan.Q1)
                                                                                                                (Term.Lab
                                                                                                                  "Succ")
                                                                                                                (Term.Tup
                                                                                                                  (Quan.Q1)
                                                                                                                  (Term.Tup
                                                                                                                    (Quan.Q1)
                                                                                                                    (Term.Lab
                                                                                                                      "Succ")
                                                                                                                    (Term.Tup
                                                                                                                      (Quan.Q1)
                                                                                                                      (Term.Tup
                                                                                                                        (Quan.Q1)
                                                                                                                        (Term.Lab
                                                                                                                          "Succ")
                                                                                                                        (Term.Tup
                                                                                                                          (Quan.Q1)
                                                                                                                          (Term.Tup
                                                                                                                            (Quan.Q1)
                                                                                                                            (Term.Lab
                                                                                                                              "Succ")
                                                                                                                            (Term.Tup
                                                                                                                              (Quan.Q1)
                                                                                                                              (Term.Tup
                                                                                                                                (Quan.Q1)
                                                                                                                                (Term.Lab
                                                                                                                                  "Succ")
                                                                                                                                (Term.Tup
                                                                                                                                  (Quan.Q1)
                                                                                                                                  (Term.Tup
                                                                                                                                    (Quan.Q1)
                                                                                                                                    (Term.Lab
                                                                                                                                      "Succ")
                                                                                                                                    (Term.Tup
                                                                                                                                      (Quan.Q1)
                                                                                                                                      (Term.Tup
                                                                                                                                        (Quan.Q1)
                                                                                                                                        (Term.Lab
                                                                                                                                          "Succ")
                                                                                                                                        (Term.Tup
                                                                                                                                          (Quan.Q1)
                                                                                                                                          (Term.Tup
                                                                                                                                            (Quan.Q1)
                                                                                                                                            (Term.Lab
                                                                                                                                              "Zero")
                                                                                                                                            (Term.Lab
                                                                                                                                              "()"))
                                                                                                                                          (Term.Lab
                                                                                                                                            "()")))
                                                                                                                                      (Term.Lab
                                                                                                                                        "()")))
                                                                                                                                  (Term.Lab
                                                                                                                                    "()")))
                                                                                                                              (Term.Lab
                                                                                                                                "()")))
                                                                                                                          (Term.Lab
                                                                                                                            "()")))
                                                                                                                      (Term.Lab
                                                                                                                        "()")))
                                                                                                                  (Term.Lab
                                                                                                                    "()")))
                                                                                                              (Term.Lab
                                                                                                                "()")))
                                                                                                          (Term.Lab
                                                                                                            "()")))
                                                                                                      (Term.Lab
                                                                                                        "()")))
                                                                                                  (Term.Lab
                                                                                                    "()")))
                                                                                              (Term.Lab
                                                                                                "()")))
                                                                                          (Term.Lab
                                                                                            "()")))
                                                                                      (Term.Lab
                                                                                        "()")))
                                                                                  (Term.Lab "()")))
                                                                              (Term.Lab "()")))
                                                                          (Term.Lab "()")))
                                                                      (Term.Lab "()")))
                                                                  (Term.Lab "()")))
                                                              (Term.Lab "()")))
                                                          (Term.Lab "()")))
                                                      (Term.Lab "()")))
                                                  (Term.Lab "()")))
                                              (Term.Lab "()")))
                                          (Term.Lab "()")))
                                      (Term.Lab "()")))
                                  (Term.Lab "()")))
                              (Term.Lab "()")))
                          (Term.Lab "()")))
                      (Term.Lab "()")))
                  (Term.Lab "()")))
              (Term.Lab "()"))))
        (Term.Enu ["()"]))
      (Term.Efq),
    false⟩

def «reader.U32» : Def :=
  ⟨"U32",
    Term.Typ (Term.Lab "Q2"),
    Term.Sig (Quan.Q1) (Term.Enu ["U32"]) (Term.App (Quan.Q1) (Term.Ref "U32.arms") (Term.Var 0)),
    false⟩

def «reader.List.arms» : Def :=
  ⟨"List.arms",
    Term.All
      (Quan.Q0)
      (Term.Enu ["Q0", "Q1", "Q2"])
      (Term.All
        (Quan.Q0)
        (Term.Typ (Term.Var 0))
        (Term.All (Quan.Q1) (Term.Enu ["Nil", "Con"]) (Term.Typ (Term.Var 2)))),
    Term.Lam
      (Quan.Q0)
      (Term.Lam
        (Quan.Q0)
        (Term.Mat
          "Nil"
          (Term.Enu ["()"])
          (Term.Mat
            "Con"
            (Term.Sig
              (Quan.Q1)
              (Term.Var 0)
              (Term.Sig
                (Quan.Q1)
                (Term.App
                  (Quan.Q0)
                  (Term.App (Quan.Q0) (Term.Ref "List") (Term.Var 2))
                  (Term.Var 1))
                (Term.Enu ["()"])))
            (Term.Efq)))),
    false⟩

def «reader.List» : Def :=
  ⟨"List",
    Term.All
      (Quan.Q0)
      (Term.Enu ["Q0", "Q1", "Q2"])
      (Term.All (Quan.Q0) (Term.Typ (Term.Var 0)) (Term.Typ (Term.Var 1))),
    Term.Lam
      (Quan.Q0)
      (Term.Lam
        (Quan.Q0)
        (Term.Sig
          (Quan.Q1)
          (Term.Enu ["Nil", "Con"])
          (Term.App
            (Quan.Q1)
            (Term.App
              (Quan.Q0)
              (Term.App (Quan.Q0) (Term.Ref "List.arms") (Term.Var 2))
              (Term.Var 1))
            (Term.Var 0)))),
    false⟩

def reader : List Def :=
  [«reader.Quan.arms»,
   «reader.Quan»,
   «reader.Term.arms»,
   «reader.Term»,
   «reader.Def.arms»,
   «reader.Def»,
   «reader.Item.arms»,
   «reader.Item»,
   «reader.Book.read.succ»,
   «reader.Book.read.byte»,
   «reader.Book.read.names»,
   «reader.Book.read.defs»,
   «reader.Book.read.def»,
   «reader.Book.read.var»,
   «reader.Book.read.ref»,
   «reader.Book.read.ann»,
   «reader.Book.read.let»,
   «reader.Book.read.typ»,
   «reader.Book.read.min»,
   «reader.Book.read.all»,
   «reader.Book.read.lam»,
   «reader.Book.read.app»,
   «reader.Book.read.sig»,
   «reader.Book.read.tup»,
   «reader.Book.read.prj»,
   «reader.Book.read.enu»,
   «reader.Book.read.lab»,
   «reader.Book.read.mat»,
   «reader.Book.read.eql»,
   «reader.Book.read.rwt»,
   «reader.Book.read.token32»,
   «reader.Book.read.token24»,
   «reader.Book.read.token16»,
   «reader.Book.read.token8»,
   «reader.Book.read.token»,
   «reader.Nat.double»,
   «reader.Word.to_nat»,
   «reader.U32.to_nat»,
   «reader.Book.read.step»,
   «reader.Book.read.done»,
   «reader.Book.read.go»,
   «reader.Book.read»,
   «reader.Word.Nil.arms»,
   «reader.Word.Nil»,
   «reader.Word.Con.arms»,
   «reader.Word.Con»,
   «reader.Word»,
   «reader.Maybe.arms»,
   «reader.Maybe»,
   «reader.Bool.arms»,
   «reader.Bool»,
   «reader.Nat.arms»,
   «reader.Nat»,
   «reader.U32.arms»,
   «reader.U32»,
   «reader.List.arms»,
   «reader.List»]
