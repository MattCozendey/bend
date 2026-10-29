import Step

-- Word.Ref
-- ========
--
-- GENERATED. The bodies of base's word code, as bend -o gives them: R.k is
-- the body of def k. Made with bend 2.0.39 (repo source, in WSL) from a
-- program that calls each U32 operation, then printed with Book.parse and
-- reprStr.
-- A word jump runs only when the book's defs equal these terms. If they
-- differ, the jump does not run, and the result stays correct.

open Quan Term

def R.Bool.not : Term :=
  Term.Prj
    (Term.Mat
      "False"
      (Term.Mat "()" (Term.Tup (Quan.Q1) (Term.Lab "True") (Term.Lab "()")) (Term.Efq))
      (Term.Mat "True" (Term.Mat "()" (Term.Tup (Quan.Q1) (Term.Lab "False") (Term.Lab "()")) (Term.Efq)) (Term.Efq)))

def R.Bool.and : Term :=
  Term.Prj
    (Term.Mat
      "False"
      (Term.Mat "()" (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "False") (Term.Lab "()"))) (Term.Efq))
      (Term.Mat "True" (Term.Mat "()" (Term.Lam (Quan.Q1) (Term.Var 0)) (Term.Efq)) (Term.Efq)))

def R.Bool.or : Term :=
  Term.Prj
    (Term.Mat
      "False"
      (Term.Mat "()" (Term.Lam (Quan.Q1) (Term.Var 0)) (Term.Efq))
      (Term.Mat
        "True"
        (Term.Mat "()" (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "True") (Term.Lab "()"))) (Term.Efq))
        (Term.Efq)))

def R.Bool.xor : Term :=
  Term.Prj
    (Term.Mat
      "False"
      (Term.Mat "()" (Term.Lam (Quan.Q1) (Term.Var 0)) (Term.Efq))
      (Term.Mat
        "True"
        (Term.Mat "()" (Term.Lam (Quan.Q1) (Term.App (Quan.Q1) (Term.Ref "Bool.not") (Term.Var 0))) (Term.Efq))
        (Term.Efq)))

def R.Bool.cmp : Term :=
  Term.Prj
    (Term.Mat
      "False"
      (Term.Mat
        "()"
        (Term.Prj
          (Term.Mat
            "False"
            (Term.Mat "()" (Term.Tup (Quan.Q1) (Term.Lab "EQ") (Term.Lab "()")) (Term.Efq))
            (Term.Mat "True" (Term.Mat "()" (Term.Tup (Quan.Q1) (Term.Lab "LT") (Term.Lab "()")) (Term.Efq)) (Term.Efq))))
        (Term.Efq))
      (Term.Mat
        "True"
        (Term.Mat
          "()"
          (Term.Prj
            (Term.Mat
              "False"
              (Term.Mat "()" (Term.Tup (Quan.Q1) (Term.Lab "GT") (Term.Lab "()")) (Term.Efq))
              (Term.Mat
                "True"
                (Term.Mat "()" (Term.Tup (Quan.Q1) (Term.Lab "EQ") (Term.Lab "()")) (Term.Efq))
                (Term.Efq))))
          (Term.Efq))
        (Term.Efq)))

def R.Bool.full_add : Term :=
  Term.Prj
    (Term.Mat
      "False"
      (Term.Mat
        "()"
        (Term.Lam
          (Quan.Q2)
          (Term.Lam
            (Quan.Q2)
            (Term.Tup
              (Quan.Q1)
              (Term.Lab "Tuple")
              (Term.Tup
                (Quan.Q1)
                (Term.App (Quan.Q1) (Term.App (Quan.Q1) (Term.Ref "Bool.xor") (Term.Var 1)) (Term.Var 0))
                (Term.Tup
                  (Quan.Q1)
                  (Term.App (Quan.Q1) (Term.App (Quan.Q1) (Term.Ref "Bool.and") (Term.Var 1)) (Term.Var 0))
                  (Term.Lab "()"))))))
        (Term.Efq))
      (Term.Mat
        "True"
        (Term.Mat
          "()"
          (Term.Lam
            (Quan.Q2)
            (Term.Lam
              (Quan.Q2)
              (Term.Tup
                (Quan.Q1)
                (Term.Lab "Tuple")
                (Term.Tup
                  (Quan.Q1)
                  (Term.App
                    (Quan.Q1)
                    (Term.Ref "Bool.not")
                    (Term.App (Quan.Q1) (Term.App (Quan.Q1) (Term.Ref "Bool.xor") (Term.Var 1)) (Term.Var 0)))
                  (Term.Tup
                    (Quan.Q1)
                    (Term.App (Quan.Q1) (Term.App (Quan.Q1) (Term.Ref "Bool.or") (Term.Var 1)) (Term.Var 0))
                    (Term.Lab "()"))))))
          (Term.Efq))
        (Term.Efq)))

def R.Nat.double : Term :=
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
                    (Term.Tup (Quan.Q1) (Term.App (Quan.Q1) (Term.Ref "Nat.double") (Term.Var 0)) (Term.Lab "()")))
                  (Term.Lab "()")))
              (Term.Efq))))
        (Term.Efq)))

def R.Word.zero : Term :=
  Term.Prj
    (Term.Mat
      "Zero"
      (Term.Mat "()" (Term.Tup (Quan.Q1) (Term.Lab "WNil") (Term.Lab "()")) (Term.Efq))
      (Term.Mat
        "Succ"
        (Term.Prj
          (Term.Lam
            (Quan.Q1)
            (Term.Mat
              "()"
              (Term.Tup
                (Quan.Q1)
                (Term.Lab "WCon")
                (Term.Tup
                  (Quan.Q1)
                  (Term.Tup (Quan.Q1) (Term.Lab "False") (Term.Lab "()"))
                  (Term.Tup (Quan.Q1) (Term.App (Quan.Q1) (Term.Ref "Word.zero") (Term.Var 0)) (Term.Lab "()"))))
              (Term.Efq))))
        (Term.Efq)))

def R.Word.not : Term :=
  Term.Prj
    (Term.Mat
      "Zero"
      (Term.Mat "()" (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "WNil") (Term.Lab "()"))) (Term.Efq))
      (Term.Mat
        "Succ"
        (Term.Prj
          (Term.Lam
            (Quan.Q1)
            (Term.Mat
              "()"
              (Term.Prj
                (Term.Mat
                  "WCon"
                  (Term.Prj
                    (Term.Lam
                      (Quan.Q1)
                      (Term.Prj
                        (Term.Lam
                          (Quan.Q1)
                          (Term.Mat
                            "()"
                            (Term.Tup
                              (Quan.Q1)
                              (Term.Lab "WCon")
                              (Term.Tup
                                (Quan.Q1)
                                (Term.App (Quan.Q1) (Term.Ref "Bool.not") (Term.Var 1))
                                (Term.Tup
                                  (Quan.Q1)
                                  (Term.App
                                    (Quan.Q1)
                                    (Term.App (Quan.Q1) (Term.Ref "Word.not") (Term.Var 2))
                                    (Term.Var 0))
                                  (Term.Lab "()"))))
                            (Term.Efq))))))
                  (Term.Efq)))
              (Term.Efq))))
        (Term.Efq)))

def R.Word.and : Term :=
  Term.Prj
    (Term.Mat
      "Zero"
      (Term.Mat
        "()"
        (Term.Lam (Quan.Q1) (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "WNil") (Term.Lab "()"))))
        (Term.Efq))
      (Term.Mat
        "Succ"
        (Term.Prj
          (Term.Lam
            (Quan.Q1)
            (Term.Mat
              "()"
              (Term.Prj
                (Term.Mat
                  "WCon"
                  (Term.Prj
                    (Term.Lam
                      (Quan.Q1)
                      (Term.Prj
                        (Term.Lam
                          (Quan.Q1)
                          (Term.Mat
                            "()"
                            (Term.Prj
                              (Term.Mat
                                "WCon"
                                (Term.Prj
                                  (Term.Lam
                                    (Quan.Q1)
                                    (Term.Prj
                                      (Term.Lam
                                        (Quan.Q1)
                                        (Term.Mat
                                          "()"
                                          (Term.Tup
                                            (Quan.Q1)
                                            (Term.Lab "WCon")
                                            (Term.Tup
                                              (Quan.Q1)
                                              (Term.App
                                                (Quan.Q1)
                                                (Term.App (Quan.Q1) (Term.Ref "Bool.and") (Term.Var 3))
                                                (Term.Var 1))
                                              (Term.Tup
                                                (Quan.Q1)
                                                (Term.App
                                                  (Quan.Q1)
                                                  (Term.App
                                                    (Quan.Q1)
                                                    (Term.App (Quan.Q1) (Term.Ref "Word.and") (Term.Var 4))
                                                    (Term.Var 2))
                                                  (Term.Var 0))
                                                (Term.Lab "()"))))
                                          (Term.Efq))))))
                                (Term.Efq)))
                            (Term.Efq))))))
                  (Term.Efq)))
              (Term.Efq))))
        (Term.Efq)))

def R.Word.or : Term :=
  Term.Prj
    (Term.Mat
      "Zero"
      (Term.Mat
        "()"
        (Term.Lam (Quan.Q1) (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "WNil") (Term.Lab "()"))))
        (Term.Efq))
      (Term.Mat
        "Succ"
        (Term.Prj
          (Term.Lam
            (Quan.Q1)
            (Term.Mat
              "()"
              (Term.Prj
                (Term.Mat
                  "WCon"
                  (Term.Prj
                    (Term.Lam
                      (Quan.Q1)
                      (Term.Prj
                        (Term.Lam
                          (Quan.Q1)
                          (Term.Mat
                            "()"
                            (Term.Prj
                              (Term.Mat
                                "WCon"
                                (Term.Prj
                                  (Term.Lam
                                    (Quan.Q1)
                                    (Term.Prj
                                      (Term.Lam
                                        (Quan.Q1)
                                        (Term.Mat
                                          "()"
                                          (Term.Tup
                                            (Quan.Q1)
                                            (Term.Lab "WCon")
                                            (Term.Tup
                                              (Quan.Q1)
                                              (Term.App
                                                (Quan.Q1)
                                                (Term.App (Quan.Q1) (Term.Ref "Bool.or") (Term.Var 3))
                                                (Term.Var 1))
                                              (Term.Tup
                                                (Quan.Q1)
                                                (Term.App
                                                  (Quan.Q1)
                                                  (Term.App
                                                    (Quan.Q1)
                                                    (Term.App (Quan.Q1) (Term.Ref "Word.or") (Term.Var 4))
                                                    (Term.Var 2))
                                                  (Term.Var 0))
                                                (Term.Lab "()"))))
                                          (Term.Efq))))))
                                (Term.Efq)))
                            (Term.Efq))))))
                  (Term.Efq)))
              (Term.Efq))))
        (Term.Efq)))

def R.Word.xor : Term :=
  Term.Prj
    (Term.Mat
      "Zero"
      (Term.Mat
        "()"
        (Term.Lam (Quan.Q1) (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "WNil") (Term.Lab "()"))))
        (Term.Efq))
      (Term.Mat
        "Succ"
        (Term.Prj
          (Term.Lam
            (Quan.Q1)
            (Term.Mat
              "()"
              (Term.Prj
                (Term.Mat
                  "WCon"
                  (Term.Prj
                    (Term.Lam
                      (Quan.Q1)
                      (Term.Prj
                        (Term.Lam
                          (Quan.Q1)
                          (Term.Mat
                            "()"
                            (Term.Prj
                              (Term.Mat
                                "WCon"
                                (Term.Prj
                                  (Term.Lam
                                    (Quan.Q1)
                                    (Term.Prj
                                      (Term.Lam
                                        (Quan.Q1)
                                        (Term.Mat
                                          "()"
                                          (Term.Tup
                                            (Quan.Q1)
                                            (Term.Lab "WCon")
                                            (Term.Tup
                                              (Quan.Q1)
                                              (Term.App
                                                (Quan.Q1)
                                                (Term.App (Quan.Q1) (Term.Ref "Bool.xor") (Term.Var 3))
                                                (Term.Var 1))
                                              (Term.Tup
                                                (Quan.Q1)
                                                (Term.App
                                                  (Quan.Q1)
                                                  (Term.App
                                                    (Quan.Q1)
                                                    (Term.App (Quan.Q1) (Term.Ref "Word.xor") (Term.Var 4))
                                                    (Term.Var 2))
                                                  (Term.Var 0))
                                                (Term.Lab "()"))))
                                          (Term.Efq))))))
                                (Term.Efq)))
                            (Term.Efq))))))
                  (Term.Efq)))
              (Term.Efq))))
        (Term.Efq)))

def R.Word.inc : Term :=
  Term.Prj
    (Term.Mat
      "Zero"
      (Term.Mat "()" (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "WNil") (Term.Lab "()"))) (Term.Efq))
      (Term.Mat
        "Succ"
        (Term.Prj
          (Term.Lam
            (Quan.Q1)
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
                                (Term.Tup
                                  (Quan.Q1)
                                  (Term.Lab "WCon")
                                  (Term.Tup
                                    (Quan.Q1)
                                    (Term.Tup (Quan.Q1) (Term.Lab "True") (Term.Lab "()"))
                                    (Term.Tup (Quan.Q1) (Term.Var 0) (Term.Lab "()"))))
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
                                    (Term.Lab "WCon")
                                    (Term.Tup
                                      (Quan.Q1)
                                      (Term.Tup (Quan.Q1) (Term.Lab "False") (Term.Lab "()"))
                                      (Term.Tup
                                        (Quan.Q1)
                                        (Term.App
                                          (Quan.Q1)
                                          (Term.App (Quan.Q1) (Term.Ref "Word.inc") (Term.Var 1))
                                          (Term.Var 0))
                                        (Term.Lab "()"))))
                                  (Term.Efq))))
                            (Term.Efq))
                          (Term.Efq)))))
                  (Term.Efq)))
              (Term.Efq))))
        (Term.Efq)))

def R.Word.shl.put : Term :=
  Term.Prj
    (Term.Mat
      "Zero"
      (Term.Mat
        "()"
        (Term.Lam (Quan.Q1) (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "WNil") (Term.Lab "()"))))
        (Term.Efq))
      (Term.Mat
        "Succ"
        (Term.Prj
          (Term.Lam
            (Quan.Q1)
            (Term.Mat
              "()"
              (Term.Lam
                (Quan.Q1)
                (Term.Prj
                  (Term.Mat
                    "WCon"
                    (Term.Prj
                      (Term.Lam
                        (Quan.Q1)
                        (Term.Prj
                          (Term.Lam
                            (Quan.Q1)
                            (Term.Mat
                              "()"
                              (Term.Tup
                                (Quan.Q1)
                                (Term.Lab "WCon")
                                (Term.Tup
                                  (Quan.Q1)
                                  (Term.Var 2)
                                  (Term.Tup
                                    (Quan.Q1)
                                    (Term.App
                                      (Quan.Q1)
                                      (Term.App
                                        (Quan.Q1)
                                        (Term.App (Quan.Q1) (Term.Ref "Word.shl.put") (Term.Var 3))
                                        (Term.Var 1))
                                      (Term.Var 0))
                                    (Term.Lab "()"))))
                              (Term.Efq))))))
                    (Term.Efq))))
              (Term.Efq))))
        (Term.Efq)))

def R.Word.shl : Term :=
  Term.Prj
    (Term.Mat
      "Zero"
      (Term.Mat "()" (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "WNil") (Term.Lab "()"))) (Term.Efq))
      (Term.Mat
        "Succ"
        (Term.Prj
          (Term.Lam
            (Quan.Q1)
            (Term.Mat
              "()"
              (Term.Prj
                (Term.Mat
                  "WCon"
                  (Term.Prj
                    (Term.Lam
                      (Quan.Q1)
                      (Term.Prj
                        (Term.Lam
                          (Quan.Q1)
                          (Term.Mat
                            "()"
                            (Term.Tup
                              (Quan.Q1)
                              (Term.Lab "WCon")
                              (Term.Tup
                                (Quan.Q1)
                                (Term.Tup (Quan.Q1) (Term.Lab "False") (Term.Lab "()"))
                                (Term.Tup
                                  (Quan.Q1)
                                  (Term.App
                                    (Quan.Q1)
                                    (Term.App
                                      (Quan.Q1)
                                      (Term.App (Quan.Q1) (Term.Ref "Word.shl.put") (Term.Var 2))
                                      (Term.Var 1))
                                    (Term.Var 0))
                                  (Term.Lab "()"))))
                            (Term.Efq))))))
                  (Term.Efq)))
              (Term.Efq))))
        (Term.Efq)))

def R.Word.shr.pad : Term :=
  Term.Prj
    (Term.Mat
      "Zero"
      (Term.Mat
        "()"
        (Term.Lam
          (Quan.Q1)
          (Term.Tup
            (Quan.Q1)
            (Term.Lab "WCon")
            (Term.Tup
              (Quan.Q1)
              (Term.Tup (Quan.Q1) (Term.Lab "False") (Term.Lab "()"))
              (Term.Tup (Quan.Q1) (Term.Var 0) (Term.Lab "()")))))
        (Term.Efq))
      (Term.Mat
        "Succ"
        (Term.Prj
          (Term.Lam
            (Quan.Q1)
            (Term.Mat
              "()"
              (Term.Prj
                (Term.Mat
                  "WCon"
                  (Term.Prj
                    (Term.Lam
                      (Quan.Q1)
                      (Term.Prj
                        (Term.Lam
                          (Quan.Q1)
                          (Term.Mat
                            "()"
                            (Term.Tup
                              (Quan.Q1)
                              (Term.Lab "WCon")
                              (Term.Tup
                                (Quan.Q1)
                                (Term.Var 1)
                                (Term.Tup
                                  (Quan.Q1)
                                  (Term.App
                                    (Quan.Q1)
                                    (Term.App (Quan.Q1) (Term.Ref "Word.shr.pad") (Term.Var 2))
                                    (Term.Var 0))
                                  (Term.Lab "()"))))
                            (Term.Efq))))))
                  (Term.Efq)))
              (Term.Efq))))
        (Term.Efq)))

def R.Word.shr : Term :=
  Term.Prj
    (Term.Mat
      "Zero"
      (Term.Mat "()" (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "WNil") (Term.Lab "()"))) (Term.Efq))
      (Term.Mat
        "Succ"
        (Term.Prj
          (Term.Lam
            (Quan.Q1)
            (Term.Mat
              "()"
              (Term.Prj
                (Term.Mat
                  "WCon"
                  (Term.Prj
                    (Term.Lam
                      (Quan.Q1)
                      (Term.Prj
                        (Term.Lam
                          (Quan.Q1)
                          (Term.Mat
                            "()"
                            (Term.App (Quan.Q1) (Term.App (Quan.Q1) (Term.Ref "Word.shr.pad") (Term.Var 2)) (Term.Var 0))
                            (Term.Efq))))))
                  (Term.Efq)))
              (Term.Efq))))
        (Term.Efq)))

def R.Word.cmp.fin : Term :=
  Term.Lam
    (Quan.Q1)
    (Term.Lam
      (Quan.Q1)
      (Term.Prj
        (Term.Mat
          "LT"
          (Term.Mat "()" (Term.Tup (Quan.Q1) (Term.Lab "LT") (Term.Lab "()")) (Term.Efq))
          (Term.Mat
            "EQ"
            (Term.Mat
              "()"
              (Term.App (Quan.Q1) (Term.App (Quan.Q1) (Term.Ref "Bool.cmp") (Term.Var 1)) (Term.Var 0))
              (Term.Efq))
            (Term.Mat "GT" (Term.Mat "()" (Term.Tup (Quan.Q1) (Term.Lab "GT") (Term.Lab "()")) (Term.Efq)) (Term.Efq))))))

def R.Word.cmp : Term :=
  Term.Prj
    (Term.Mat
      "Zero"
      (Term.Mat
        "()"
        (Term.Lam (Quan.Q1) (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "EQ") (Term.Lab "()"))))
        (Term.Efq))
      (Term.Mat
        "Succ"
        (Term.Prj
          (Term.Lam
            (Quan.Q1)
            (Term.Mat
              "()"
              (Term.Prj
                (Term.Mat
                  "WCon"
                  (Term.Prj
                    (Term.Lam
                      (Quan.Q1)
                      (Term.Prj
                        (Term.Lam
                          (Quan.Q1)
                          (Term.Mat
                            "()"
                            (Term.Prj
                              (Term.Mat
                                "WCon"
                                (Term.Prj
                                  (Term.Lam
                                    (Quan.Q1)
                                    (Term.Prj
                                      (Term.Lam
                                        (Quan.Q1)
                                        (Term.Mat
                                          "()"
                                          (Term.App
                                            (Quan.Q1)
                                            (Term.App
                                              (Quan.Q1)
                                              (Term.App (Quan.Q1) (Term.Ref "Word.cmp.fin") (Term.Var 3))
                                              (Term.Var 1))
                                            (Term.App
                                              (Quan.Q1)
                                              (Term.App
                                                (Quan.Q1)
                                                (Term.App (Quan.Q1) (Term.Ref "Word.cmp") (Term.Var 4))
                                                (Term.Var 2))
                                              (Term.Var 0)))
                                          (Term.Efq))))))
                                (Term.Efq)))
                            (Term.Efq))))))
                  (Term.Efq)))
              (Term.Efq))))
        (Term.Efq)))

def R.Word.to_nat : Term :=
  Term.Prj
    (Term.Mat
      "Zero"
      (Term.Mat "()" (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "Zero") (Term.Lab "()"))) (Term.Efq))
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
                                          (Term.App (Quan.Q1) (Term.Ref "Word.to_nat") (Term.Var 1))
                                          (Term.Var 0)))
                                      (Term.Lab "()")))
                                  (Term.Efq))))
                            (Term.Efq))
                          (Term.Efq)))))
                  (Term.Efq)))
              (Term.Efq))))
        (Term.Efq)))

def R.Word.adc.group : Term :=
  Term.Lam
    (Quan.Q1)
    (Term.Lam
      (Quan.Q1)
      (Term.Lam
        (Quan.Q1)
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
                  (Term.App
                    (Quan.Q1)
                    (Term.App
                      (Quan.Q1)
                      (Term.Prj
                        (Term.Mat
                          "Word.adc"
                          (Term.Mat
                            "()"
                            (Term.Lam
                              (Quan.Q1)
                              (Term.Lam
                                (Quan.Q1)
                                (Term.Lam
                                  (Quan.Q1)
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
                                            (Term.App
                                              (Quan.Q1)
                                              (Term.App
                                                (Quan.Q1)
                                                (Term.Prj
                                                  (Term.Mat
                                                    "Zero"
                                                    (Term.Mat
                                                      "()"
                                                      (Term.Lam
                                                        (Quan.Q1)
                                                        (Term.Lam
                                                          (Quan.Q1)
                                                          (Term.Lam
                                                            (Quan.Q1)
                                                            (Term.Lam
                                                              (Quan.Q1)
                                                              (Term.Tup (Quan.Q1) (Term.Lab "WNil") (Term.Lab "()"))))))
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
                                                                  (Term.Lam
                                                                    (Quan.Q2)
                                                                    (Term.Prj
                                                                      (Term.Lam
                                                                        (Quan.Q2)
                                                                        (Term.Mat
                                                                          "()"
                                                                          (Term.Prj
                                                                            (Term.Mat
                                                                              "WCon"
                                                                              (Term.Prj
                                                                                (Term.Lam
                                                                                  (Quan.Q2)
                                                                                  (Term.Prj
                                                                                    (Term.Lam
                                                                                      (Quan.Q2)
                                                                                      (Term.Mat
                                                                                        "()"
                                                                                        (Term.Prj
                                                                                          (Term.Mat
                                                                                            "False"
                                                                                            (Term.Mat
                                                                                              "()"
                                                                                              (Term.Lam
                                                                                                (Quan.Q1)
                                                                                                (Term.Ann
                                                                                                  (Term.App
                                                                                                    (Quan.Q1)
                                                                                                    (Term.App
                                                                                                      (Quan.Q1)
                                                                                                      (Term.App
                                                                                                        (Quan.Q1)
                                                                                                        (Term.App
                                                                                                          (Quan.Q1)
                                                                                                          (Term.App
                                                                                                            (Quan.Q1)
                                                                                                            (Term.App
                                                                                                              (Quan.Q1)
                                                                                                              (Term.Ref
                                                                                                                "Word.adc.group")
                                                                                                              (Term.Var
                                                                                                                5))
                                                                                                            (Term.Var 3))
                                                                                                          (Term.Var 1))
                                                                                                        (Term.Tup
                                                                                                          (Quan.Q1)
                                                                                                          (Term.Lab
                                                                                                            "False")
                                                                                                          (Term.Lab
                                                                                                            "()")))
                                                                                                      (Term.Tup
                                                                                                        (Quan.Q1)
                                                                                                        (Term.Lab
                                                                                                          "Word.adc.con")
                                                                                                        (Term.Tup
                                                                                                          (Quan.Q1)
                                                                                                          (Term.Tup
                                                                                                            (Quan.Q1)
                                                                                                            (Term.Lab
                                                                                                              "Word.adc")
                                                                                                            (Term.Lab
                                                                                                              "()"))
                                                                                                          (Term.Lab
                                                                                                            "()"))))
                                                                                                    (Term.App
                                                                                                      (Quan.Q2)
                                                                                                      (Term.App
                                                                                                        (Quan.Q2)
                                                                                                        (Term.App
                                                                                                          (Quan.Q1)
                                                                                                          (Term.Ref
                                                                                                            "Bool.full_add")
                                                                                                          (Term.Var 4))
                                                                                                        (Term.Var 2))
                                                                                                      (Term.Var 0)))
                                                                                                  (Term.App
                                                                                                    (Quan.Q1)
                                                                                                    (Term.Ref "Word")
                                                                                                    (Term.Tup
                                                                                                      (Quan.Q1)
                                                                                                      (Term.Lab "Succ")
                                                                                                      (Term.Tup
                                                                                                        (Quan.Q1)
                                                                                                        (Term.Var 5)
                                                                                                        (Term.Lab
                                                                                                          "()"))))))
                                                                                              (Term.Efq))
                                                                                            (Term.Mat
                                                                                              "True"
                                                                                              (Term.Mat
                                                                                                "()"
                                                                                                (Term.Lam
                                                                                                  (Quan.Q1)
                                                                                                  (Term.Ann
                                                                                                    (Term.App
                                                                                                      (Quan.Q1)
                                                                                                      (Term.App
                                                                                                        (Quan.Q1)
                                                                                                        (Term.App
                                                                                                          (Quan.Q1)
                                                                                                          (Term.App
                                                                                                            (Quan.Q1)
                                                                                                            (Term.App
                                                                                                              (Quan.Q1)
                                                                                                              (Term.App
                                                                                                                (Quan.Q1)
                                                                                                                (Term.Ref
                                                                                                                  "Word.adc.group")
                                                                                                                (Term.Var
                                                                                                                  5))
                                                                                                              (Term.Var
                                                                                                                3))
                                                                                                            (Term.Var 1))
                                                                                                          (Term.Tup
                                                                                                            (Quan.Q1)
                                                                                                            (Term.Lab
                                                                                                              "True")
                                                                                                            (Term.Lab
                                                                                                              "()")))
                                                                                                        (Term.Tup
                                                                                                          (Quan.Q1)
                                                                                                          (Term.Lab
                                                                                                            "Word.adc.con")
                                                                                                          (Term.Tup
                                                                                                            (Quan.Q1)
                                                                                                            (Term.Tup
                                                                                                              (Quan.Q1)
                                                                                                              (Term.Lab
                                                                                                                "Word.adc")
                                                                                                              (Term.Lab
                                                                                                                "()"))
                                                                                                            (Term.Lab
                                                                                                              "()"))))
                                                                                                      (Term.App
                                                                                                        (Quan.Q2)
                                                                                                        (Term.App
                                                                                                          (Quan.Q2)
                                                                                                          (Term.App
                                                                                                            (Quan.Q1)
                                                                                                            (Term.Ref
                                                                                                              "Bool.full_add")
                                                                                                            (Term.Var 4))
                                                                                                          (Term.App
                                                                                                            (Quan.Q1)
                                                                                                            (Term.Ref
                                                                                                              "Bool.not")
                                                                                                            (Term.Var 2)))
                                                                                                        (Term.Var 0)))
                                                                                                    (Term.App
                                                                                                      (Quan.Q1)
                                                                                                      (Term.Ref "Word")
                                                                                                      (Term.Tup
                                                                                                        (Quan.Q1)
                                                                                                        (Term.Lab "Succ")
                                                                                                        (Term.Tup
                                                                                                          (Quan.Q1)
                                                                                                          (Term.Var 5)
                                                                                                          (Term.Lab
                                                                                                            "()"))))))
                                                                                                (Term.Efq))
                                                                                              (Term.Efq))))
                                                                                        (Term.Efq))))))
                                                                              (Term.Efq)))
                                                                          (Term.Efq))))))
                                                                (Term.Efq)))
                                                            (Term.Efq))))
                                                      (Term.Efq))))
                                                (Term.Var 4))
                                              (Term.Var 3))
                                            (Term.Var 2))
                                          (Term.Var 1))
                                        (Term.Var 0)))))))
                            (Term.Efq))
                          (Term.Mat
                            "Word.adc.con"
                            (Term.Prj
                              (Term.Prj
                                (Term.Mat
                                  "Word.adc"
                                  (Term.Mat
                                    "()"
                                    (Term.Mat
                                      "()"
                                      (Term.Lam
                                        (Quan.Q1)
                                        (Term.Lam
                                          (Quan.Q1)
                                          (Term.Lam
                                            (Quan.Q1)
                                            (Term.Lam
                                              (Quan.Q1)
                                              (Term.Lam
                                                (Quan.Q1)
                                                (Term.App
                                                  (Quan.Q1)
                                                  (Term.Prj
                                                    (Term.Mat
                                                      "Tuple"
                                                      (Term.Prj
                                                        (Term.Lam
                                                          (Quan.Q1)
                                                          (Term.Prj
                                                            (Term.Lam
                                                              (Quan.Q1)
                                                              (Term.Mat
                                                                "()"
                                                                (Term.Tup
                                                                  (Quan.Q1)
                                                                  (Term.Lab "WCon")
                                                                  (Term.Tup
                                                                    (Quan.Q1)
                                                                    (Term.Var 1)
                                                                    (Term.Tup
                                                                      (Quan.Q1)
                                                                      (Term.Ann
                                                                        (Term.App
                                                                          (Quan.Q1)
                                                                          (Term.App
                                                                            (Quan.Q1)
                                                                            (Term.App
                                                                              (Quan.Q1)
                                                                              (Term.App
                                                                                (Quan.Q1)
                                                                                (Term.App
                                                                                  (Quan.Q1)
                                                                                  (Term.App
                                                                                    (Quan.Q1)
                                                                                    (Term.Ref "Word.adc.group")
                                                                                    (Term.Var 6))
                                                                                  (Term.Var 5))
                                                                                (Term.Var 4))
                                                                              (Term.Var 3))
                                                                            (Term.Tup
                                                                              (Quan.Q1)
                                                                              (Term.Lab "Word.adc")
                                                                              (Term.Lab "()")))
                                                                          (Term.Var 0))
                                                                        (Term.App
                                                                          (Quan.Q1)
                                                                          (Term.Ref "Word")
                                                                          (Term.Var 6)))
                                                                      (Term.Lab "()"))))
                                                                (Term.Efq))))))
                                                      (Term.Efq)))
                                                  (Term.Var 0)))))))
                                      (Term.Efq))
                                    (Term.Efq))
                                  (Term.Efq))))
                            (Term.Efq))))
                      (Term.Var 0))
                    (Term.Var 4))
                  (Term.Var 3))
                (Term.Var 2))
              (Term.Var 1))))))

def R.Word.add : Term :=
  Term.Lam
    (Quan.Q1)
    (Term.Lam
      (Quan.Q1)
      (Term.Lam
        (Quan.Q1)
        (Term.Ann
          (Term.App
            (Quan.Q1)
            (Term.App
              (Quan.Q1)
              (Term.App
                (Quan.Q1)
                (Term.App
                  (Quan.Q1)
                  (Term.App (Quan.Q1) (Term.App (Quan.Q1) (Term.Ref "Word.adc.group") (Term.Var 2)) (Term.Var 1))
                  (Term.Var 0))
                (Term.Tup (Quan.Q1) (Term.Lab "False") (Term.Lab "()")))
              (Term.Tup (Quan.Q1) (Term.Lab "Word.adc") (Term.Lab "()")))
            (Term.Tup (Quan.Q1) (Term.Lab "False") (Term.Lab "()")))
          (Term.App (Quan.Q1) (Term.Ref "Word") (Term.Var 2)))))

def R.Word.mul.go : Term :=
  Term.Lam
    (Quan.Q2)
    (Term.Prj
      (Term.Mat
        "Zero"
        (Term.Mat "()" (Term.Lam (Quan.Q1) (Term.Lam (Quan.Q2) (Term.Lam (Quan.Q1) (Term.Var 0)))) (Term.Efq))
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
                                  (Term.Lam
                                    (Quan.Q2)
                                    (Term.Lam
                                      (Quan.Q1)
                                      (Term.App
                                        (Quan.Q1)
                                        (Term.App
                                          (Quan.Q2)
                                          (Term.App
                                            (Quan.Q1)
                                            (Term.App
                                              (Quan.Q1)
                                              (Term.App (Quan.Q2) (Term.Ref "Word.mul.go") (Term.Var 4))
                                              (Term.Var 3))
                                            (Term.Var 2))
                                          (Term.App
                                            (Quan.Q1)
                                            (Term.App (Quan.Q1) (Term.Ref "Word.shl") (Term.Var 4))
                                            (Term.Var 1)))
                                        (Term.Var 0))))
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
                                    (Term.Lam
                                      (Quan.Q2)
                                      (Term.Lam
                                        (Quan.Q1)
                                        (Term.App
                                          (Quan.Q1)
                                          (Term.App
                                            (Quan.Q2)
                                            (Term.App
                                              (Quan.Q1)
                                              (Term.App
                                                (Quan.Q1)
                                                (Term.App (Quan.Q2) (Term.Ref "Word.mul.go") (Term.Var 4))
                                                (Term.Var 3))
                                              (Term.Var 2))
                                            (Term.App
                                              (Quan.Q1)
                                              (Term.App (Quan.Q1) (Term.Ref "Word.shl") (Term.Var 4))
                                              (Term.Var 1)))
                                          (Term.App
                                            (Quan.Q1)
                                            (Term.App
                                              (Quan.Q1)
                                              (Term.App (Quan.Q1) (Term.Ref "Word.add") (Term.Var 4))
                                              (Term.Var 0))
                                            (Term.Var 1)))))
                                    (Term.Efq))))
                              (Term.Efq))
                            (Term.Efq)))))
                    (Term.Efq)))
                (Term.Efq))))
          (Term.Efq))))

