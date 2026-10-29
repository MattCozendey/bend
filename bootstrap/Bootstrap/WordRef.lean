import Bootstrap.Step

-- WordRef
-- =======
--
-- GENERATED. The bodies of base's word add code, as bend -o gives them.
-- Made with bend 2.0.39 (repo source, in WSL) from a program that calls
-- U32.add, then printed with Book.parse and reprStr.
-- A word jump runs only when the book's defs equal these terms. If they
-- differ, the jump does not run, and the result stays correct.

open Quan Term

def refNot : Term :=
  Term.Prj
    (Term.Mat
      "False"
      (Term.Mat "()" (Term.Tup (Quan.Q1) (Term.Lab "True") (Term.Lab "()")) (Term.Efq))
      (Term.Mat "True" (Term.Mat "()" (Term.Tup (Quan.Q1) (Term.Lab "False") (Term.Lab "()")) (Term.Efq)) (Term.Efq)))

def refXor : Term :=
  Term.Prj
    (Term.Mat
      "False"
      (Term.Mat "()" (Term.Lam (Quan.Q1) (Term.Var 0)) (Term.Efq))
      (Term.Mat
        "True"
        (Term.Mat "()" (Term.Lam (Quan.Q1) (Term.App (Quan.Q1) (Term.Ref "Bool.not") (Term.Var 0))) (Term.Efq))
        (Term.Efq)))

def refAnd : Term :=
  Term.Prj
    (Term.Mat
      "False"
      (Term.Mat "()" (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "False") (Term.Lab "()"))) (Term.Efq))
      (Term.Mat "True" (Term.Mat "()" (Term.Lam (Quan.Q1) (Term.Var 0)) (Term.Efq)) (Term.Efq)))

def refOr : Term :=
  Term.Prj
    (Term.Mat
      "False"
      (Term.Mat "()" (Term.Lam (Quan.Q1) (Term.Var 0)) (Term.Efq))
      (Term.Mat
        "True"
        (Term.Mat "()" (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "True") (Term.Lab "()"))) (Term.Efq))
        (Term.Efq)))

def refFullAdd : Term :=
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

def refGroup : Term :=
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

