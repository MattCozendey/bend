import bendtt

-- Made by scripts/Copy.lean from the `bend -o` output of a file that uses Base's Exists (impl.bend uses none yet),
-- for the roots Exists, and the defs that they need. Do not edit it.

open Quan Term

def «existsCopy.Sigma.arms» : Def :=
  ⟨"Sigma.arms",
    Term.All
      (Quan.Q0)
      (Term.Enu ["Q0", "Q1", "Q2"])
      (Term.All
        (Quan.Q0)
        (Term.Enu ["Q0", "Q1", "Q2"])
        (Term.All
          (Quan.Q0)
          (Term.Typ (Term.Var 1))
          (Term.All
            (Quan.Q0)
            (Term.All (Quan.Q0) (Term.Var 0) (Term.Typ (Term.Var 2)))
            (Term.All
              (Quan.Q1)
              (Term.Enu ["Tuple"])
              (Term.Typ (Term.Min (Term.Var 4) (Term.Var 3))))))),
    Term.Lam
      (Quan.Q0)
      (Term.Lam
        (Quan.Q0)
        (Term.Lam
          (Quan.Q0)
          (Term.Lam
            (Quan.Q0)
            (Term.Mat
              "Tuple"
              (Term.Sig
                (Quan.Q1)
                (Term.Var 1)
                (Term.Sig
                  (Quan.Q1)
                  (Term.App (Quan.Q0) (Term.Var 1) (Term.Var 0))
                  (Term.Enu ["()"])))
              (Term.Efq))))),
    false⟩

def «existsCopy.Sigma» : Def :=
  ⟨"Sigma",
    Term.All
      (Quan.Q0)
      (Term.Enu ["Q0", "Q1", "Q2"])
      (Term.All
        (Quan.Q0)
        (Term.Enu ["Q0", "Q1", "Q2"])
        (Term.All
          (Quan.Q0)
          (Term.Typ (Term.Var 1))
          (Term.All
            (Quan.Q0)
            (Term.All (Quan.Q0) (Term.Var 0) (Term.Typ (Term.Var 2)))
            (Term.Typ (Term.Min (Term.Var 3) (Term.Var 2)))))),
    Term.Lam
      (Quan.Q0)
      (Term.Lam
        (Quan.Q0)
        (Term.Lam
          (Quan.Q0)
          (Term.Lam
            (Quan.Q0)
            (Term.Sig
              (Quan.Q1)
              (Term.Enu ["Tuple"])
              (Term.App
                (Quan.Q1)
                (Term.App
                  (Quan.Q0)
                  (Term.App
                    (Quan.Q0)
                    (Term.App
                      (Quan.Q0)
                      (Term.App (Quan.Q0) (Term.Ref "Sigma.arms") (Term.Var 4))
                      (Term.Var 3))
                    (Term.Var 2))
                  (Term.Var 1))
                (Term.Var 0)))))),
    false⟩

def «existsCopy.Exists» : Def :=
  ⟨"Exists",
    Term.All
      (Quan.Q0)
      (Term.Typ (Term.Lab "Q1"))
      (Term.All
        (Quan.Q0)
        (Term.All (Quan.Q0) (Term.Var 0) (Term.Typ (Term.Lab "Q1")))
        (Term.Typ (Term.Lab "Q1"))),
    Term.Lam
      (Quan.Q0)
      (Term.Lam
        (Quan.Q0)
        (Term.App
          (Quan.Q0)
          (Term.App
            (Quan.Q0)
            (Term.App
              (Quan.Q0)
              (Term.App (Quan.Q0) (Term.Ref "Sigma") (Term.Lab "Q1"))
              (Term.Lab "Q1"))
            (Term.Var 1))
          (Term.Lam (Quan.Q0) (Term.App (Quan.Q0) (Term.Var 1) (Term.Var 0))))),
    false⟩

def existsCopy : List Def :=
  [«existsCopy.Sigma.arms»,
   «existsCopy.Sigma»,
   «existsCopy.Exists»]
