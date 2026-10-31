import Bootstrap.EvalSteps.Name
import Bootstrap.EvalSteps.Subst

-- EvalSteps.Walk
-- ==============
--
-- The defs of the Eval copy on spines, and its walk of a case tree.

open Quan Term

namespace EvalCopy

theorem head_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Term.head") [(Q1, Form.term t)]) (Form.term (unspine t []).1) := by
  have hk : Book.get B "Term.head" = some «evalCopy.Term.head» :=
    h «evalCopy.Term.head» (by simp [evalCopy])
  induction t with
  | App q f x ihf _ =>
    rw [unspine, unspine_app]
    refine .step (Eval.walk hk (.cons (fun _ => value_term) .nil) ?_) ihf
    simp [«evalCopy.Term.head», walk, Form.term, ctor, bindsAt, Quan.live, takes, Quan.fld,
        Term.sub, Env.sub, Term.spine, unspine]
  | _ =>
    refine .step (Eval.walk hk (.cons (fun _ => value_term) .nil) ?_) (.refl value_term)
    simp [«evalCopy.Term.head», walk, Form.term, ctor, bindsAt, Quan.live, takes, Quan.fld,
        Term.sub, Env.sub, Term.spine, unspine]

theorem args_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Term.args") [(Q1, Form.term t), (Q1, Form.args xs)])
      (Form.args (unspine t xs).2) := by
  have hk : Book.get B "Term.args" = some «evalCopy.Term.args» :=
    h «evalCopy.Term.args» (by simp [evalCopy])
  have vs : ∀ u ys, Values B [(Q1, Form.term u), (Q1, Form.args ys)] := fun _ _ =>
    .cons (fun _ => value_term) (.cons (fun _ => value_args_form) .nil)
  induction t generalizing xs with
  | App q f x ihf _ =>
    refine .step (Eval.walk hk (vs _ _) ?_) ihf
    simp [«evalCopy.Term.args», walk, Form.term, Form.args, Form.arg, list, ctor, bindsAt,
        Quan.live, takes, Quan.fld, Term.sub, Env.sub, Term.spine]
  | _ =>
    refine .step (Eval.walk hk (vs _ _) ?_) (.refl value_args_form)
    simp [«evalCopy.Term.args», walk, Form.term, ctor, bindsAt, Quan.live, takes, Quan.fld,
        Term.sub, Env.sub, Term.spine, unspine]

theorem spine_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Term.spine") [(Q1, Form.args xs), (Q1, Form.term t)])
      (Form.term (Term.spine t xs)) := by
  have hk : Book.get B "Term.spine" = some «evalCopy.Term.spine» :=
    h «evalCopy.Term.spine» (by simp [evalCopy])
  have vs : ∀ ys u, Values B [(Q1, Form.args ys), (Q1, Form.term u)] := fun _ _ =>
    .cons (fun _ => value_args_form) (.cons (fun _ => value_term) .nil)
  induction xs generalizing t with
  | cons a xs ih =>
    obtain ⟨q, x⟩ := a
    refine .step (Eval.walk hk (vs _ _) ?_) (ih (t := App q t x))
    simp [«evalCopy.Term.spine», walk, Form.term, Form.args, Form.arg, list, ctor, bindsAt,
        Quan.live, takes, Quan.fld, Term.sub, Env.sub, Term.spine]
  | nil =>
    refine .step (Eval.walk hk (vs _ _) ?_) (.refl value_term)
    simp [«evalCopy.Term.spine», walk, Form.args, list, ctor, bindsAt, Quan.live, takes, Quan.fld,
        Term.sub, Env.sub, Term.spine]


-- a run of the argument, after a function that is a value
private theorem runs_x (vf : Value B f) (l : q.live = true) (rx : Runs B x x')
    (r : Runs B (App q f x') v) : Runs B (App q f x) v :=
  have ⟨_, s, _⟩ := rx; .steps (s.app_x vf l) r

-- a run of the argument, under one more application
private theorem runs_x2 (vf : Value B f) (l : q.live = true) (rx : Runs B x x')
    (r : Runs B (App q2 (App q f x') y) v) : Runs B (App q2 (App q f x) y) v :=
  have ⟨_, s, _⟩ := rx; .steps (s.app_x vf l).app_f r

-- a run of the argument, under two more applications
private theorem runs_x3 (vf : Value B f) (l : q.live = true) (rx : Runs B x x')
    (r : Runs B (App q3 (App q2 (App q f x') y) z) v) : Runs B (App q3 (App q2 (App q f x) y) z) v :=
  have ⟨_, s, _⟩ := rx; .steps (s.app_x vf l).app_f.app_f r

-- the first field of a pair takes its steps
private theorem steps_tup_a (l : q.live = true) (h : Steps B n a a') :
    Steps B n (Tup q a b) (Tup q a' b) := by
  induction h with
  | refl => exact .refl
  | step e _ ih => exact .step (.tup_a l e) ih

-- the second field of a pair takes its steps, after a first field that is a value
private theorem steps_tup_b (va : Value B a) (h : Steps B n b b') :
    Steps B n (Tup q a b) (Tup q a b') := by
  induction h with
  | refl => exact .refl
  | step e _ ih => exact .step (.tup_b (fun _ => va) e) ih

-- a pair whose first field runs, beside a value
private theorem runs_tup_a (ra : Runs B a a') (vb : Value B b) : Runs B (Tup Q1 a b) (Tup Q1 a' b) :=
  have ⟨_, s, va⟩ := ra; ⟨_, steps_tup_a rfl s, .tup (fun _ => va) vb⟩

-- a pair whose second field runs, after a value
private theorem runs_tup_b (va : Value B a) (rb : Runs B b b') : Runs B (Tup Q1 a b) (Tup Q1 a b') :=
  have ⟨_, s, vb⟩ := rb; ⟨_, steps_tup_b va s, .tup (fun _ => va) vb⟩

-- a run reaches any term equal to its value
private theorem runs_eq (r : Runs B e v) (h : v = v') : Runs B e v' := h ▸ r

-- a call whose walk needs more arguments is a value
private theorem value_call (hk : Book.get B k = some d) (vs : Values B xs)
    (w : walk B d.v [] xs = some none) : Value B (spine (Ref k) xs) := .call hk vs (walk_iff.1 w)

-- the forms are Data, computed
private theorem data_fterm : data (Form.term t) = true := data_iff.2 data_term
private theorem data_fquan : data (Form.quan q) = true := data_iff.2 data_quan
private theorem data_fnat : data (Form.nat n) = true := data_iff.2 data_nat
private theorem data_fname : data (Form.name k) = true := data_iff.2 (data_bytes)
private theorem data_fenv : data (Form.env e) = true := data_iff.2 data_env
private theorem data_fargs : data (Form.args xs) = true := data_iff.2 data_args_form
private theorem data_fnames : data (list (List.map Form.name ks)) = true :=
  data_iff.2 (data_list fun _ hx => by obtain ⟨_, -, rfl⟩ := List.mem_map.1 hx; exact data_bytes)

-- the form of a nonempty environment
private theorem env_cons : Form.env (x :: e) = ctor "Con" [Form.term x, Form.env e] := rfl

-- the form of an empty argument list
private theorem args_nil : Form.args [] = ctor "Nil" [] := rfl

-- the form of a nonempty argument list
private theorem args_cons : Form.args (a :: xs) = ctor "Con" [Form.arg a, Form.args xs] := rfl

-- the result of a walk is a value
private theorem value_res : Value B (Form.maybe (Form.maybe Form.term) o) :=
  value_maybe fun _ => value_maybe fun _ => value_term

-- Eval.walk.if gives its result when its test holds, and none else
private theorem if_run (h : Contains B evalCopy) (ra : Runs B a (Form.bool b))
    (rc : Runs B c (Form.maybe (Form.maybe Form.term) o)) :
    Runs B (spine (Ref "Eval.walk.if") [(Q1, a), (Q1, c)])
      (Form.maybe (Form.maybe Form.term) (if b then o else none)) := by
  have hk := h «evalCopy.Eval.walk.if» (by simp [evalCopy])
  have v0 : Value B (Ref "Eval.walk.if") := value_call (xs := []) hk .nil
    (by simp [«evalCopy.Eval.walk.if», walk, takes])
  have v1 : Value B (App Q1 (Ref "Eval.walk.if") (Form.bool b)) :=
    value_call (xs := [(Q1, _)]) hk (.cons (fun _ => value_bool) .nil)
      (by cases b <;> simp [«evalCopy.Eval.walk.if», walk, takes, Form.bool, ctor, Quan.fld,
          Quan.live])
  refine runs_x2 v0 rfl ra (runs_x v1 rfl rc (.step (Eval.walk hk (xs := [(Q1, _), (Q1, _)])
    (.cons (fun _ => value_bool) (.cons (fun _ => value_res) .nil)) ?_) (.refl value_res)))
  cases b <;> simp [«evalCopy.Eval.walk.if», walk, takes, Form.bool, ctor, Quan.fld, Quan.live,
    bindsAt, Term.sub, Env.sub, Term.spine, Form.maybe]

-- Eval.walk.pick gives its first result when its test holds, and its second else
private theorem pick_run (h : Contains B evalCopy) (ra : Runs B a (Form.bool b))
    (rc : Runs B c (Form.maybe (Form.maybe Form.term) o))
    (rd : Runs B d (Form.maybe (Form.maybe Form.term) o')) :
    Runs B (spine (Ref "Eval.walk.pick") [(Q1, a), (Q1, c), (Q1, d)])
      (Form.maybe (Form.maybe Form.term) (if b then o else o')) := by
  have hk := h «evalCopy.Eval.walk.pick» (by simp [evalCopy])
  have v0 : Value B (Ref "Eval.walk.pick") := value_call (xs := []) hk .nil
    (by simp [«evalCopy.Eval.walk.pick», walk, takes])
  have v1 : Value B (App Q1 (Ref "Eval.walk.pick") (Form.bool b)) :=
    value_call (xs := [(Q1, _)]) hk (.cons (fun _ => value_bool) .nil)
      (by cases b <;> simp [«evalCopy.Eval.walk.pick», walk, takes, Form.bool, ctor, Quan.fld,
          Quan.live])
  have v2 : Value B (App Q1 (App Q1 (Ref "Eval.walk.pick") (Form.bool b))
      (Form.maybe (Form.maybe Form.term) o)) :=
    value_call (xs := [(Q1, _), (Q1,
        _)]) hk (.cons (fun _ => value_bool) (.cons (fun _ => value_res) .nil))
      (by cases b <;> simp [«evalCopy.Eval.walk.pick», walk, takes, Form.bool, ctor, Quan.fld,
        Quan.live, bindsAt])
  refine runs_x3 v0 rfl ra (runs_x2 v1 rfl rc (runs_x v2 rfl rd (.step (Eval.walk hk
    (xs := [(Q1, _), (Q1, _), (Q1, _)])
    (.cons (fun _ => value_bool) (.cons (fun _ => value_res) (.cons (fun _ => value_res) .nil))) ?_)
    (.refl value_res))))
  cases b <;> simp [«evalCopy.Eval.walk.pick», walk, takes, Form.bool, ctor, Quan.fld, Quan.live,
    bindsAt, Term.sub, Env.sub, Term.spine]

-- Eval.walk.app gives the walk on when its test holds, and the leaf u else
private theorem app_run (h : Contains B evalCopy) (ra : Runs B a (Form.bool b))
    (rc : Runs B c (Form.maybe (Form.maybe Form.term) o)) (rd : Runs B d (Form.term u)) :
    Runs B (spine (Ref "Eval.walk.app") [(Q1, a), (Q1, c), (Q1, d)])
      (Form.maybe (Form.maybe Form.term) (if b then o else some (some u))) := by
  have hk := h «evalCopy.Eval.walk.app» (by simp [evalCopy])
  have v0 : Value B (Ref "Eval.walk.app") := value_call (xs := []) hk .nil
    (by simp [«evalCopy.Eval.walk.app», walk, takes])
  have v1 : Value B (App Q1 (Ref "Eval.walk.app") (Form.bool b)) :=
    value_call (xs := [(Q1, _)]) hk (.cons (fun _ => value_bool) .nil)
      (by cases b <;> simp [«evalCopy.Eval.walk.app», walk, takes, Form.bool, ctor, Quan.fld,
          Quan.live])
  have v2 : Value B (App Q1 (App Q1 (Ref "Eval.walk.app") (Form.bool b))
      (Form.maybe (Form.maybe Form.term) o)) :=
    value_call (xs := [(Q1, _), (Q1,
        _)]) hk (.cons (fun _ => value_bool) (.cons (fun _ => value_res) .nil))
      (by cases b <;> simp [«evalCopy.Eval.walk.app», walk, takes, Form.bool, ctor, Quan.fld,
        Quan.live, bindsAt])
  refine runs_x3 v0 rfl ra (runs_x2 v1 rfl rc (runs_x v2 rfl rd (.step (Eval.walk hk
    (xs := [(Q1, _), (Q1, _), (Q1, _)])
    (.cons (fun _ => value_bool) (.cons (fun _ => value_res) (.cons (fun _ => value_term) .nil))) ?_)
    (.refl value_res))))
  cases b <;> simp [«evalCopy.Eval.walk.app», walk, takes, Form.bool, ctor, Quan.fld, Quan.live,
    bindsAt, Term.sub, Env.sub, Term.spine, Form.maybe, Form.some]

-- Eval.walk.leaf needs more arguments at a node with none left, fails at a node
-- with some left, and gives the leaf u else
private theorem leaf_run (h : Contains B evalCopy) (ra : Runs B a (Form.bool b))
    (rd : Runs B d (Form.term u)) :
    Runs B (spine (Ref "Eval.walk.leaf") [(Q1, a), (Q1, Form.args ys), (Q1, d)])
      (Form.maybe (Form.maybe Form.term)
        (if b then (if ys.isEmpty then some none else none) else some (some u))) := by
  have hk := h «evalCopy.Eval.walk.leaf» (by simp [evalCopy])
  have v0 : Value B (Ref "Eval.walk.leaf") := value_call (xs := []) hk .nil
    (by simp [«evalCopy.Eval.walk.leaf», walk, takes])
  have v2 : Value B (App Q1 (App Q1 (Ref "Eval.walk.leaf") (Form.bool b)) (Form.args ys)) :=
    value_call (xs := [(Q1, _), (Q1, _)]) hk
      (.cons (fun _ => value_bool) (.cons (fun _ => value_args_form) .nil))
      (by cases b <;> cases ys <;> simp [«evalCopy.Eval.walk.leaf», walk, takes, Form.bool, ctor,
        Quan.fld, Quan.live, bindsAt, args_nil, args_cons])
  refine runs_x3 v0 rfl ra (runs_x v2 rfl rd (.step (Eval.walk hk
    (xs := [(Q1, _), (Q1, _), (Q1, _)])
    (.cons (fun _ => value_bool) (.cons (fun _ => value_args_form) (.cons (fun _ => value_term) .nil))) ?_)
    (.refl value_res)))
  cases b <;> cases ys <;> simp [«evalCopy.Eval.walk.leaf», walk, takes, Form.bool, ctor, Quan.fld,
    Quan.live, bindsAt, Term.sub, Env.sub, Term.spine, Form.maybe, Form.some, args_nil, args_cons]

-- the substitution of Term.subst at depth 0 is the substitution of the environment
private theorem subk_env : Term.subk (Env.sub e) 0 t = Term.sub (Env.sub e) t := by
  rw [subk_sub]; congr

-- the leaf of the Bend walk: the term under e, applied to the rest of the spine
private theorem body_run (h : Contains B evalCopy) :
    Runs B (spine (Ref "Term.spine") [(Q1, Form.args ys),
      (Q1, spine (Ref "Term.subst") [(Q1, Form.term t), (Q2, Form.env e), (Q2, Form.nat 0)])])
      (Form.term (Term.spine (Term.sub (Env.sub e) t) ys)) := by
  have hk := h «evalCopy.Term.spine» (by simp [evalCopy])
  have v1 : Value B (App Q1 (Ref "Term.spine") (Form.args ys)) :=
    value_call (xs := [(Q1, _)]) hk (.cons (fun _ => value_args_form) .nil)
      (by rcases ys with _ | ⟨⟨q, x⟩, ys⟩ <;> simp [«evalCopy.Term.spine», walk, takes, ctor,
          Quan.fld,
        Quan.live, bindsAt, args_nil, args_cons, Form.arg])
  exact runs_x v1 rfl (subst_copy h) (runs_eq (spine_copy h) (by rw [subk_env]))

-- a pair of argument forms whose quantity runs
private theorem args_quan_run (rc : Runs B c (Form.quan q)) :
    Runs B (Tup Q1 (Lab "Con") (Tup Q1 (Tup Q1 (Lab "Arg") (Tup Q1 c (Tup Q1 (Form.term x) (Lab "()"))))
      (Tup Q1 (Form.args xs) (Lab "()")))) (Form.args ((q, x) :: xs)) :=
  runs_tup_b .lab (runs_tup_a (runs_tup_b .lab (runs_tup_a rc (.tup (fun _ => value_term) .lab)))
    (.tup (fun _ => value_args_form) .lab))

-- a pair of argument forms whose term runs
private theorem args_term_run (rc : Runs B c (Form.term x)) :
    Runs B (Tup Q1 (Lab "Con") (Tup Q1 (Tup Q1 (Lab "Arg") (Tup Q1 (Form.quan q) (Tup Q1 c (Lab "()"))))
      (Tup Q1 (Form.args xs) (Lab "()")))) (Form.args ((q, x) :: xs)) :=
  runs_tup_b .lab (runs_tup_a (runs_tup_b .lab (runs_tup_b value_quan (runs_tup_a rc .lab)))
    (.tup (fun _ => value_args_form) .lab))

-- Eval.walk on a term and an environment waits for its arguments
private theorem value_walk2 (h : Contains B evalCopy) :
    Value B (App Q2 (App Q2 (Ref "Eval.walk") (Form.term t)) (Form.env e)) := by
  have hk := h «evalCopy.Eval.walk» (by simp [evalCopy])
  refine value_call (xs := [(Q2, _), (Q2, _)]) hk
    (.cons (fun _ => value_term) (.cons (fun _ => value_env) .nil)) ?_
  cases t
  case App q f x => cases x <;> simp [«evalCopy.Eval.walk», walk, takes, ctor, Form.term, Quan.fld,
    Quan.live, bindsAt, data, data_fterm, data_fquan, data_fnat, data_fname, data_fenv, data_fnames]
  all_goals simp [«evalCopy.Eval.walk», walk, takes, ctor, Form.term, Quan.fld,
    Quan.live, bindsAt, data, data_fterm, data_fquan, data_fnat, data_fname, data_fenv, data_fnames]

-- the arguments of Eval.walk are values
private theorem values_walk : Values B [(Q2, Form.term t), (Q2, Form.env e), (Q2, Form.args xs)] :=
  .cons (fun _ => value_term) (.cons (fun _ => value_env) (.cons (fun _ => value_args_form) .nil))

-- a walk that reaches the Bend walk's last case gives the leaf, or needs more arguments
private theorem walk_leaf (h : Contains B evalCopy)
    (hw : walk B «evalCopy.Eval.walk».v [] [(Q2, Form.term t), (Q2, Form.env e), (Q2,
        Form.args xs)] =
      some (some (spine (Ref "Eval.walk.leaf") [(Q1, spine (Ref "Term.takes") [(Q1, Form.term t)]),
        (Q1, Form.args xs), (Q1, spine (Ref "Term.spine") [(Q1, Form.args xs),
          (Q1, spine (Ref "Term.subst") [(Q1, Form.term t), (Q2, Form.env e), (Q2,
              Form.nat 0)])])])))
    (ht : walk bk t e xs = if takes t then (if xs.isEmpty then some none else none)
      else some (some (Term.spine (Term.sub (Env.sub e) t) xs))) :
    Runs B (spine (Ref "Eval.walk") [(Q2, Form.term t), (Q2, Form.env e), (Q2, Form.args xs)])
      (Form.maybe (Form.maybe Form.term) (walk bk t e xs)) :=
  .step (Eval.walk (h «evalCopy.Eval.walk» (by simp [evalCopy])) values_walk hw)
    (runs_eq (leaf_run h (takes_copy h) (body_run h)) (by rw [ht]))

theorem walk_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Eval.walk") [(Q2, Form.term t), (Q2, Form.env e), (Q2, Form.args xs)])
      (Form.maybe (Form.maybe Form.term) (walk bk t e xs)) := by
  have hk := h «evalCopy.Eval.walk» (by simp [evalCopy])
  have vt : Value B (Ref "Term.takes") :=
    value_call (xs := []) (h «evalCopy.Term.takes» (by simp [evalCopy])) .nil (by simp [«evalCopy.Term.takes», walk, takes])
  induction t generalizing e xs with
  | Lam p f ih =>
    rcases xs with _ | ⟨⟨q, x⟩, xs⟩
    · exact walk_leaf h (by simp [«evalCopy.Eval.walk», walk, takes, ctor, Form.term, Form.nat,
        Quan.fld,
        Quan.live, bindsAt, data, data_fterm, data_fquan, data_fenv,
        args_nil, Term.sub, Env.sub, Term.spine]) (by simp [walk, takes])
    · refine .step (Eval.walk hk values_walk ?_)
        (runs_eq (if_run h (binds_copy (p := p) (q := q) (x := x) h) (ih (e := x :: e) (xs := xs)))
          (by simp [walk]))
      simp [«evalCopy.Eval.walk», walk, takes, ctor, Form.term, Quan.fld,
          Quan.live, bindsAt, data_fterm, data_fquan, data_fenv, data_fargs,
          args_cons, Form.arg, env_cons, Term.sub, Env.sub, Term.spine]
  | Prj hh ih =>
    rcases xs with _ | ⟨⟨q, x⟩, xs⟩
    · exact walk_leaf h (by simp [«evalCopy.Eval.walk», walk, takes, ctor, Form.term, Form.nat,
        Quan.fld,
        Quan.live, bindsAt, data, data_fterm, data_fenv,
        args_nil, Term.sub, Env.sub, Term.spine]) (by simp [walk, takes])
    cases x
    case Tup r a b =>
      refine .step (Eval.walk hk values_walk ?_)
        (runs_eq (if_run h (live_copy (q := q) h) (runs_x (value_walk2 h) rfl
          (args_quan_run (fld_copy (r := r) (q := q) h)) (ih (e := e) (xs := (Quan.fld r q,
              a) :: (q, b) :: xs))))
          (by simp [walk]))
      simp [«evalCopy.Eval.walk», walk, takes, ctor, Form.term, Quan.fld,
          Quan.live, bindsAt, data_fterm, data_fquan, data_fenv, data_fargs,
          args_cons, Form.arg, Term.sub, Env.sub, Term.spine]
    all_goals exact walk_leaf h (by simp [«evalCopy.Eval.walk», walk, takes, ctor, Form.term,
        Form.nat, Quan.fld,
        Quan.live, bindsAt, data, data_fterm, data_fquan, data_fnat, data_fname, data_fenv, data_fargs,
        data_fnames, args_cons, Form.arg, Term.sub, Env.sub, Term.spine]) (by simp [walk, takes])
  | Mat k hh m ihh ihm =>
    rcases xs with _ | ⟨⟨q, x⟩, xs⟩
    · exact walk_leaf h (by simp [«evalCopy.Eval.walk», walk, takes, ctor, Form.term, Form.nat,
        Quan.fld,
        Quan.live, bindsAt, data, data_fterm, data_fname, data_fenv,
        args_nil, Term.sub, Env.sub, Term.spine]) (by simp [walk, takes])
    cases x
    case Lab j =>
      refine .step (Eval.walk hk values_walk ?_)
        (runs_eq (if_run h (live_copy (q := q) h) (pick_run h (name_is_eq_copy (a := j) (b := k) h)
          (ihh (e := e) (xs := xs)) (ihm (e := e) (xs := (q, Lab j) :: xs))))
          (by simp [walk]))
      simp [«evalCopy.Eval.walk», walk, takes, ctor, Form.term, Quan.fld,
          Quan.live, bindsAt, data_fterm, data_fquan, data_fname, data_fenv, data_fargs,
          args_cons, Form.arg, Term.sub, Env.sub, Term.spine]
    all_goals exact walk_leaf h (by simp [«evalCopy.Eval.walk», walk, takes, ctor, Form.term,
        Form.nat, Quan.fld,
        Quan.live, bindsAt, data, data_fterm, data_fquan, data_fnat, data_fname, data_fenv, data_fargs,
        data_fnames, args_cons, Form.arg, Term.sub, Env.sub, Term.spine]) (by simp [walk, takes])
  | App q f x ihf ihx =>
    clear ihx
    cases x
    case Var v =>
      refine .step (Eval.walk hk values_walk ?_)
        (runs_eq (app_run h (runs_x vt rfl (head_copy (t := f) h) (takes_copy h))
          (runs_x (value_walk2 h) rfl (args_term_run (env_sub_copy (e := e) (i := v) h))
            (ihf (e := e) (xs := (q, Env.sub e v) :: xs)))
          (body_run (t := App q f (Var v)) (e := e) (ys := xs) h))
          (by simp [walk]))
      simp [«evalCopy.Eval.walk», walk, takes, ctor, Form.term, Form.nat, Quan.fld,
          Quan.live, bindsAt, data_fterm, data_fquan, data_fnat, data_fenv, data_fargs,
          Term.sub, Env.sub, Term.spine]
    all_goals exact walk_leaf h (by simp [«evalCopy.Eval.walk», walk, takes, ctor, Form.term,
        Form.nat, Quan.fld,
        Quan.live, bindsAt, data, data_fterm, data_fquan, data_fname, data_fenv, data_fargs,
        data_fnames, Term.sub, Env.sub, Term.spine]) (by simp [walk, takes])
  | _ => exact walk_leaf h (by simp [«evalCopy.Eval.walk», walk, takes, ctor, Form.term, Form.nat,
      Quan.fld,
        Quan.live, bindsAt, data, data_fterm, data_fquan, data_fnat, data_fname, data_fenv, data_fargs,
        data_fnames, Term.sub, Env.sub, Term.spine]) (by simp [walk, takes])

end EvalCopy
