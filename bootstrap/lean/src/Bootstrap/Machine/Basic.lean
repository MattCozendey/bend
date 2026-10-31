import Bootstrap.Machine

-- Machine.Basic
-- =============
--
-- What a state of the machine knows, and the facts about its terms that the
-- proofs of its moves use.

open Quan Term

namespace Machine

-- each local known to be a value is one, and its own locals know the same
def Locals.Ok (bk : Book) : Locals → Prop
  | .nil => True
  | .cons t l k rest => (k = true → Value bk (close t l)) ∧ l.Ok bk ∧ rest.Ok bk

-- an argument of a walk, put together
def argOf : MArg → Arg
  | (q, x, l, _) => (q, close x l)

-- an argument put together, by its parts
theorem argOf_eq : argOf a = (a.1, close a.2.1 a.2.2.1) := rfl

-- the locals of an argument know what is true, and it is a value when its flag
-- says so
def argOk (bk : Book) (a : MArg) : Prop :=
  a.2.2.1.Ok bk ∧ (a.2.2.2 = true → Value bk (close a.2.1 a.2.2.1))

-- what a frame knows is true
def Frame.Ok (bk : Book) : Frame → Prop
  | .appArg _ _ l => l.Ok bk
  | .appVal _ x l k => (k = true → Value bk (close x l)) ∧ l.Ok bk
  | .appFun q f l => q.live = true ∧ Value bk (close f l) ∧ l.Ok bk
  | .letIn q _ l => q.live = true ∧ l.Ok bk
  | .tupB q _ l => q.live = true ∧ l.Ok bk
  | .tupA q a l => (q.live = true → Value bk (close a l)) ∧ l.Ok bk
  | .rwt _ _ l => l.Ok bk
  | .minB _ l => l.Ok bk
  | .minA a => Value bk a

def Focus.Ok (bk : Book) : Focus → Prop
  | .ev _ l => l.Ok bk
  | .ret v l => Value bk (close v l) ∧ l.Ok bk

-- what the state knows is true
def State.Ok (bk : Book) (s : State) : Prop := s.focus.Ok bk ∧ ∀ f ∈ s.stack, f.Ok bk

theorem plugs_append : plugs (fs ++ st) t = plugs st (plugs fs t) := by
  simp [plugs, List.foldl_append]

-- the terms of locals, each under its own locals
theorem terms_cons : (Locals.cons t l k r).terms = close t l :: r.terms := by
  cases l <;> rfl

-- the term of each variable under locals
theorem subst_nil : subst .nil = Var := by
  funext i; rfl

theorem subst_zero : subst (.cons t l k r) 0 = close t l := by
  simp only [subst, terms_cons, Env.sub]

theorem subst_succ : subst (.cons t l k r) (i + 1) = subst r i := by
  simp only [subst, terms_cons, Env.sub]

-- a term under its locals, by its head
theorem close_nil : close t .nil = t := rfl

theorem close_eq : close t l = sub (subst l) t := by
  cases l with
  | nil => rw [subst_nil, sub_var]; rfl
  | cons => rfl

theorem close_var : close (Var i) l = subst l i := by
  rw [close_eq]; rfl

theorem close_lab : close (Lab i) l = Lab i := by
  simp only [close_eq, sub]

theorem close_rfl : close Rfl l = Rfl := by
  simp only [close_eq, sub]

theorem close_ref : close (Ref k) l = Ref k := by
  simp only [close_eq, sub]

theorem close_lam : close (Lam p b) l = Lam p (sub (Subst.up (subst l)) b) := by
  simp only [close_eq, sub]

theorem close_prj : close (Prj h) l = Prj (close h l) := by
  simp only [close_eq, sub]

theorem close_mat : close (Mat j h m) l = Mat j (close h l) (close m l) := by
  simp only [close_eq, sub]

theorem close_app : close (App q f x) l = App q (close f l) (close x l) := by
  simp only [close_eq, sub]

theorem close_tup : close (Tup q a b) l = Tup q (close a l) (close b l) := by
  simp only [close_eq, sub]

-- no locals change a term with no variable
theorem noVars_sub (h : noVars t = true) : sub σ t = t := by
  induction t generalizing σ <;> simp_all [noVars, sub]

theorem noVars_close (h : noVars t = true) : close t l = t := by
  rw [close_eq, noVars_sub h]

-- the local i, when l has it
theorem get?_close (h : l.get? i = some (x, xl, k)) : subst l i = close x xl := by
  induction l generalizing i with
  | nil => cases h
  | cons t l' k' r _ ih =>
    cases i with
    | zero =>
      simp only [Locals.get?, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact subst_zero
    | succ i => rw [subst_succ]; exact ih h

-- the local i knows what is true
theorem get?_ok {l : Locals} (hl : l.Ok bk) (h : l.get? i = some (x, xl, k)) :
    (k = true → Value bk (close x xl)) ∧ xl.Ok bk := by
  induction l generalizing i with
  | nil => cases h
  | cons t l' k' r _ ih =>
    cases i with
    | zero =>
      simp only [Locals.get?, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨hl.1, hl.2.1⟩
    | succ i => exact ih hl.2.2 h

-- the local v, or the variable beyond l
theorem localAt_eq : close (localAt l v).1 (localAt l v).2.1 = subst l v := by
  induction l generalizing v with
  | nil => rfl
  | cons t l k r _ ih =>
    cases v with
    | zero => exact subst_zero.symm
    | succ v => rw [subst_succ]; exact ih

-- the local v knows what is true
theorem localAt_ok (hl : l.Ok bk) : argOk bk (q, localAt l v) := by
  induction l generalizing v with
  | nil => exact ⟨trivial, nofun⟩
  | cons t l k r _ ih =>
    cases v with
    | zero => exact ⟨hl.2.1, hl.1⟩
    | succ v => exact ih hl.2.2

-- a let's body, under its value and l
theorem close_cons : close f (.cons v vl k l) = inst (sub (Subst.up (subst l)) f) (close v vl) := by
  show sub (subst _) f = _
  simp only [inst, sub_sub]
  congr 1; funext i
  cases i with
  | zero => exact subst_zero
  | succ i =>
    rw [subst_succ]
    simp only [Function.comp, Subst.up, sub_ren]
    exact (sub_var _).symm

-- a call that waits for one more argument, under that argument and l
theorem close_shift :
    close (App q (ren Nat.succ f) (Var 0)) (.cons x xl k fl) = App q (close f fl) (close x xl) := by
  rw [close_app, close_var, subst_zero, close_eq, close_eq (l := fl), sub_ren]
  congr 2; funext i; exact subst_succ

-- resolve keeps the term
theorem resolve_close : close (resolve t l).1 (resolve t l).2 = close t l := by
  fun_induction resolve t l
  case case1 ih => rw [ih, close_var, subst_zero]
  case case2 ih => rw [ih, close_var, close_var, subst_succ]
  case case3 => rfl

-- resolve gives locals that know what is true
theorem resolve_ok (hl : l.Ok bk) : (resolve t l).2.Ok bk := by
  fun_induction resolve t l
  case case1 ih => exact ih hl.2.1
  case case2 ih => exact ih hl.2.2
  case case3 => exact hl

theorem resolve_ok' (hl : l.Ok bk) (h : resolve t l = (u, ul)) : ul.Ok bk := by
  have := resolve_ok (t := t) hl; rwa [h] at this

-- a variable that resolve gives is beyond its locals
theorem resolve_var (h : resolve t l = (Var i, ul)) : ul = .nil := by
  fun_induction resolve t l
  case case1 ih => exact ih h
  case case2 ih => exact ih h
  case case3 t l h1 h2 =>
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    cases l with
    | nil => rfl
    | cons =>
      cases i with
      | zero => exact (h1 _ _ _ _ rfl rfl).elim
      | succ i => exact (h2 _ _ _ _ _ rfl rfl).elim

-- the term, from what resolve gives
theorem resolve_eq (h : resolve t l = (u, ul)) : close t l = close u ul := by
  rw [← resolve_close, h]

-- dataAt is data of the term
theorem dataAt_eq : dataAt t l = data (close t l) := by
  fun_induction dataAt t l
  case case1 => simp only [close_eq, sub, data]
  case case2 => simp only [close_eq, sub, data]
  case case3 iha ihb => rw [iha, ihb, close_tup]; rfl
  case case4 ih => rw [ih, close_var, subst_zero]
  case case5 ih => rw [ih, close_var, close_var, subst_succ]
  case case6 t l h1 h2 h3 h4 h5 =>
    cases t
    case Var i =>
      cases l with
      | nil => rfl
      | cons =>
        cases i with
        | zero => exact (h4 _ _ _ _ rfl rfl).elim
        | succ i => exact (h5 _ _ _ _ _ rfl rfl).elim
    all_goals simp_all [close_eq, sub, data]

-- bindsAtL is bindsAt of the term
theorem bindsAtL_eq : bindsAtL p q x l = bindsAt p q (close x l) := by
  simp only [bindsAtL, bindsAt, dataAt_eq]

-- the term an unspine took apart
theorem spine_unspine (h : unspine t ys = (u, zs)) : spine t ys = spine u zs := by
  induction t generalizing ys with
  | App q f x ihf _ => exact ihf h
  | _ => simp only [unspine, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl

-- unspineL unspines the term under its locals
theorem unspineL_unspine : unspine (close t l) (xs.map argOf) =
    unspine (close (unspineL t l xs).1 (unspineL t l xs).2.1) ((unspineL t l xs).2.2.map argOf) := by
  fun_induction unspineL t l xs
  case case1 ih => rw [← ih, close_app]; rfl
  case case2 ih => rw [← ih, close_var, subst_zero]
  case case3 ih => rw [← ih, close_var, close_var, subst_succ]
  case case4 => rfl

-- the arguments of unspineL have locals that know what is true, and their
-- flags say whether they are live
theorem unspineL_ok (hl : l.Ok bk) (hx : ∀ a ∈ xs, a.2.2.1.Ok bk ∧ a.2.2.2 = a.1.live) :
    ∀ a ∈ (unspineL t l xs).2.2, a.2.2.1.Ok bk ∧ a.2.2.2 = a.1.live := by
  fun_induction unspineL t l xs
  case case1 ih =>
    refine ih hl fun a m => ?_
    rcases List.mem_cons.1 m with rfl | m
    · exact ⟨hl, rfl⟩
    · exact hx a m
  case case2 ih => exact ih hl.2.1 hx
  case case3 ih => exact ih hl.2.2 hx
  case case4 => exact hx

-- the live arguments of values are values
theorem values_mem (vs : Values bk xs) (m : (q, x) ∈ xs) (l : q.live = true) : Value bk x := by
  induction xs with
  | nil => cases m
  | cons y ys ih =>
    cases vs with
    | cons hx vs =>
      rcases List.mem_cons.1 m with e | m
      · cases e; exact hx l
      · exact ih vs m

-- a step in the hole is a step of the whole term
theorem Eval.plugs (hs : ∀ f ∈ st, f.Ok bk) (h : Eval bk t u) : Eval bk (plugs st t) (plugs st u) :=
  by
  induction st generalizing t u with
  | nil => exact h
  | cons f st ih =>
    have hf := hs f (by simp)
    apply ih (fun g hg => hs g (by simp [hg]))
    cases f <;> simp only [Frame.Ok] at hf <;> simp only [Frame.plug]
    case appArg => exact .app_f h
    case appVal => exact .app_f h
    case appFun => exact .app_x hf.2.1 hf.1 h
    case letIn => exact .lett hf.1 h
    case tupB => exact .tup_a hf.1 h
    case tupA => exact .tup_b hf.1 h
    case rwt => exact .rwt h
    case minB => exact .min_a h
    case minA => exact .min_b hf h

-- the frames of a spine's arguments
theorem plugs_argFrames : plugs (argFrames ys) t = spine t (ys.map argOf) := by
  induction ys generalizing t with
  | nil => rfl
  | cons y ys ih =>
    obtain ⟨q, x, l, k⟩ := y
    exact ih

end Machine
