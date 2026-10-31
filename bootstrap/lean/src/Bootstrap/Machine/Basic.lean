import Bootstrap.Machine

-- Machine.Basic
-- =============
--
-- What a state of the machine knows, and the facts about its terms that the
-- proofs of its moves use.

open Quan Term

namespace Machine

-- each local known to be a value is one
def Locals.Ok (bk : Book) (l : Locals) : Prop := ∀ x ∈ l, x.2 = true → Value bk x.1

-- what a frame knows is true
def Frame.Ok (bk : Book) : Frame → Prop
  | .appArg _ _ l => Locals.Ok bk l
  | .appVal _ x k => k = true → Value bk x
  | .appFun q f => q.live = true ∧ Value bk f
  | .letIn q _ l => q.live = true ∧ Locals.Ok bk l
  | .tupB q _ l => q.live = true ∧ Locals.Ok bk l
  | .tupA q a => q.live = true → Value bk a
  | .rwt _ _ l => Locals.Ok bk l
  | .minB _ l => Locals.Ok bk l
  | .minA a => Value bk a

def Focus.Ok (bk : Book) : Focus → Prop
  | .ev _ l => Locals.Ok bk l
  | .ret v => Value bk v

-- what the state knows is true
def State.Ok (bk : Book) (s : State) : Prop := s.focus.Ok bk ∧ ∀ f ∈ s.stack, f.Ok bk

theorem plugs_append : plugs (fs ++ st) t = plugs st (plugs fs t) := by
  simp [plugs, List.foldl_append]

theorem subst_nil : subst [] = Var := by
  funext i; rfl

theorem close_eq : close t l = sub (subst l) t := by
  cases l with
  | nil => simp [close, subst_nil, sub_var]
  | cons _ _ => simp [close]

-- the local i, when l has it
theorem subst_get (h : l[i]? = some x) : subst l i = x.1 := by
  induction l generalizing i with
  | nil => simp at h
  | cons y l ih =>
    cases i with
    | zero => simp at h; subst h; rfl
    | succ i => exact ih (by simpa using h)

theorem localAt_eq : (localAt l v).1 = subst l v := by
  induction l generalizing v with
  | nil => rfl
  | cons y l ih =>
    cases v with
    | zero => rfl
    | succ v =>
      have := @ih v
      simp only [localAt, subst, List.map_cons, Env.sub, List.getElem?_cons_succ,
        List.length_cons] at this ⊢
      rw [← this, Nat.add_sub_add_right]

theorem localAt_ok (hl : Locals.Ok bk l) (h : (localAt l v).2 = true) : Value bk (localAt l v).1 :=
  by
  unfold localAt at h ⊢
  cases e : l[v]? with
  | none => simp [e] at h
  | some x =>
    simp only [e, Option.getD_some] at h ⊢
    exact hl x (List.mem_of_getElem? e) h

-- a λ's body, under its argument
theorem close_one : close t [(x, k)] = inst t x := by
  simp only [close, List.isEmpty_cons, inst, Bool.false_eq_true, ite_false]
  congr 1; funext i; cases i <;> rfl

-- a let's body, under its value and l
theorem close_cons : close f ((v, k) :: l) = inst (sub (Subst.up (subst l)) f) v := by
  simp only [close, List.isEmpty_cons, inst, sub_sub, Bool.false_eq_true, ite_false]
  congr 1; funext i
  cases i with
  | zero => rfl
  | succ i => simp [Subst.up, sub_ren]; exact (sub_var _).symm

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
    case appFun => exact .app_x hf.2 hf.1 h
    case letIn => exact .lett hf.1 h
    case tupB => exact .tup_a hf.1 h
    case tupA => exact .tup_b hf h
    case rwt => exact .rwt h
    case minB => exact .min_a h
    case minA => exact .min_b hf h

-- the frames of a spine's arguments
theorem plugs_argFrames : plugs (argFrames ys) t = spine t (ys.map fun (q, y, _) => (q, y)) := by
  induction ys generalizing t with
  | nil => rfl
  | cons y ys ih =>
    obtain ⟨q, x, k⟩ := y
    exact ih

end Machine
