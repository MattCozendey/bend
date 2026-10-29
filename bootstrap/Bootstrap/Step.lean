import Bootstrap.Spec

-- Step
-- ====
--
-- One step of the interpreter. step bk t makes one Eval step from t, or
-- gives none when no Eval step fits. The proofs show that it agrees with
-- the kernel's Eval: each step is an Eval step, and step gives none only
-- when no Eval step exists.

open Quan Term

namespace Interp

-- Data and walks
-- ==============

-- isData t: t is plain data, as the kernel's Data says.
def isData : Term → Bool
  | Lab _ => true
  | Rfl => true
  | Tup q a b => (!q.live || isData a) && isData b
  | _ => false

theorem isData_iff : isData t = true ↔ Data t := by
  constructor
  · intro h
    induction t with
    | Lab => exact .lab
    | Rfl => exact .rfl
    | Tup q a b iha ihb =>
      simp only [isData, Bool.and_eq_true] at h
      exact .tup (fun l => iha (by simpa [l] using h.1)) (ihb h.2)
    | _ => simp [isData] at h
  · intro h
    induction h with
    | lab => rfl
    | rfl => rfl
    | tup _ _ iha ihb =>
      rename_i q _ _
      simp only [isData, Bool.and_eq_true, Bool.or_eq_true]
      exact ⟨by cases q <;> simp_all [Quan.live], ihb⟩

-- walk t e xs: the kernel's Walk as a function.
-- some o: Walk gives o. none: no Walk rule fits.
def walk : Term → Env → List Arg → Option (Option Term)
  | Lam _ _, _, [] => some none
  | Lam p f, e, (q, x) :: xs =>
    if p.live = q.live ∧ (p = Q2 → isData x = true) then walk f (x :: e) xs else none
  | Prj _, _, [] => some none
  | Prj h, e, (q, Tup r a b) :: xs =>
    if q.live then walk h e ((Quan.fld r q, a) :: (q, b) :: xs) else none
  | Prj _, _, _ :: _ => none
  | Mat .., _, [] => some none
  | Mat k h m, e, (q, Lab j) :: xs =>
    if q.live then (if j = k then walk h e xs else walk m e ((q, Lab j) :: xs)) else none
  | Mat .., _, _ :: _ => none
  | Efq, _, [] => some none
  | Efq, _, _ :: _ => none
  | App q f (Var v), e, xs =>
    if takes (unspine f []).1 then walk f e ((q, Env.sub e v) :: xs)
    else some (some (spine (sub (Env.sub e) (App q f (Var v))) xs))
  | t, e, xs => some (some (spine (sub (Env.sub e) t) xs))

-- a term that is no case tree node leaves the tree
theorem walk_done (n : node t = false) : walk t e xs = some (some (spine (sub (Env.sub e) t) xs)) := by
  cases t with
  | App q f x =>
    cases x
    case Var v => simp only [node] at n; simp [walk, n]
    all_goals simp [walk]
  | Lam | Prj | Mat | Efq => simp [node, takes] at n
  | _ => simp [walk]

theorem walk_sound : walk t e xs = some o → Walk bk t e xs o := by
  induction t generalizing e xs o with
  | Lam p f ih =>
    cases xs with
    | nil => simp [walk]; rintro rfl; exact .need rfl
    | cons a xs =>
      obtain ⟨q, x⟩ := a
      simp only [walk]; split
      · rename_i h; exact fun w => .lam h.1 (fun e => isData_iff.1 (h.2 e)) (ih w)
      · simp
  | Prj h ih =>
    cases xs with
    | nil => simp [walk]; rintro rfl; exact .need rfl
    | cons a xs =>
      obtain ⟨q, x⟩ := a
      cases x
      case Tup r a b =>
        simp only [walk]; split
        · rename_i l; exact fun w => .prj l (ih w)
        · simp
      all_goals simp [walk]
  | Mat k h m ihh ihm =>
    cases xs with
    | nil => simp [walk]; rintro rfl; exact .need rfl
    | cons a xs =>
      obtain ⟨q, x⟩ := a
      cases x
      case Lab j =>
        simp only [walk]; split
        · rename_i l; split
          · rename_i e; subst e; exact fun w => .hit l (ihh w)
          · rename_i e; exact fun w => .miss l e (ihm w)
        · simp
      all_goals simp [walk]
  | Efq =>
    cases xs with
    | nil => simp [walk]; rintro rfl; exact .need rfl
    | cons a xs => obtain ⟨q, x⟩ := a; simp [walk]
  | App q f x ihf =>
    cases x
    case Var v =>
      simp only [walk]; split
      · rename_i h; exact fun w => .app (by simpa only [node] using h) (ihf w)
      · rename_i h; simp only [Option.some.injEq]; rintro rfl
        exact .done (by simpa only [node, Bool.not_eq_true] using h)
    all_goals (rw [walk_done rfl]; simp only [Option.some.injEq]; rintro rfl; exact .done rfl)
  | _ => rw [walk_done rfl]; simp only [Option.some.injEq]; rintro rfl; exact .done rfl

theorem walk_complete (w : Walk bk t e xs o) : walk t e xs = some o := by
  induction w with
  | lam l d _ ih =>
    simp only [walk]; split
    · exact ih
    · rename_i h; exact absurd ⟨l, fun e => isData_iff.2 (d e)⟩ h
  | prj l _ ih => simp only [walk, l, ite_true]; exact ih
  | hit l _ ih => simp only [walk, l, ite_true]; exact ih
  | miss l n _ ih => simp only [walk, l, n, ite_true, ite_false]; exact ih
  | app n _ ih => simp only [node] at n; simp only [walk, n, ite_true]; exact ih
  | need t => rename_i t' _; cases t' <;> simp_all [takes, walk]
  | done n => exact walk_done n

-- Values
-- ======

-- stops bk t: t is a call, and its def's case tree needs more arguments.
def stops (bk : Book) (t : Term) : Bool :=
  match unspine t [] with
  | (Ref k, xs) =>
    match bk.get k with
    | some d =>
      match walk d.v [] xs with
      | some none => true
      | _ => false
    | none => false
  | _ => false

mutual
-- isValue bk t: t is a value, as the kernel's Value says.
def isValue (bk : Book) : Term → Bool
  | Tup q a b => (!q.live || isValue bk a) && isValue bk b
  | Ref k => stops bk (Ref k)
  | App q f x => isArgs bk f && (!q.live || isValue bk x) && stops bk (App q f x)
  | Var _ | Ann .. | Let .. | .Min .. | Rwt .. => false
  | _ => true

-- isArgs bk t: t is a spine on a Ref, and each live argument is a value.
def isArgs (bk : Book) : Term → Bool
  | Ref _ => true
  | App q f x => isArgs bk f && (!q.live || isValue bk x)
  | _ => false
end

theorem stops_iff : stops bk t = true ↔
    ∃ k d xs, unspine t [] = (Ref k, xs) ∧ bk.get k = some d ∧ Walk bk d.v [] xs none := by
  unfold stops
  constructor
  · intro h
    split at h
    · rename_i k xs e
      split at h
      · rename_i d hd
        split at h
        · rename_i hw; exact ⟨k, d, xs, e, hd, walk_sound hw⟩
        · simp at h
      · simp at h
    · simp at h
  · rintro ⟨k, d, xs, e, hd, w⟩
    simp only [e, hd, walk_complete w]

-- a term whose head is no Ref is no call
theorem no_spine (h : (unspine t []).1 ≠ Ref k) : t ≠ spine (Ref k) xs :=
  fun e => h (by rw [spine_head e])

-- a live flag, read as an implication
theorem live_or {q : Quan} {b : Bool} : (!q.live || b) = true ↔ (q.live = true → b = true) := by
  cases q.live <;> simp

theorem value_iff : (isValue bk t = true ↔ Value bk t) ∧
    (isArgs bk t = true ↔ ∃ k xs, t = spine (Ref k) xs ∧ Values bk xs) := by
  induction t with
  | Ref k =>
    refine ⟨?_, ⟨fun _ => ⟨k, [], rfl, .nil⟩, fun _ => rfl⟩⟩
    simp only [isValue, stops_iff]
    constructor
    · rintro ⟨k', d, xs, e, hd, w⟩
      simp only [unspine, Prod.mk.injEq, Term.Ref.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      exact .call (xs := []) hd .nil w
    · intro v
      obtain ⟨k', d, xs, e, hd, -, w⟩ := value_inv v rfl
      exact ⟨k', d, xs, by rw [spine_head e], hd, w⟩
  | App q f x ihf ihx =>
    have args : (isArgs bk f && (!q.live || isValue bk x)) = true ↔
        ∃ k xs, App q f x = spine (Ref k) xs ∧ Values bk xs := by
      rw [Bool.and_eq_true, live_or]
      constructor
      · rintro ⟨hf, hx⟩
        obtain ⟨k, ys, rfl, vs⟩ := ihf.2.1 hf
        exact ⟨k, ys ++ [(q, x)], spine_snoc.symm,
          values_snoc.2 ⟨vs, fun l => ihx.1.1 (hx l)⟩⟩
      · rintro ⟨k, xs, e, vs⟩
        rcases xs.eq_nil_or_concat with rfl | ⟨ys, ⟨q', x'⟩, rfl⟩
        · cases e
        · simp only [List.concat_eq_append, spine_snoc] at e vs
          cases e
          obtain ⟨vs, vx⟩ := values_snoc.1 vs
          exact ⟨ihf.2.2 ⟨k, ys, rfl, vs⟩, fun l => ihx.1.2 (vx l)⟩
    refine ⟨?_, by simpa only [isArgs] using args⟩
    simp only [isValue, Bool.and_eq_true]
    rw [← Bool.and_eq_true, args, stops_iff]
    constructor
    · rintro ⟨⟨k, xs, e, vs⟩, k', d, xs', e', hd, w⟩
      rw [spine_head e] at e'
      simp only [Prod.mk.injEq, Term.Ref.injEq] at e'
      obtain ⟨rfl, rfl⟩ := e'
      rw [e]; exact .call hd vs w
    · intro v
      obtain ⟨k, d, xs, e, hd, vs, w⟩ := value_inv v rfl
      exact ⟨⟨k, xs, e, vs⟩, k, d, xs, spine_head e, hd, w⟩
  | Tup q a b iha ihb =>
    refine ⟨?_, ⟨fun h => by simp [isArgs] at h, fun ⟨k, xs, e, _⟩ => (no_spine (by simp [unspine]) e).elim⟩⟩
    simp only [isValue, Bool.and_eq_true, live_or]
    constructor
    · rintro ⟨ha, hb⟩; exact .tup (fun l => iha.1.1 (ha l)) (ihb.1.1 hb)
    · intro v; have ⟨va, vb⟩ := value_tup v; exact ⟨fun l => iha.1.2 (va l), ihb.1.2 vb⟩
  | _ =>
    refine ⟨?_, ⟨fun h => by simp [isArgs] at h, fun ⟨k, xs, e, _⟩ => (no_spine (by simp [unspine]) e).elim⟩⟩
    first
      | exact ⟨fun _ => by constructor, fun _ => rfl⟩
      | exact ⟨fun h => by simp [isValue] at h,
          fun v => have ⟨_, _, _, e, _⟩ := value_inv v rfl; (no_spine (by simp [unspine]) e).elim⟩

theorem isValue_iff : isValue bk t = true ↔ Value bk t := value_iff.1

-- the call part of an App, read as a spine on a Ref
theorem app_args : (isArgs bk f = true ∧ (q.live = true → isValue bk x = true)) ↔
    ∃ k xs, App q f x = spine (Ref k) xs ∧ Values bk xs := by
  rw [← (value_iff (t := App q f x)).2]; simp only [isArgs, Bool.and_eq_true, live_or]

-- Step
-- ====

-- fires bk t: t is a call, and its def's case tree takes all its
-- arguments. It gives the term that the tree reaches.
def fires (bk : Book) (t : Term) : Option Term :=
  match unspine t [] with
  | (Ref k, xs) =>
    match bk.get k with
    | some d =>
      match walk d.v [] xs with
      | some (some u) => some u
      | _ => none
    | none => none
  | _ => none

-- redex bk q f x: the Eval step of f applied to x, when f is a λ or a
-- λ-match.
def redex (bk : Book) (q : Quan) (f x : Term) : Option Term :=
  match f, x with
  | Lam p b, x =>
    if p.live = q.live ∧ (q.live = true → isValue bk x = true) ∧ (p = Q2 → isData x = true)
    then some (inst b x) else none
  | Prj h, Tup r a b =>
    if q.live = true ∧ isValue bk (Tup r a b) = true
    then some (App q (App (Quan.fld r q) h a) b) else none
  | Mat k h m, Lab j =>
    if q.live = true then (if j = k then some h else some (App q m (Lab j))) else none
  | _, _ => none

-- the call step of App q f x: a call on values whose tree takes them all
def call (bk : Book) (q : Quan) (f x : Term) : Option Term :=
  if isArgs bk f = true ∧ (q.live = true → isValue bk x = true) then fires bk (App q f x) else none

-- step bk t: one Eval step from t, or none when no Eval step fits.
def step (bk : Book) : Term → Option Term
  | Ann x _ => some x
  | Ref k => fires bk (Ref k)
  | App q f x =>
    match call bk q f x with
    | some u => some u
    | none =>
      match step bk f with
      | some f' => some (App q f' x)
      | none =>
        if isValue bk f = true then
          match (if q.live = true then step bk x else none) with
          | some x' => some (App q f x')
          | none => redex bk q f x
        else none
  | Let q v f =>
    match (if q.live = true then step bk v else none) with
    | some v' => some (Let q v' f)
    | none =>
      if (q.live = true → isValue bk v = true) ∧ (q = Q2 → isData v = true)
      then some (inst f v) else none
  | Tup q a b =>
    match (if q.live = true then step bk a else none) with
    | some a' => some (Tup q a' b)
    | none =>
      if q.live = true → isValue bk a = true then (step bk b).map (Tup q a ·) else none
  | Rwt e P f =>
    match e with
    | Rfl => some f
    | _ => (step bk e).map (Rwt · P f)
  | .Min a b =>
    match step bk a with
    | some a' => some (.Min a' b)
    | none =>
      if isValue bk a = true then
        match step bk b with
        | some b' => some (.Min a b')
        | none =>
          match a, b with
          | Lab i, Lab j => if i ∈ QS ∧ j ∈ QS then some (qmin (Lab i) (Lab j)) else none
          | _, _ => none
      else none
  | _ => none

theorem fires_iff : fires bk t = some u ↔
    ∃ k d xs, unspine t [] = (Ref k, xs) ∧ bk.get k = some d ∧ Walk bk d.v [] xs (some u) := by
  unfold fires
  constructor
  · intro h
    split at h
    · rename_i k xs e
      split at h
      · rename_i d hd
        split at h
        · rename_i u' hw; cases h; exact ⟨k, d, xs, e, hd, walk_sound hw⟩
        · simp at h
      · simp at h
    · simp at h
  · rintro ⟨k, d, xs, e, hd, w⟩
    simp only [e, hd, walk_complete w]

theorem call_sound (h : call bk q f x = some u) : Eval bk (App q f x) u := by
  unfold call at h
  split at h
  · rename_i c
    obtain ⟨k, xs, e, vs⟩ := app_args.1 c
    obtain ⟨k', d, xs', e', hd, w⟩ := fires_iff.1 h
    rw [spine_head e] at e'
    simp only [Prod.mk.injEq, Term.Ref.injEq] at e'
    obtain ⟨rfl, rfl⟩ := e'
    rw [e]; exact .call hd vs w
  · simp at h

theorem redex_sound (h : redex bk q f x = some u) : Eval bk (App q f x) u := by
  unfold redex at h
  split at h
  · split at h
    · rename_i c; cases h
      exact .beta c.1 (fun l => isValue_iff.1 (c.2.1 l)) (fun e => isData_iff.1 (c.2.2 e))
    · simp at h
  · split at h
    · rename_i c; cases h; exact .split c.1 (isValue_iff.1 c.2)
    · simp at h
  · split at h
    · rename_i l; split at h
      · rename_i e; subst e; cases h; exact .hit l
      · rename_i e; cases h; exact .miss l e
    · simp at h
  · simp at h

theorem step_sound : step bk t = some u → Eval bk t u := by
  induction t generalizing u with
  | Ann x T => simp only [step, Option.some.injEq]; rintro rfl; exact .ann
  | Ref k =>
    simp only [step]; intro h
    obtain ⟨k', d, xs, e, hd, w⟩ := fires_iff.1 h
    simp only [unspine, Prod.mk.injEq, Term.Ref.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact .call (xs := []) hd .nil w
  | App q f x ihf ihx =>
    simp only [step]; intro h
    split at h
    · rename_i hc; cases h; exact call_sound hc
    · split at h
      · rename_i hf; cases h; exact .app_f (ihf hf)
      · split at h
        · rename_i vf
          split at h
          · rename_i hx; cases h
            split at hx
            · rename_i l; exact .app_x (isValue_iff.1 vf) l (ihx hx)
            · simp at hx
          · exact redex_sound h
        · simp at h
  | Let q v f ihv =>
    simp only [step]; intro h
    split at h
    · rename_i hv; cases h
      split at hv
      · rename_i l; exact .lett l (ihv hv)
      · simp at hv
    · split at h
      · rename_i c; cases h
        exact .unlet (fun l => isValue_iff.1 (c.1 l)) (fun e => isData_iff.1 (c.2 e))
      · simp at h
  | Tup q a b iha ihb =>
    simp only [step]; intro h
    split at h
    · rename_i ha; cases h
      split at ha
      · rename_i l; exact .tup_a l (iha ha)
      · simp at ha
    · split at h
      · rename_i c
        obtain ⟨b', hb, rfl⟩ := Option.map_eq_some_iff.1 h
        exact .tup_b (fun l => isValue_iff.1 (c l)) (ihb hb)
      · simp at h
  | Rwt e P f ihe =>
    simp only [step]; intro h
    split at h
    · cases h; exact .cast
    · obtain ⟨e', he, rfl⟩ := Option.map_eq_some_iff.1 h
      exact .rwt (ihe he)
  | Min a b iha ihb =>
    simp only [step]; intro h
    split at h
    · rename_i ha; cases h; exact .min_a (iha ha)
    · split at h
      · rename_i va
        split at h
        · rename_i hb; cases h; exact .min_b (isValue_iff.1 va) (ihb hb)
        · split at h
          · split at h
            · rename_i c; cases h; exact .meet c.1 c.2
            · simp at h
          · simp at h
      · simp at h
  | _ => simp [step]

-- an if whose condition holds
theorem ite_yes [Decidable c] (h : c) : (if c then a else b) = a := by simp [h]

-- when step gives none on an App, no part of it fits
theorem step_app_none (h : step bk (App q f x) = none) :
    call bk q f x = none ∧ step bk f = none ∧
    (isValue bk f = true → (q.live = true → step bk x = none) ∧ redex bk q f x = none) := by
  simp only [step] at h
  split at h
  · simp at h
  rename_i hc
  split at h
  · simp at h
  rename_i hf
  refine ⟨hc, hf, fun vf => ?_⟩
  simp only [vf, ite_true] at h
  split at h
  · simp at h
  rename_i hx
  exact ⟨fun l => by simpa [l] using hx, h⟩

theorem step_complete (h : Eval bk t u) : step bk t ≠ none := by
  induction h with
  | ann => simp [step]
  | app_f _ ih => exact fun hn => ih (step_app_none hn).2.1
  | app_x vf l _ ih => exact fun hn => ih (((step_app_none hn).2.2 (isValue_iff.2 vf)).1 l)
  | beta l vx dx =>
    intro hn
    have := ((step_app_none hn).2.2 rfl).2
    simp only [redex] at this; split at this
    · simp at this
    · rename_i c; exact c ⟨l, fun l' => isValue_iff.2 (vx l'), fun e => isData_iff.2 (dx e)⟩
  | split l vt =>
    intro hn
    have := ((step_app_none hn).2.2 rfl).2
    simp only [redex] at this; split at this
    · simp at this
    · rename_i c; exact c ⟨l, isValue_iff.2 vt⟩
  | hit l =>
    intro hn
    have := ((step_app_none hn).2.2 rfl).2
    simp [redex, l] at this
  | miss l n =>
    intro hn
    have := ((step_app_none hn).2.2 rfl).2
    simp [redex, l, n] at this
  | call hd vs w =>
    rename_i k d xs _
    rcases xs.eq_nil_or_concat with rfl | ⟨ys, ⟨q, x⟩, rfl⟩
    · simp only [spine, step]
      rw [fires_iff.2 ⟨k, d, [], rfl, hd, w⟩]; simp
    · simp only [List.concat_eq_append] at vs w ⊢
      rw [spine_snoc]
      intro hn
      have hc := (step_app_none hn).1
      unfold call at hc
      rw [ite_yes (app_args.2 ⟨k, ys ++ [(q, x)], spine_snoc.symm, vs⟩),
        fires_iff.2 ⟨k, d, ys ++ [(q, x)], spine_head spine_snoc.symm, hd, w⟩] at hc
      simp at hc
  | lett l _ ih =>
    simp only [step, l, ite_true]
    split
    · simp
    · rename_i hv; exact absurd hv ih
  | unlet vv dv =>
    simp only [step]
    split
    · simp
    · rw [ite_yes ⟨fun l => isValue_iff.2 (vv l), fun e => isData_iff.2 (dv e)⟩]; simp
  | tup_a l _ ih =>
    simp only [step, l, ite_true]
    split
    · simp
    · rename_i ha; exact absurd ha ih
  | tup_b va _ ih =>
    simp only [step]
    split
    · simp
    · rw [ite_yes (fun l => isValue_iff.2 (va l))]; simpa using ih
  | rwt he ih =>
    simp only [step]
    split
    · simp
    · simpa using ih
  | cast => simp [step]
  | min_a _ ih =>
    simp only [step]
    split
    · simp
    · rename_i ha; exact absurd ha ih
  | min_b va _ ih =>
    simp only [step]
    split
    · simp
    · rw [ite_yes (isValue_iff.2 va)]
      split
      · simp
      · rename_i hb; exact absurd hb ih
  | meet hi hj => simp [step, isValue, hi, hj]

-- One pass
-- ========
--
-- scan bk t gives step, isValue and isArgs of t from one walk of t. step
-- itself checks values again at each App, so its cost grows as the square
-- of the term. scan_eq proves scan gives exactly what step, isValue and
-- isArgs give.

-- redexWith q f x vx: redex, with vx the value check of x, made once
def redexWith (q : Quan) (f x : Term) (vx : Bool) : Option Term :=
  match f, x with
  | Lam p b, x =>
    if p.live = q.live ∧ (q.live = true → vx = true) ∧ (p = Q2 → isData x = true)
    then some (inst b x) else none
  | Prj h, Tup r a b =>
    if q.live = true ∧ vx = true then some (App q (App (Quan.fld r q) h a) b) else none
  | Mat k h m, Lab j =>
    if q.live = true then (if j = k then some h else some (App q m (Lab j))) else none
  | _, _ => none

theorem redexWith_eq : redexWith q f x (isValue bk x) = redex bk q f x := by
  cases f <;> try rfl
  all_goals cases x <;> rfl

-- scan bk t: (step bk t, isValue bk t, isArgs bk t), from one walk of t
def scan (bk : Book) : Term → Option Term × Bool × Bool
  | Ann x _ => (some x, false, false)
  | Ref k => (fires bk (Ref k), stops bk (Ref k), true)
  | App q f x =>
    let (sf, vf, af) := scan bk f
    let (sx, vx, _) := scan bk x
    let ok := af && (!q.live || vx)
    let s :=
      match (if ok = true then fires bk (App q f x) else none) with
      | some u => some u
      | none =>
        match sf with
        | some f' => some (App q f' x)
        | none =>
          if vf = true then
            match (if q.live = true then sx else none) with
            | some x' => some (App q f x')
            | none => redexWith q f x vx
          else none
    (s, ok && stops bk (App q f x), ok)
  | Let q v f =>
    let (sv, vv, _) := scan bk v
    let s :=
      match (if q.live = true then sv else none) with
      | some v' => some (Let q v' f)
      | none =>
        if (q.live = true → vv = true) ∧ (q = Q2 → isData v = true)
        then some (inst f v) else none
    (s, false, false)
  | Tup q a b =>
    let (sa, va, _) := scan bk a
    let (sb, vb, _) := scan bk b
    let s :=
      match (if q.live = true then sa else none) with
      | some a' => some (Tup q a' b)
      | none => if q.live = true → va = true then sb.map (Tup q a ·) else none
    (s, (!q.live || va) && vb, false)
  | Rwt e P f =>
    let (se, _, _) := scan bk e
    let s :=
      match e with
      | Rfl => some f
      | _ => se.map (Rwt · P f)
    (s, false, false)
  | .Min a b =>
    let (sa, va, _) := scan bk a
    let (sb, _, _) := scan bk b
    let s :=
      match sa with
      | some a' => some (.Min a' b)
      | none =>
        if va = true then
          match sb with
          | some b' => some (.Min a b')
          | none =>
            match a, b with
            | Lab i, Lab j => if i ∈ QS ∧ j ∈ QS then some (qmin (Lab i) (Lab j)) else none
            | _, _ => none
        else none
    (s, false, false)
  | Var _ => (none, false, false)
  | _ => (none, true, false)

theorem scan_eq : scan bk t = (step bk t, isValue bk t, isArgs bk t) := by
  induction t with
  | App q f x ihf ihx =>
    simp only [scan, ihf, ihx, step, call, isValue, isArgs, ← redexWith_eq]
    congr 2
    simp only [Bool.and_eq_true, live_or]
  | Let q v f ihv => simp only [scan, ihv, step, isValue, isArgs]
  | Tup q a b iha ihb => simp only [scan, iha, ihb, step, isValue, isArgs]
  | Rwt e P f ihe => simp only [scan, ihe, step, isValue, isArgs]
  | Min a b iha ihb => simp only [scan, iha, ihb, step, isValue, isArgs]
  | _ => rfl

-- next bk t: the step that run takes. It is step, from one walk.
def next (bk : Book) (t : Term) : Option Term := (scan bk t).1

theorem next_eq : next bk t = step bk t := by simp [next, scan_eq]

end Interp
