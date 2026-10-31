import Bootstrap.Eval

-- Interp
-- ======
--
-- Walk, Value and one step of Eval (bend2/bendtt.lean) as functions,
-- each proven to give what the kernel's relation gives.

open Quan Term

def data : Term → Bool
  | Lab _ => true
  | Rfl => true
  | Tup q a b => (!q.live || data a) && data b
  | _ => false

-- Data, computed
theorem data_iff : data t = true ↔ Data t := by
  constructor
  · intro h
    induction t
    case Lab => exact .lab
    case Rfl => exact .rfl
    case Tup q a b iha ihb =>
      simp only [data, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
      exact .tup (fun l => iha (by simpa [l] using h.1)) (ihb h.2)
    all_goals simp [data] at h
  · intro h
    induction h with
    | lab => rfl
    | rfl => rfl
    | tup _ _ iha ihb =>
      simp only [data, ihb, Bool.and_true, Bool.or_eq_true, Bool.not_eq_true']
      exact (Bool.eq_false_or_eq_true _).symm.imp_right iha

def bindsAt (p q : Quan) (x : Term) : Bool :=
  p.live == q.live && (p != Q2 || data x)

-- a λ of quantity p binds x at quantity q: both live or both dead, and x is
-- Data when p is 2
theorem bindsAt_iff : bindsAt p q x = true ↔ p.live = q.live ∧ (p = Q2 → Data x) := by
  simp [bindsAt, data_iff, Decidable.imp_iff_not_or]

def walk (bk : Book) : Term → Env → List Arg → Option (Option Term)
  | Lam p f, e, (q, x) :: xs => if bindsAt p q x then walk bk f (x :: e) xs else none
  | Prj h, e, (q, Tup r a b) :: xs =>
    if q.live then walk bk h e ((Quan.fld r q, a) :: (q, b) :: xs) else none
  | Mat k h m, e, (q, Lab j) :: xs =>
    if q.live then if j = k then walk bk h e xs else walk bk m e ((q, Lab j) :: xs) else none
  | App q f (Var v), e, xs =>
    if takes (unspine f []).1 then walk bk f e ((q, Env.sub e v) :: xs)
    else some (some (spine (sub (Env.sub e) (App q f (Var v))) xs))
  | t, e, xs =>
    if takes t then if xs.isEmpty then some none else none
    else some (some (spine (sub (Env.sub e) t) xs))

-- a term that is no App on a variable is a node when it takes an argument
theorem node_of (h : ∀ q f v, t = App q f (Var v) → False) : node t = takes t := by
  cases t <;> try rfl
  case App q f x => cases x <;> first | rfl | exact (h _ _ _ rfl).elim

theorem walk_need (h : takes t = true) : walk bk t e [] = some none := by
  cases t <;> simp_all [takes, walk]

theorem walk_done (h : node t = false) :
    walk bk t e xs = some (some (spine (sub (Env.sub e) t) xs)) := by
  cases t
  case App q f x => cases x <;> simp_all [node, takes, walk]
  all_goals simp_all [node, takes, walk]

-- the walk of a case tree, computed: none when no walk exists
theorem walk_iff : walk bk t e xs = some o ↔ Walk bk t e xs o := by
  constructor
  · intro h
    fun_induction walk bk t e xs generalizing o
    case case1 hb ih => exact .lam (bindsAt_iff.1 hb).1 (bindsAt_iff.1 hb).2 (ih h)
    case case3 hq ih => exact .prj hq (ih h)
    case case5 hq ih => exact .hit hq (ih h)
    case case6 hq hjk ih => exact .miss hq hjk (ih h)
    case case8 ht ih => exact .app ht (ih h)
    case case9 ht => cases h; exact .done (by simpa [node] using ht)
    case case10 ht hx => cases h; obtain rfl := List.isEmpty_iff.1 hx; exact .need ht
    case case12 hA ht => cases h; exact .done ((node_of hA).trans (by simpa using ht))
    all_goals cases h
  · intro w
    induction w with
    | lam pq hd _ ih => simp [walk, bindsAt_iff.2 ⟨pq, hd⟩, ih]
    | prj l _ ih => simp [walk, l, ih]
    | hit l _ ih => simp [walk, l, ih]
    | miss l jk _ ih => simp [walk, l, jk, ih]
    | app hn _ ih => simp [walk, show takes _ = true from hn, ih]
    | need h => exact walk_need h
    | done h => exact walk_done h

-- the walk of a call's case tree on its arguments
def callWalk (bk : Book) (t : Term) : Option (Option Term) :=
  match unspine t [] with
  | (Ref k, xs) => (bk.get k).bind fun d => walk bk d.v [] xs
  | _ => none

theorem callWalk_spine (hk : Book.get bk k = some d) :
    callWalk bk (spine (Ref k) xs) = walk bk d.v [] xs := by
  simp [callWalk, spine_head rfl, hk]

mutual

def value (bk : Book) : Term → Bool
  | Tup q a b => (!q.live || value bk a) && value bk b
  | App q f x => args bk f && (!q.live || value bk x) && callWalk bk (App q f x) == some none
  | Ref k => callWalk bk (Ref k) == some none
  | t => t.former != 0

def args (bk : Book) : Term → Bool
  | App q f x => args bk f && (!q.live || value bk x)
  | Ref _ => true
  | _ => false

end

theorem value_args : (value bk t = true ↔ Value bk t) ∧
    (args bk t = true ↔ ∃ k xs, t = spine (Ref k) xs ∧ Values bk xs) := by
  induction t
  case Tup q a b iha ihb =>
    refine ⟨?_, nofun, fun ⟨_, _, e, _⟩ => by simpa [unspine] using spine_head e⟩
    simp only [value, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true']
    constructor
    · intro ⟨h1, h2⟩
      exact .tup (fun l => iha.1.1 (by simpa [l] using h1)) (ihb.1.1 h2)
    · intro v
      have ⟨va, vb⟩ := value_tup v
      exact ⟨(Bool.eq_false_or_eq_true _).symm.imp_right (fun l => iha.1.2 (va l)), ihb.1.2 vb⟩
  case App q f x ihf ihx =>
    have hargs : args bk (App q f x) = true ↔
        ∃ k xs, App q f x = spine (Ref k) xs ∧ Values bk xs := by
      simp only [args, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true']
      constructor
      · intro ⟨hf, hx⟩
        have ⟨k, ys, ef, vs⟩ := ihf.2.1 hf
        refine ⟨k, ys ++ [(q, x)], by rw [spine_snoc, ef], values_snoc.2 ⟨vs, fun l => ?_⟩⟩
        exact ihx.1.1 (by simpa [l] using hx)
      · intro ⟨k, xs, e, vs⟩
        rcases xs.eq_nil_or_concat with rfl | ⟨ys, ⟨q', x'⟩, rfl⟩
        · cases e
        · simp only [List.concat_eq_append, spine_snoc] at e vs
          cases e
          have ⟨vys, vx⟩ := values_snoc.1 vs
          exact ⟨ihf.2.2 ⟨k, ys, rfl, vys⟩,
            (Bool.eq_false_or_eq_true _).symm.imp_right (fun l => ihx.1.2 (vx l))⟩
    refine ⟨⟨fun h => ?_, fun v => ?_⟩, hargs⟩
    · simp only [value, Bool.and_eq_true, beq_iff_eq] at h
      have ⟨k, xs, e, vs⟩ := hargs.1 (by simp only [args, h.1.1, h.1.2, Bool.and_self])
      have hw := h.2
      rw [e] at hw ⊢
      cases hk : Book.get bk k with
      | none => simp [callWalk, spine_head rfl, hk] at hw
      | some d => exact .call hk vs (walk_iff.1 (by rwa [callWalk_spine hk] at hw))
    · have ⟨k, d, xs, e, hk, vs, w⟩ := value_inv v rfl
      have ha := hargs.2 ⟨k, xs, e, vs⟩
      simp only [args] at ha
      simp only [value, ha, Bool.true_and, beq_iff_eq, e, callWalk_spine hk, walk_iff.2 w]
  case Ref k =>
    refine ⟨?_, fun _ => ⟨k, [], rfl, .nil⟩, fun _ => rfl⟩
    simp only [value, beq_iff_eq]
    constructor
    · intro hw
      cases hk : Book.get bk k with
      | none => simp [callWalk, unspine, hk] at hw
      | some d => exact .call (xs := []) hk .nil (walk_iff.1 ((callWalk_spine (xs := []) hk).symm.trans hw))
    · intro v
      have ⟨k', d, xs, e, hk, _, w⟩ := value_inv v rfl
      have := spine_head e
      simp only [unspine, Prod.mk.injEq, Ref.injEq] at this
      obtain ⟨rfl, rfl⟩ := this
      exact (callWalk_spine (xs := []) hk).trans (walk_iff.2 w)
  all_goals
    refine ⟨⟨fun h => ?_, fun v => ?_⟩, nofun, fun ⟨_, _, e, _⟩ => ?_⟩
    · first | constructor | simp [value, former] at h
    · first | rfl | (have ⟨_, _, _, e, _⟩ := value_inv v rfl; simpa [unspine] using spine_head e)
    · simpa [unspine] using spine_head e

-- a value, computed
theorem value_iff : value bk t = true ↔ Value bk t := value_args.1

-- the live arguments of a spine on a def are values
theorem args_iff : args bk t = true ↔ ∃ k xs, t = spine (Ref k) xs ∧ Values bk xs :=
  value_args.2

-- the step of a call whose case tree takes the whole walk
def call (bk : Book) (t : Term) : Option Term :=
  if args bk t then (callWalk bk t).join else none

theorem call_sound (h : call bk t = some u) : Eval bk t u := by
  unfold call at h
  split at h
  next ha =>
    obtain ⟨k, xs, rfl, vs⟩ := args_iff.1 ha
    cases hk : Book.get bk k with
    | none => simp [callWalk, spine_head rfl, hk] at h
    | some d =>
      rw [callWalk_spine hk, Option.join_eq_some_iff] at h
      exact .call hk vs (walk_iff.1 h)
  next => cases h

theorem call_spine (hk : Book.get bk k = some d) (vs : Values bk xs)
    (w : Walk bk d.v [] xs (some u)) : call bk (spine (Ref k) xs) = some u := by
  simp [call, args_iff.2 ⟨k, xs, rfl, vs⟩, callWalk_spine hk, walk_iff.2 w]

-- the step of an App on a value, whose argument is a value if it is live
def redex (bk : Book) (q : Quan) : Term → Term → Option Term
  | Lam p f, x => if bindsAt p q x then some (inst f x) else none
  | Prj h, Tup r a b => if q.live then some (App q (App (Quan.fld r q) h a) b) else none
  | Mat k h m, Lab j => if q.live then some (if j = k then h else App q m (Lab j)) else none
  | f, x => call bk (App q f x)

theorem redex_sound (hx : q.live = true → Value bk x) (h : redex bk q f x = some u) :
    Eval bk (App q f x) u := by
  unfold redex at h
  split at h
  · split at h
    next hb => cases h; exact .beta (bindsAt_iff.1 hb).1 hx (bindsAt_iff.1 hb).2
    next => cases h
  · split at h
    next l => cases h; exact .split l (hx l)
    next => cases h
  · split at h
    next l =>
      cases h
      split
      next e => subst e; exact .hit l
      next e => exact .miss l e
    next => cases h
  · exact call_sound h

theorem redex_call (hf : f.former = 0) : redex bk q f x = call bk (App q f x) := by
  cases f <;> first | rfl | simp [former] at hf

-- the step of a term whose part p goes first when it is live: the step sp of
-- p, put back by rb; or, once p is a value, k
def part (bk : Book) (l : Bool) (p : Term) (sp : Unit → Option Term) (rb : Term → Term)
    (k : Unit → Option Term) : Option Term :=
  if !l then k ()
  else match sp () with
    | some p' => some (rb p')
    | none => if value bk p then k () else none

theorem part_some (h : part bk l p sp rb k = some u) :
    (∃ p', l = true ∧ sp () = some p' ∧ u = rb p') ∨
      ((l = true → value bk p = true) ∧ k () = some u) := by
  unfold part at h
  split at h
  next hl => exact .inr ⟨fun l' => by simp_all, h⟩
  next hl =>
    split at h
    next p' hs => cases h; exact .inl ⟨p', by simpa using hl, hs, rfl⟩
    next =>
      split at h
      next hv => exact .inr ⟨fun _ => hv, h⟩
      next => cases h

-- the meet of two quantity labels
def meet : Term → Term → Option Term
  | Lab i, Lab j => if i ∈ QS ∧ j ∈ QS then some (qmin (Lab i) (Lab j)) else none
  | _, _ => none

theorem meet_sound (h : meet a b = some u) : Eval bk (Term.Min a b) u := by
  unfold meet at h
  split at h
  · split at h
    next hij => cases h; exact .meet hij.1 hij.2
    next => cases h
  · cases h

def step (bk : Book) : Term → Option Term
  | Ann x _ => some x
  | Ref k => call bk (Ref k)
  | App q f x =>
    part bk true f (fun _ => step bk f) (App q · x) fun _ =>
      part bk q.live x (fun _ => step bk x) (App q f ·) fun _ => redex bk q f x
  | Let q v f =>
    part bk q.live v (fun _ => step bk v) (Let q · f) fun _ =>
      if q = Q2 → data v = true then some (inst f v) else none
  | Tup q a b =>
    part bk q.live a (fun _ => step bk a) (Tup q · b) fun _ => (step bk b).map (Tup q a ·)
  | Rwt e P f =>
    part bk true e (fun _ => step bk e) (Rwt · P f) fun _ => if e = Rfl then some f else none
  | Term.Min a b =>
    part bk true a (fun _ => step bk a) (Term.Min · b) fun _ =>
      part bk true b (fun _ => step bk b) (Term.Min a ·) fun _ => meet a b
  | _ => none

theorem step_sound (h : step bk t = some u) : Eval bk t u := by
  induction t generalizing u
  case Ann => simp only [step] at h; cases h; exact .ann
  case Ref => simp only [step] at h; exact call_sound h
  case App q f x ihf ihx =>
    simp only [step] at h
    rcases part_some h with ⟨f', -, hf, rfl⟩ | ⟨vf, h⟩
    · exact .app_f (ihf hf)
    · rcases part_some h with ⟨x', l, hx, rfl⟩ | ⟨vx, h⟩
      · exact .app_x (value_iff.1 (vf rfl)) l (ihx hx)
      · exact redex_sound (fun l => value_iff.1 (vx l)) h
  case Let q v f ihv _ =>
    simp only [step] at h
    rcases part_some h with ⟨v', l, hv, rfl⟩ | ⟨vv, h⟩
    · exact .lett l (ihv hv)
    · split at h
      next hd => cases h; exact .unlet (fun l => value_iff.1 (vv l)) (fun e => data_iff.1 (hd e))
      next => cases h
  case Tup q a b iha ihb =>
    simp only [step] at h
    rcases part_some h with ⟨a', l, ha, rfl⟩ | ⟨va, h⟩
    · exact .tup_a l (iha ha)
    · obtain ⟨b', hb, rfl⟩ := Option.map_eq_some_iff.1 h
      exact .tup_b (fun l => value_iff.1 (va l)) (ihb hb)
  case Rwt e P f ihe _ _ =>
    simp only [step] at h
    rcases part_some h with ⟨e', -, he, rfl⟩ | ⟨-, h⟩
    · exact .rwt (ihe he)
    · split at h
      next he => subst he; cases h; exact .cast
      next => cases h
  case Min a b iha ihb =>
    simp only [step] at h
    rcases part_some h with ⟨a', -, ha, rfl⟩ | ⟨va, h⟩
    · exact .min_a (iha ha)
    · rcases part_some h with ⟨b', -, hb, rfl⟩ | ⟨-, h⟩
      · exact .min_b (value_iff.1 (va rfl)) (ihb hb)
      · exact meet_sound h
  all_goals simp [step] at h

theorem step_value (v : Value bk t) : step bk t = none := by
  cases h : step bk t with
  | none => rfl
  | some u => exact (eval_value (step_sound h) v).elim

theorem step_app (vf : Value bk f) (hx : q.live = true → Value bk x) :
    step bk (App q f x) = redex bk q f x := by
  cases hq : q.live
  · simp [step, part, step_value vf, value_iff.2 vf, hq]
  · simp [step, part, step_value vf, value_iff.2 vf, hq, step_value (hx hq), value_iff.2 (hx hq)]

theorem step_let (hv : q.live = true → Value bk v) :
    step bk (Let q v f) = if q = Q2 → data v = true then some (inst f v) else none := by
  cases hq : q.live
  · simp [step, part, hq]
  · simp [step, part, hq, step_value (hv hq), value_iff.2 (hv hq)]

theorem step_tup (ha : q.live = true → Value bk a) :
    step bk (Tup q a b) = (step bk b).map (Tup q a ·) := by
  cases hq : q.live
  · simp [step, part, hq]
  · simp [step, part, hq, step_value (ha hq), value_iff.2 (ha hq)]

theorem call_some (hk : Book.get bk k = some d) (vs : Values bk xs)
    (w : Walk bk d.v [] xs (some u)) : ∃ u', step bk (spine (Ref k) xs) = some u' := by
  generalize hn : xs.length = n
  induction n generalizing xs u with
  | zero => obtain rfl := List.length_eq_zero_iff.1 hn; exact ⟨u, call_spine hk vs w⟩
  | succ n ih =>
    rcases xs.eq_nil_or_concat with rfl | ⟨ys, ⟨q, x⟩, rfl⟩
    · cases hn
    · simp only [List.concat_eq_append, List.length_append, List.length_singleton,
        Nat.add_right_cancel_iff] at hn vs w ⊢
      have ⟨vys, vx⟩ := values_snoc.1 vs
      rcases walk_snoc w rfl with wn | ⟨r, wr, -⟩
      · have vf : Value bk (spine (Ref k) ys) := .call hk vys wn
        have hc := call_spine hk vs w
        rw [spine_snoc] at hc ⊢
        exact ⟨u, (step_app vf vx).trans ((redex_call (spine_ft ⟨rfl, rfl⟩).1).trans hc)⟩
      · have ⟨u', hu'⟩ := ih vys wr hn
        exact ⟨App q u' x, by rw [spine_snoc]; simp [step, part, hu']⟩

theorem step_some (h : Eval bk t u) : step bk t ≠ none := by
  induction h with
  | ann => simp [step]
  | app_f _ ih => have ⟨_, hf⟩ := Option.ne_none_iff_exists'.1 ih; simp [step, part, hf]
  | app_x vf l _ ih =>
    have ⟨_, hx⟩ := Option.ne_none_iff_exists'.1 ih
    simp [step, part, step_value vf, value_iff.2 vf, l, hx]
  | beta pq hv hd => rw [step_app .lam hv]; simp [redex, bindsAt_iff.2 ⟨pq, hd⟩]
  | split l vt => rw [step_app .prj (fun _ => vt)]; simp [redex, l]
  | hit l => rw [step_app .mat (fun _ => .lab)]; simp [redex, l]
  | miss l _ => rw [step_app .mat (fun _ => .lab)]; simp [redex, l]
  | call hk vs w => have ⟨_, h⟩ := call_some hk vs w; simp [h]
  | lett l _ ih => have ⟨_, hv⟩ := Option.ne_none_iff_exists'.1 ih; simp [step, part, l, hv]
  | unlet hv hd =>
    have hd' := fun e => data_iff.2 (hd e)
    rw [step_let hv]; simpa using hd'
  | tup_a l _ ih => have ⟨_, ha⟩ := Option.ne_none_iff_exists'.1 ih; simp [step, part, l, ha]
  | tup_b hva _ ih =>
    have ⟨_, hb⟩ := Option.ne_none_iff_exists'.1 ih
    rw [step_tup hva]; simp [hb]
  | rwt _ ih => have ⟨_, he⟩ := Option.ne_none_iff_exists'.1 ih; simp [step, part, he]
  | cast => simp [step, part, value, former]
  | min_a _ ih => have ⟨_, ha⟩ := Option.ne_none_iff_exists'.1 ih; simp [step, part, ha]
  | min_b va _ ih =>
    have ⟨_, hb⟩ := Option.ne_none_iff_exists'.1 ih
    simp [step, part, step_value va, value_iff.2 va, hb]
  | meet hi hj => simp [step, part, value, former, meet, hi, hj]

-- one step of Eval, computed: no extra step and no missing step
theorem step_iff : step bk t = some u ↔ Eval bk t u :=
  ⟨step_sound, fun h =>
    have ⟨_, h'⟩ := Option.ne_none_iff_exists'.1 (step_some h)
    h'.trans (congrArg some (eval_det (step_sound h') h))⟩
