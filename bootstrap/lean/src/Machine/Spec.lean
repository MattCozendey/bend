import Machine.Impl

-- Machine.Spec
-- ============
--
-- The proof that the machine runs Eval. Each step is StepSound
-- (step_sound). So a run makes only Eval steps (run_sound), and where Eval
-- ends, the machine stops (run_ends).

open Quan Term Contract

namespace Interp.Machine

-- Readback
-- ========

theorem rbs_get (h : e[i]? = some v) : Env.sub (Val.rbs e) i = v.rb := by
  induction e generalizing i with
  | nil => simp at h
  | cons w e ih =>
    cases i with
    | zero => simp at h; subst h; rfl
    | succ i => simp only [List.getElem?_cons_succ] at h; exact ih h

theorem rbArgs_append : ∀ (xs ys : List (Quan × Val)),
    Val.rbArgs (xs ++ ys) = Val.rbArgs xs ++ Val.rbArgs ys
  | [], _ => rfl
  | (q, v) :: xs, ys => by simp [Val.rbArgs, rbArgs_append xs ys]

theorem rb_nil (t : Term) : sub (Env.sub (Val.rbs [])) t = t := by
  simp only [Val.rbs, env_nil, sub_var]

theorem Val.isData_sound : ∀ {v : Val}, Val.isData v = true → Data v.rb
  | .lab _, _ => .lab
  | .rfl, _ => .rfl
  | .tup q a b, h => by
    simp only [Val.isData, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
    exact .tup (fun l => Val.isData_sound (by cases h.1 <;> simp_all)) (Val.isData_sound h.2)
  | .clo .., h | .dead .., h | .call .., h => by simp [Val.isData] at h

theorem plug_appVs : ∀ (rest : List (Quan × Val)) (fs : List Frame) (t : Term),
    plug (rest.map (fun (q, a) => .appV q a) ++ fs) t = plug fs (spine t (Val.rbArgs rest))
  | [], _, _ => rfl
  | (q, a) :: rest, fs, t => plug_appVs rest fs (App q t a.rb)

-- Invariants
-- ==========

mutual
-- Good bk v: outside dead terms, each closure and call in v reads back to a
-- value, and no live field or live argument is a dead term
def Good (bk : Book) : Val → Prop
  | .clo t e => Goods bk e ∧ Value bk (Val.rb (.clo t e))
  | .dead _ _ => True
  | .lab _ => True
  | .rfl => True
  | .tup q a b => Good bk a ∧ (q.live → a.live) ∧ Good bk b ∧ b.live
  | .call k xs => GoodArgs bk xs ∧ Value bk (Val.rb (.call k xs))

def Goods (bk : Book) : List Val → Prop
  | [] => True
  | v :: vs => Good bk v ∧ Goods bk vs

def GoodArgs (bk : Book) : List (Quan × Val) → Prop
  | [] => True
  | (q, v) :: xs => Good bk v ∧ (q.live → v.live) ∧ GoodArgs bk xs
end

theorem good_value : ∀ {v : Val}, Good bk v → v.live → Value bk v.rb
  | .clo .., g, _ => g.2
  | .dead .., _, h => by simp [Val.live] at h
  | .lab _, _, _ => .lab
  | .rfl, _, _ => .rfl
  | .tup .., ⟨ga, la, gb, lb⟩, _ => .tup (fun l => good_value ga (la l)) (good_value gb lb)
  | .call .., g, _ => g.2

theorem goods_get : ∀ {e : List Val} {i : Nat}, Goods bk e → e[i]? = some v → Good bk v
  | [], _, _, h => by simp at h
  | w :: e, 0, g, h => by simp at h; subst h; exact g.1
  | w :: e, i + 1, g, h => by simp only [List.getElem?_cons_succ] at h; exact goods_get g.2 h

theorem goodArgs_append : ∀ (xs ys : List (Quan × Val)),
    GoodArgs bk xs → GoodArgs bk ys → GoodArgs bk (xs ++ ys)
  | [], _, _, g => g
  | (_, _) :: xs, ys, ⟨g1, g2, g3⟩, g => ⟨g1, g2, goodArgs_append xs ys g3 g⟩

theorem goodArgs_values : ∀ {xs : List (Quan × Val)}, GoodArgs bk xs → Values bk (Val.rbArgs xs)
  | [], _ => .nil
  | (_, _) :: _, ⟨g1, g2, g3⟩ => .cons (fun l => good_value g1 (g2 l)) (goodArgs_values g3)

theorem ofData_sound (h : ofData t = some v) : v.rb = t ∧ Good bk v ∧ v.live := by
  induction t generalizing v with
  | Lab => cases h; exact ⟨rfl, trivial, rfl⟩
  | Rfl => cases h; exact ⟨rfl, trivial, rfl⟩
  | Tup q a b iha ihb =>
    simp only [ofData] at h
    split at h
    · rename_i a' b' ha hb
      cases h
      have ⟨rb, gb, lb⟩ := ihb hb
      split at ha
      · have ⟨ra, ga, la⟩ := iha ha
        exact ⟨by simp [Val.rb, ra, rb], ⟨ga, fun _ => la, gb, lb⟩, rfl⟩
      · rename_i l
        cases ha
        exact ⟨by simp [Val.rb, rb_nil, rb], ⟨trivial, fun l' => absurd l' l, gb, lb⟩, rfl⟩
    · simp at h
  | _ => simp [ofData] at h

def GoodFrame (bk : Book) : Frame → Prop
  | .appF _ _ e => Goods bk e
  | .appX q f => q.live ∧ Good bk f ∧ f.live
  | .appV q a => Good bk a ∧ (q.live → a.live)
  | .letV q _ e => q.live ∧ Goods bk e
  | .tupA q _ e => q.live ∧ Goods bk e
  | .tupB q a => Good bk a ∧ (q.live → a.live)
  | .rwt _ _ e => Goods bk e
  | .minA _ e => Goods bk e
  | .minB a => Good bk a ∧ a.live

def GoodFrames (bk : Book) : List Frame → Prop
  | [] => True
  | f :: fs => GoodFrame bk f ∧ GoodFrames bk fs

-- Inv bk s: the invariant of each state that the machine reaches
def Inv (bk : Book) : St → Prop
  | .eval _ e fs => Goods bk e ∧ GoodFrames bk fs
  | .ret v fs => Good bk v ∧ v.live ∧ GoodFrames bk fs

-- Contexts
-- ========

-- an Eval step inside good frames is an Eval step of the whole term
theorem eval_plug : ∀ {fs : List Frame} {t t' : Term}, GoodFrames bk fs → Eval bk t t' →
    Eval bk (plug fs t) (plug fs t')
  | [], _, _, _, h => h
  | f :: fs, t, t', ⟨gf, gs⟩, h => by
    cases f with
    | appF => exact eval_plug (fs := fs) gs (.app_f h)
    | appX q f => exact eval_plug (fs := fs) gs (.app_x (good_value gf.2.1 gf.2.2) gf.1 h)
    | appV => exact eval_plug (fs := fs) gs (.app_f h)
    | letV q => exact eval_plug (fs := fs) gs (.lett gf.1 h)
    | tupA q => exact eval_plug (fs := fs) gs (.tup_a gf.1 h)
    | tupB q a => exact eval_plug (fs := fs) gs (.tup_b (fun l => good_value gf.1 (gf.2 l)) h)
    | rwt => exact eval_plug (fs := fs) gs (.rwt h)
    | minA => exact eval_plug (fs := fs) gs (.min_a h)
    | minB a => exact eval_plug (fs := fs) gs (.min_b (good_value gf.1 gf.2) h)

theorem plus_plug (g : GoodFrames bk fs) : Plus bk t t' → Plus bk (plug fs t) (plug fs t') :=
  plus_map (plug fs) (eval_plug g)

theorem one_plug (g : GoodFrames bk fs) (h : Eval bk t t') : Plus bk (plug fs t) (plug fs t') :=
  plus_plug g ⟨_, h, .refl⟩

-- Walks
-- =====

-- leafT o: the inner result o of walk, as Interp.walk gives it
def leafT : Option (Term × List Val × List (Quan × Val)) → Option Term
  | none => none
  | some (t, e, rest) => some (spine (sub (Env.sub (Val.rbs e)) t) (Val.rbArgs rest))

-- GoodLeaf bk o: the environment and the arguments of the leaf o are good
def GoodLeaf (bk : Book) : Option (Term × List Val × List (Quan × Val)) → Prop
  | none => True
  | some (_, e, rest) => Goods bk e ∧ GoodArgs bk rest

theorem fld_live : (Quan.fld r q).live = true → r.live = true := by
  cases r <;> cases q <;> simp [Quan.fld, Quan.live]

theorem walk_sound (ge : Goods bk e) (gx : GoodArgs bk xs) : walk t e xs = some o →
    Interp.walk t (Val.rbs e) (Val.rbArgs xs) = some (leafT o) ∧ GoodLeaf bk o := by
  induction t generalizing e xs o with
  | Lam p f ih =>
    cases xs with
    | nil => simp [walk]; rintro rfl; exact ⟨rfl, trivial⟩
    | cons a xs =>
      obtain ⟨q, x⟩ := a
      simp only [walk, Interp.walk, Val.rbArgs]; split
      · rename_i c
        have c' : p.live = q.live ∧ (p = Q2 → isData x.rb = true) :=
          ⟨c.1, fun e => isData_iff.2 (Val.isData_sound (c.2 e))⟩
        rw [ite_eq_left c']; exact ih ⟨gx.1, ge⟩ gx.2.2
      · simp
  | Prj h ih =>
    cases xs with
    | nil => simp [walk]; rintro rfl; exact ⟨rfl, trivial⟩
    | cons a xs =>
      obtain ⟨q, x⟩ := a
      cases x
      case tup r a b =>
        simp only [walk, Interp.walk, Val.rbArgs, Val.rb]; split
        · obtain ⟨⟨ga, la, gb, lb⟩, _, gxs⟩ := gx
          exact ih ge ⟨ga, fun l => la (fld_live l), gb, fun _ => lb, gxs⟩
        · simp
      all_goals simp [walk]
  | Mat k h m ihh ihm =>
    cases xs with
    | nil => simp [walk]; rintro rfl; exact ⟨rfl, trivial⟩
    | cons a xs =>
      obtain ⟨q, x⟩ := a
      cases x
      case lab j =>
        simp only [walk, Interp.walk, Val.rbArgs, Val.rb]; split
        · split
          · exact ihh ge gx.2.2
          · exact ihm ge ⟨trivial, fun _ => rfl, gx.2.2⟩
        · simp
      all_goals simp [walk]
  | Efq =>
    cases xs with
    | nil => simp [walk]; rintro rfl; exact ⟨rfl, trivial⟩
    | cons a xs => obtain ⟨q, x⟩ := a; simp [walk]
  | App q f x ihf =>
    cases x
    case Var v =>
      simp only [walk, Interp.walk]; split
      · split
        · rename_i x' hx
          split
          · rename_i lx; rw [rbs_get hx]; exact ihf ge ⟨goods_get ge hx, lx, gx⟩
          · simp
        · simp
      · simp only [Option.some.injEq]; rintro rfl; exact ⟨rfl, ge, gx⟩
    all_goals (simp only [walk, Interp.walk, Option.some.injEq]; rintro rfl; exact ⟨rfl, ge, gx⟩)
  | _ => simp only [walk, Interp.walk, Option.some.injEq]; rintro rfl; exact ⟨rfl, ge, gx⟩

theorem goodFrames_appVs : ∀ {rest : List (Quan × Val)}, GoodArgs bk rest → GoodFrames bk fs →
    GoodFrames bk (rest.map (fun (q, a) => .appV q a) ++ fs)
  | [], _, g => g
  | (_, _) :: _, ⟨g1, g2, g3⟩, g => ⟨⟨g1, g2⟩, goodFrames_appVs g3 g⟩

-- Measure
-- =======

-- pend f: a bound on the bookkeeping steps that the frame f still needs. A
-- bookkeeping step keeps the decoded term.
noncomputable def pend : Frame → Nat
  | .appF _ x _ => 3 * sizeOf x + 2
  | .appX .. => 1
  | .appV .. => 1
  | .letV .. => 0
  | .tupA _ b _ => 3 * sizeOf b + 2
  | .tupB .. => 1
  | .rwt .. => 0
  | .minA b _ => 3 * sizeOf b + 2
  | .minB _ => 1

-- μ s: a bound on the bookkeeping steps from s before the next Eval step.
-- Each term node needs at most 3.
noncomputable def μ : St → Nat
  | .eval t _ fs => 3 * sizeOf t + (fs.map pend).sum
  | .ret _ fs => (fs.map pend).sum

-- Calls
-- =====

-- PlugSound bk fs t s': as StepSound, from the term plug fs t. When s' stands
-- for that same term, its μ is only the part for fs.
def PlugSound (bk : Book) (fs : List Frame) (t : Term) (s' : St) : Prop :=
  Inv bk s' ∧ ((decode s' = plug fs t ∧ μ s' = (fs.map pend).sum) ∨ Plus bk (plug fs t) (decode s'))

theorem tryCall_sound (hj : Jump.Sound bk jump) (gx : GoodArgs bk xs)
    (gs : GoodFrames bk fs) (h : tryCall bk jump k xs fs = some s') :
    PlugSound bk fs (spine (Ref k) (Val.rbArgs xs)) s' := by
  unfold tryCall at h
  split at h
  · rename_i u hu
    split at hu
    · obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.1 h
      have ⟨r, g, l⟩ := ofData_sound (bk := bk) hv
      refine ⟨⟨g, l, gs⟩, .inr ?_⟩
      simp only [decode, r]
      exact plus_plug gs (hj _ _ hu)
    · simp at hu
  · split at h
    · rename_i d hd
      split at h
      · rename_i hw
        cases h
        have w := Interp.walk_sound (bk := bk) (walk_sound (show Goods bk [] from trivial) gx hw).1
        exact ⟨⟨⟨gx, .call hd (goodArgs_values gx) w⟩, rfl, gs⟩, .inl ⟨rfl, rfl⟩⟩
      · rename_i t e rest hw
        cases h
        obtain ⟨w, ge, gr⟩ := walk_sound (show Goods bk [] from trivial) gx hw
        refine ⟨⟨ge, goodFrames_appVs gr gs⟩, .inr ?_⟩
        simp only [decode, plug_appVs]
        exact one_plug gs (.call hd (goodArgs_values gx) (Interp.walk_sound w))
      · simp at h
    · simp at h

-- Apply
-- =====

theorem apply_sound (hj : Jump.Sound bk jump) (gf : Good bk f)
    (gx : Good bk x) (lx : q.live → x.live) (gs : GoodFrames bk fs)
    (h : apply bk jump f q x fs = some s') : PlugSound bk fs (App q f.rb x.rb) s' := by
  unfold apply at h
  split at h
  · rename_i p b e
    split at h
    · rename_i c
      cases h
      refine ⟨⟨⟨gx, gf.1⟩, gs⟩, .inr ?_⟩
      simp only [decode, Val.rbs, env_inst, Val.rb, Term.sub]
      exact one_plug gs
        (.beta c.1 (fun l => good_value gx (lx l)) (fun e => Val.isData_sound (c.2 e)))
    · simp at h
  · rename_i hh e r a b
    split at h
    · rename_i l
      cases h
      have vx := good_value gx rfl
      obtain ⟨ga, la, gb, lb⟩ := gx
      refine ⟨⟨gf.1, ⟨⟨ga, fun l' => la (fld_live l')⟩,
        ⟨gb, fun _ => lb⟩, gs⟩⟩, .inr ?_⟩
      simp only [decode, plug, Val.rb, Term.sub]
      exact one_plug gs (.split l vx)
    · simp at h
  · rename_i k hh m e j
    split at h
    · rename_i l
      split at h
      · rename_i hjk
        cases h; subst hjk
        refine ⟨⟨gf.1, gs⟩, .inr ?_⟩
        simp only [decode, Val.rb, Term.sub]
        exact one_plug gs (.hit l)
      · rename_i hjk
        cases h
        refine ⟨⟨gf.1, ⟨⟨trivial, fun _ => rfl⟩, gs⟩⟩, .inr ?_⟩
        simp only [decode, plug, Val.rb, Term.sub]
        exact one_plug gs (.miss l hjk)
    · simp at h
  · rename_i k xs
    have gx' : GoodArgs bk (xs ++ [(q, x)]) := goodArgs_append xs _ gf.1 ⟨gx, lx, trivial⟩
    have e : spine (Ref k) (Val.rbArgs (xs ++ [(q, x)])) = App q (Val.rb (.call k xs)) x.rb := by
      simp [rbArgs_append, Val.rbArgs, spine_snoc, Val.rb]
    rw [← e]
    exact tryCall_sound hj gx' gs h
  · simp at h

-- Steps
-- =====

-- StepSound bk s s': the invariant holds at s', and s' stands for the term
-- of s with a smaller μ, or for a term one or more Eval steps after it
def StepSound (bk : Book) (s s' : St) : Prop :=
  Inv bk s' ∧ ((decode s' = decode s ∧ μ s' < μ s) ∨ Plus bk (decode s) (decode s'))

theorem PlugSound.stepSound (r : PlugSound bk fs t s') (d : decode s = plug fs t)
    (m : (fs.map pend).sum < μ s) : StepSound bk s s' := by
  obtain ⟨I, r⟩ := r
  refine ⟨I, ?_⟩
  rcases r with ⟨d', m'⟩ | p
  · exact .inl ⟨d'.trans d.symm, m' ▸ m⟩
  · exact .inr (d ▸ p)

theorem eval_sound (hj : Jump.Sound bk jump) (ge : Goods bk e)
    (gs : GoodFrames bk fs) (h : step bk jump (.eval t e fs) = some s') :
    StepSound bk (.eval t e fs) s' := by
  cases t with
  | Var i =>
    simp only [step, stepEval] at h
    split at h
    · simp at h
    · rename_i v hd hv
      cases h
      have lv : v.live = true := by cases v <;> simp_all [Val.live]
      refine ⟨⟨goods_get ge hv, lv, gs⟩, .inl ⟨?_, ?_⟩⟩
      · simp [decode, Term.sub, rbs_get hv]
      · simp [μ] <;> omega
    · simp at h
  | Ref k =>
    simp only [step, stepEval] at h
    exact (tryCall_sound hj (xs := []) trivial gs h).stepSound
      (by simp [decode, Term.sub, Val.rbArgs, spine]) (by simp [μ] <;> omega)
  | Ann x T =>
    simp only [step, stepEval, Option.some.injEq] at h; subst h
    refine ⟨⟨ge, gs⟩, .inr ?_⟩
    simp only [decode, Term.sub]
    exact one_plug gs .ann
  | Let q v f =>
    simp only [step, stepEval] at h
    split at h
    · rename_i l
      cases h
      refine ⟨⟨ge, ⟨⟨l, ge⟩, gs⟩⟩, .inl ⟨by simp [decode, plug, Term.sub], ?_⟩⟩
      simp [μ, pend] <;> omega
    · rename_i l
      cases h
      refine ⟨⟨⟨trivial, ge⟩, gs⟩, .inr ?_⟩
      simp only [decode, Val.rbs, env_inst, Val.rb, Term.sub]
      exact one_plug gs (.unlet (fun l' => absurd l' l) (fun e => by subst e; simp [Quan.live] at l))
  | Tup q a b =>
    simp only [step, stepEval] at h
    split at h
    · rename_i l
      cases h
      refine ⟨⟨ge, ⟨⟨l, ge⟩, gs⟩⟩, .inl ⟨by simp [decode, plug, Term.sub], ?_⟩⟩
      simp [μ, pend] <;> omega
    · rename_i l
      cases h
      refine ⟨⟨ge, ⟨⟨trivial, fun l' => absurd l' l⟩, gs⟩⟩,
        .inl ⟨by simp [decode, plug, Term.sub, Val.rb], ?_⟩⟩
      simp [μ, pend] <;> omega
  | App _ _ _ | Rwt _ _ _ | Min _ _ =>
    simp only [step, stepEval, Option.some.injEq] at h; subst h
    refine ⟨⟨ge, ⟨ge, gs⟩⟩, .inl ⟨by simp [decode, plug, Term.sub], ?_⟩⟩
    simp [μ, pend] <;> omega
  | Lab _ | Rfl =>
    simp only [step, stepEval, Option.some.injEq] at h; subst h
    refine ⟨⟨trivial, rfl, gs⟩, .inl ⟨by simp [decode, Term.sub, Val.rb], ?_⟩⟩
    simp [μ] <;> omega
  | _ =>
    simp only [step, stepEval, Option.some.injEq] at h; subst h
    refine ⟨⟨⟨ge, ?_⟩, rfl, gs⟩, .inl ⟨rfl, ?_⟩⟩
    · simp only [Val.rb, Term.sub]; constructor
    · simp [μ] <;> omega

theorem ret_sound (hj : Jump.Sound bk jump) (gv : Good bk v) (lv : v.live)
    (gs : GoodFrames bk (fr :: fs)) (h : step bk jump (.ret v (fr :: fs)) = some s') :
    StepSound bk (.ret v (fr :: fs)) s' := by
  have ⟨gf, gs'⟩ := gs
  cases fr with
  | appF q x e =>
    simp only [step, stepRet] at h
    split at h
    · rename_i l
      cases h
      refine ⟨⟨gf, ⟨⟨l, gv, lv⟩, gs'⟩⟩, .inl ⟨by simp [decode, plug], ?_⟩⟩
      simp [μ, pend] <;> omega
    · rename_i l
      exact (apply_sound hj gv (x := .dead x e) trivial (fun l' => absurd l' l) gs' h).stepSound
        (by simp [decode, plug, Val.rb]) (by simp [μ, pend])
  | appX q f =>
    simp only [step, stepRet] at h
    exact (apply_sound hj gf.2.1 gv (fun _ => lv) gs' h).stepSound (by simp [decode, plug])
      (by simp [μ, pend])
  | appV q a =>
    simp only [step, stepRet] at h
    exact (apply_sound hj gv gf.1 gf.2 gs' h).stepSound (by simp [decode, plug]) (by simp [μ, pend])
  | letV q f e =>
    simp only [step, stepRet] at h
    split at h
    · rename_i c
      cases h
      refine ⟨⟨⟨gv, gf.2⟩, gs'⟩, .inr ?_⟩
      simp only [decode, plug, Val.rbs, env_inst]
      exact one_plug gs' (.unlet (fun _ => good_value gv lv) (fun e => Val.isData_sound (c e)))
    · simp at h
  | tupA q b e =>
    simp only [step, stepRet, Option.some.injEq] at h; subst h
    refine ⟨⟨gf.2, ⟨⟨gv, fun _ => lv⟩, gs'⟩⟩, .inl ⟨by simp [decode, plug], ?_⟩⟩
    simp [μ, pend] <;> omega
  | tupB q a =>
    simp only [step, stepRet, Option.some.injEq] at h; subst h
    refine ⟨⟨⟨gf.1, gf.2, gv, lv⟩, rfl, gs'⟩, .inl ⟨by simp [decode, plug, Val.rb], ?_⟩⟩
    simp [μ, pend]
  | rwt P f e =>
    simp only [step, stepRet] at h
    split at h
    · cases h
      refine ⟨⟨gf, gs'⟩, .inr ?_⟩
      simp only [decode, plug, Val.rb]
      exact one_plug gs' .cast
    · simp at h
  | minA b e =>
    simp only [step, stepRet, Option.some.injEq] at h; subst h
    refine ⟨⟨gf, ⟨⟨gv, lv⟩, gs'⟩⟩, .inl ⟨by simp [decode, plug], ?_⟩⟩
    simp [μ, pend] <;> omega
  | minB a =>
    simp only [step, stepRet] at h
    split at h
    · rename_i i j
      split at h
      · rename_i c
        cases h
        refine ⟨⟨trivial, gs'⟩, .inr ?_⟩
        simp only [decode, plug, Val.rb, rb_nil]
        exact one_plug gs' (.meet c.1 c.2)
      · simp at h
    · simp at h

theorem step_sound (hj : Jump.Sound bk jump) (I : Inv bk s)
    (h : step bk jump s = some s') : StepSound bk s s' := by
  cases s with
  | eval t e fs => exact eval_sound hj I.1 I.2 h
  | ret v fs =>
    cases fs with
    | nil => simp [step] at h
    | cons fr fs => exact ret_sound hj I.1 I.2.1 I.2.2 h

-- Runs
-- ====

theorem decode_init : decode (.eval t [] []) = t := rb_nil t

theorem inv_init : Inv bk (.eval t [] []) := ⟨trivial, trivial⟩

theorem run_sound (hj : Jump.Sound bk jump) (I : Inv bk s)
    (h : run bk jump n s = (s', m)) : Evals bk (decode s) (decode s') := by
  induction n generalizing s with
  | zero => simp only [run, Prod.mk.injEq] at h; rw [← h.1]; exact .refl
  | succ n ih =>
    simp only [run] at h
    split at h
    · rename_i s1 hs
      have ⟨I1, r⟩ := step_sound hj I hs
      have e := ih I1 h
      rcases r with ⟨d, _⟩ | p
      · rwa [← d]
      · exact evals_trans (plus_evals p) e
    · simp only [Prod.mk.injEq] at h; rw [← h.1]; exact .refl

-- some k steps take s to a state sf where no step fits. The term d of s and
-- the bound n on μ s are for the induction.
theorem run_ends (hj : Jump.Sound bk jump) :
    ∀ d, Acc (fun u t => Plus bk t u) d → ∀ n s, μ s ≤ n → decode s = d → Inv bk s →
      ∃ k sf, step bk jump sf = none ∧ Evals bk d (decode sf) ∧
        ∀ m, run bk jump (k + m) s = (sf, m) := by
  intro d acc
  induction acc with
  | intro d _ ihd =>
    intro n
    induction n using Nat.strongRecOn with
    | _ n ihn =>
      intro s hμ hd I
      cases hs : step bk jump s with
      | none =>
        refine ⟨0, s, hs, hd ▸ .refl, fun m => ?_⟩
        cases m <;> simp [run, hs]
      | some s1 =>
        have ⟨I1, r⟩ := step_sound hj I hs
        have ⟨k, sf, hsf, ev, hr⟩ : ∃ k sf, step bk jump sf = none ∧ Evals bk d (decode sf) ∧
            ∀ m, run bk jump (k + m) s1 = (sf, m) := by
          rcases r with ⟨e, lt⟩ | p
          · exact ihn (μ s1) (by omega) s1 (Nat.le_refl _) (e.trans hd) I1
          · obtain ⟨k, sf, hsf, ev, hr⟩ := ihd (decode s1) (hd ▸ p) (μ s1) s1 (Nat.le_refl _) rfl I1
            exact ⟨k, sf, hsf, evals_trans (hd ▸ plus_evals p) ev, hr⟩
        refine ⟨k + 1, sf, hsf, ev, fun m => ?_⟩
        rw [show k + 1 + m = (k + m) + 1 by omega]
        simp [run, hs, hr]

end Interp.Machine
