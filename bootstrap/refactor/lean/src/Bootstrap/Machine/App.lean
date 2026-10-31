import Bootstrap.Machine.Walk

-- Machine.App
-- ===========
--
-- The moves of a call, and of an application of a value.

open Quan Term

namespace Machine

-- a call that waits for more arguments: v is a value
theorem callMove_admin (vs : Values bk ys) (hv : v = spine (Ref k) ys) (hst : ∀ f ∈ st, f.Ok bk)
    (h : callMove bk k (ys.map fun (q, y) => (q, y, q.live)) st v = .admin s') :
    s'.Ok bk ∧ s'.term = plugs st v := sorry

-- a call that takes a step
theorem callMove_step (vs : Values bk ys) (hv : v = spine (Ref k) ys) (hst : ∀ f ∈ st, f.Ok bk)
    (h : callMove bk k (ys.map fun (q, y) => (q, y, q.live)) st v = .step s') :
    s'.Ok bk ∧ Eval bk (plugs st v) s'.term := sorry

-- App q f x, with f a value, and x a value when q is live
theorem appMove_admin (hf : Value bk f) (hx : q.live = true → Value bk x)
    (hst : ∀ g ∈ st, g.Ok bk) (h : appMove bk q f x st = .admin s') :
    s'.Ok bk ∧ s'.term = plugs st (App q f x) := sorry

theorem appMove_step (hf : Value bk f) (hx : q.live = true → Value bk x)
    (hst : ∀ g ∈ st, g.Ok bk) (h : appMove bk q f x st = .step s') :
    s'.Ok bk ∧ Eval bk (plugs st (App q f x)) s'.term := sorry

end Machine
