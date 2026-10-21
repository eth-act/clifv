import FV.Backend.Proof.StockPopcountScope
namespace Backend.Stock.Proof.Popcount
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000

/-- Actual emission and complete scheduling frame of one unchanged helper. -/
def HelperEmit (cls : RegClass) (st next : State) (v : V) (iv : Reg → V) : Prop :=
  v = .reg (st.base.fresh cls).1 ∧ ∃ m,MInst.ofV (iv (st.base.fresh cls).1) = some m ∧
    next = {st with base := (st.base.fresh cls).2.emit m}

private theorem lift_emit {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {n ty t : Nat} {args : List V}
    (member : t ∈ helperScope) {st next : State} {tr trace : Array RuleId} {v : V}
    (h : ApplyInternal p (Stock.sem ctx) cfg n ty t args (st,tr) v (next,trace))
    {cls : RegClass} {iv : Reg → V}
    (spec : ApplyInternal p (Backend.sem ctx) cfg n ty t args (st.base,tr) v (next.base,trace) →
      EmitOutC cls st.base next.base v iv) : HelperEmit cls st next v iv := by
  obtain ⟨legacy,kept⟩ := UnchangedHelper.observe ctx (helpers_unchanged hp) (helpers_closed hp) hc member h
  obtain ⟨value,m,decoded,base⟩ := spec legacy
  refine ⟨value,m,decoded,?_⟩
  rw [kept]
  exact congrArg (fun q => {st with base := q}) base

theorem mov_to_fpu_observed {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {n : Nat} (hn : 50 ≤ n) {a : V} {k : Nat} (hk : k = 2 ∨ k = 3)
    {st next : State} {tr trace : Array RuleId} {v : V}
    (h : ApplyInternal p (Stock.sem ctx) cfg n 27 409 [a,.data 95 k []] (st,tr) v (next,trace)) :
    HelperEmit .float st next v (fun rd => .data 58 75 [.reg rd,a,.data 95 k []]) :=
  lift_emit hp ctx hc (by decide : 409 ∈ helperScope) h
    (fun old => Backend.Proof.mov_to_fpu_ok hp hc hn hk old)

theorem mov_from_vec_observed {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {n : Nat} (hn : 50 ≤ n) {a i k : V}
    {st next : State} {tr trace : Array RuleId} {v : V}
    (h : ApplyInternal p (Stock.sem ctx) cfg n 27 414 [a,i,k] (st,tr) v (next,trace)) :
    HelperEmit .int st next v (fun rd => .data 58 78 [.reg rd,a,i,k]) :=
  lift_emit hp ctx hc (by decide : 414 ∈ helperScope) h
    (fun old => Backend.Proof.mov_from_vec_ok hp hc hn old)

theorem cnt_observed {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {n : Nat} (hn : 50 ≤ n) {a k : V}
    {st next : State} {tr trace : Array RuleId} {v : V}
    (h : ApplyInternal p (Stock.sem ctx) cfg n 27 524 [a,k] (st,tr) v (next,trace)) :
    HelperEmit .float st next v (fun rd => .data 58 96 [.data 107 17 [],.reg rd,a,k]) :=
  lift_emit hp ctx hc (by decide : 524 ∈ helperScope) h
    (fun old => Backend.Proof.vec_cnt_ok hp hc hn old)

theorem addp_observed {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {n : Nat} (hn : 50 ≤ n) {a b k : V}
    {st next : State} {tr trace : Array RuleId} {v : V}
    (h : ApplyInternal p (Stock.sem ctx) cfg n 27 469 [a,b,k] (st,tr) v (next,trace)) :
    HelperEmit .float st next v (fun rd => .data 58 93 [.data 105 34 [],.reg rd,a,b,k]) :=
  lift_emit hp ctx hc (by decide : 469 ∈ helperScope) h
    (fun old => Backend.Proof.addp_ok hp hc hn old)

theorem addv_observed {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {n : Nat} (hn : 50 ≤ n) {a k : V}
    {st next : State} {tr trace : Array RuleId} {v : V}
    (h : ApplyInternal p (Stock.sem ctx) cfg n 27 473 [a,k] (st,tr) v (next,trace)) :
    HelperEmit .float st next v (fun rd => .data 58 97 [.data 114 0 [],.reg rd,a,k]) :=
  lift_emit hp ctx hc (by decide : 473 ∈ helperScope) h
    (fun old => Backend.Proof.addv_ok hp hc hn old)
end Backend.Stock.Proof.Popcount
