import FV.Backend.Proof.StockPureHelperTransport
import FV.Backend.Proof.StockBmaskHelper

namespace Backend.Stock.Proof.ScalarMask
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

/-- The pure children of `lower_bmask`. The outer recursive helper and
`with_flags_reg` need their own input-sensitive proofs. -/
def pureChildIds : List Nat :=
  [175,201,235,305,356,360,391,428,502,1791,1802,1822,1823,1852,1966,1972,2028,2029]

section Certificate
attribute [local semireducible] Isle.Aarch64.program
private theorem children_checked :
    pureChildIds.all (PureHelper.checkTerm program pureChildIds) = true := by
  decide +kernel
end Certificate

/-- Project an actual successful pure child call and retain every scheduling
field. This includes operand-size, CMP, CSETM and logical-immediate helpers. -/
theorem stock_mask_child (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {fuel ty t : Nat} (member : t ∈ pureChildIds)
    (args : List V) {st next : State} {before trace : Array RuleId} {out : V}
    (run : ApplyInternal program (Stock.sem ctx) cfg fuel ty t args
      (st,before) out (next,trace)) :
    ApplyInternal program (Backend.sem ctx) cfg fuel ty t args
      (st.base,before) out (next.base,trace) ∧ next = {st with base := next.base} := by
  have projected := PureHelper.projects children_checked ctx hc (fuel+1) ty t member args st before
  unfold ApplyInternal at run ⊢
  rw [run] at projected
  exact ⟨projected.symm,PureHelper.preserves children_checked ctx hc member args run⟩

/-- The pure-child transport is inhabited by an actual CSETM execution, with a
genuine condition and allocation, rather than an assumed successful call. -/
theorem stock_mask_child_witness :
    ∃ (out : V) (next : State) (trace : Array RuleId),
      ApplyInternal program (Stock.sem sinkCtx) {} 999 49 428 [.data 96 1 []]
        (sinkState,#[]) out (next,trace) ∧
      ApplyInternal program (Backend.sem sinkCtx) {} 999 49 428 [.data 96 1 []]
        (sinkState.base,#[]) out (next.base,trace) ∧
      next = {sinkState with base := next.base} := by
  obtain ⟨out,next,trace,run,_⟩ := stock_csetm_helper_witness
  have actual : ApplyInternal program (Stock.sem sinkCtx) {} 999 49 428 [.data 96 1 []]
      (sinkState,#[]) out (next,trace) := run
  exact ⟨out,next,trace,actual,
    stock_mask_child sinkCtx rfl (by decide) _ actual⟩

/-- Replay any successful original call within the same checked pure closure. -/
theorem stock_mask_child_replay (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {fuel ty t : Nat} (member : t ∈ pureChildIds)
    (args : List V) (st : State) {base : LState} {before trace : Array RuleId} {out : Option V}
    (legacy : (applyTerm program (Backend.sem ctx) cfg fuel ty t args).run (st.base,before) =
      .ok (out,base,trace)) :
    (applyTerm program (Stock.sem ctx) cfg fuel ty t args).run (st,before) =
      .ok (out,{st with base},trace) :=
  PureHelper.replays children_checked ctx hc member args st legacy

/-- Both directions of the generic transport apply to the real allocating
CSETM call, so the replay premise is inhabited independently. -/
theorem stock_mask_child_replay_witness :
    ∃ (out : V) (next : State) (trace : Array RuleId),
      (applyTerm program (Backend.sem sinkCtx) {} 1000 49 428 [.data 96 1 []]).run
        (sinkState.base,#[]) = .ok (some out,next.base,trace) ∧
      (applyTerm program (Stock.sem sinkCtx) {} 1000 49 428 [.data 96 1 []]).run
        (sinkState,#[]) = .ok (some out,{sinkState with base := next.base},trace) := by
  obtain ⟨out,next,trace,_,legacy,_⟩ := stock_mask_child_witness
  exact ⟨out,next,trace,legacy,
    stock_mask_child_replay sinkCtx rfl (by decide) _ sinkState legacy⟩

end Backend.Stock.Proof.ScalarMask
