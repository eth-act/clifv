import FV.Backend.Proof.StockLowerArgsFail
import FV.Backend.Proof.StockPolicy

/-!
# Non-vacuity of the Stock `lower` transport

A real Stock context (value 2 lives in `vreg 193`, not in the baseline's identity register) and its
initial scheduling state (nothing sunk) satisfy every premise of `stock_runTerm_lower_of_backend`
for the statement `v2 = iconst.i8 9`: the diverging rules fail by `lower_diverging_args_fail`, and
the baseline `lower` run succeeds. The transported Stock run returns the statement's register.
-/

namespace Backend.Stock.Proof.LowerProjection
open Backend Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64 Backend.Stock.Proof
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private def witnessFunction : Clif.Function := {
  name := "stock_lower_projection_witness"
  sig := {params := [⟨.i64, .none, .normal⟩], returns := [⟨.i8, .none, .normal⟩]}
  blocks := [{id := 5, params := [(7, .i64)], body := [⟨[2], .iconst .i8 9⟩], term := .ret [2]}] }

private def witnessBuilt : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx witnessFunction).toOption.getD (sinkCtx, #[], sinkState)

private theorem witness_build : Stock.buildCtx witnessFunction = .ok witnessBuilt := rfl

private theorem witness_scope : LowerScope witnessFunction := lowerScope_of (by decide +kernel)

private theorem witness_source : witnessBuilt.1.insts[0]? = some witnessBuilt.1.insts[0]! := rfl

private theorem witness_clif : witnessBuilt.1.insts[0]!.clif = some (.iconst .i8 9) := rfl

private theorem witness_register : witnessBuilt.1.valueReg? 2 = some (.vreg 193 .int) := rfl

private theorem witness_unsunk : NoSunk witnessBuilt.2.2 := by
  intro i
  show (Array.replicate witnessBuilt.1.insts.size false)[i]! = false
  by_cases inside : i < witnessBuilt.1.insts.size <;>
    simp [inside] <;> rfl

private theorem witness_noLoad : ∀ (j : Nat) (info : IInfo) (cl : Clif.Inst),
    witnessBuilt.1.insts[j]? = some info → info.clif = some cl →
      (instNames cl).1 ≠ "LoadNoOffset" ∧ (instNames cl).1 ≠ "Load" := by
  intro j info cl hj hc
  have size : witnessBuilt.1.insts.size = 2 := rfl
  have bound := (Array.getElem?_eq_some_iff.mp hj).1
  rcases j with _ | _ | j
  · rw [witness_source] at hj
    cases hj
    rw [witness_clif] at hc
    cases hc
    decide
  · have slot : witnessBuilt.1.insts[1]? = some ⟨.op .unit, [], [], none⟩ := rfl
    rw [slot] at hj
    cases hj
    cases hc
  · omega

/-- Non-vacuity of `stock_runTerm_lower_of_backend`: on a real Stock context with renumbered
value registers, from its initial state, the baseline run of a statement transports to a
successful Stock run. -/
theorem stock_runTerm_lower_of_backend_witness :
    ∃ (ctx : Ctx) (st st' : State) (out : Option V) (tr : List RuleId),
      ctx.valueReg? 2 = some (.vreg 193 .int) ∧ NoSunk st ∧ out.isSome ∧
      Stock.runTerm ctx "lower" [.inst 0] st = .ok (out, st', tr) := by
  have mapped := buildCtx_mappedInv witness_scope witness_build
  have hfail := lower_diverging_args_fail mapped witness_noLoad witness_source witness_clif
    (by intro n hn; simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
        rcases hn with rfl | rfl | rfl | rfl <;> decide)
    (by intro h; exfalso; rcases h with h | h <;> simp [instNames] at h)
  have hb : Backend.runTerm witnessBuilt.1 "lower" [.inst 0] witnessBuilt.2.2.base =
      .ok (some (.regsVec [[.vreg 194 .int]]), _, _) := rfl
  obtain ⟨st', run, -, -⟩ := stock_runTerm_lower_of_backend witnessBuilt.1 witness_unsunk hfail hb
  exact ⟨_, _, st', _, _, witness_register, witness_unsunk, rfl, run⟩

end Backend.Stock.Proof.LowerProjection
