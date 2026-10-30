import FV.Backend.Proof.StockNoOpportunityPre
import FV.Backend.Proof.IselCovTab
import FV.Backend.Proof.IselCovSound
import FV.Backend.Proof.StockDFG

/-! Reuse the existing abstract coverage summaries while forbidding
opportunistic-def constructor calls. This is a fixed-program proof table,
not an accepted-program certificate or a production compiler check. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
attribute [local irreducible] Isle.Aarch64.program
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

private def noOpportunityEntryOk (e : TermId × List AW × AW) : Bool :=
  (program.rulesOf e.1).all
    (aRule program covTab aext actor noOpportunityPre aOracle e.2.1 e.2.2)

private theorem table0_checked : covTab0.all noOpportunityEntryOk = true := by
  decide +kernel

private theorem table1_checked : covTab1.all noOpportunityEntryOk = true := by
  decide +kernel

private theorem table2_checked : covTab2.all noOpportunityEntryOk = true := by
  decide +kernel

private theorem table3_checked : covTab3.all noOpportunityEntryOk = true := by
  decide +kernel

private theorem table4_checked : covTab4.all noOpportunityEntryOk = true := by
  decide +kernel

private theorem table5_checked : covTab5.all noOpportunityEntryOk = true := by
  decide +kernel

private theorem table6_checked : covTab6.all noOpportunityEntryOk = true := by
  decide +kernel

private theorem table7_checked : covTab7.all noOpportunityEntryOk = true := by
  decide +kernel

/-- The existing 704-entry coverage summary table remains checked when the
opportunistic-def constructor is forbidden. No accepted-program premise is added. -/
theorem stock_noOpportunity_table_checked :
    chkTab program covTab aext actor noOpportunityPre aOracle = true := by
  unfold chkTab
  show covTab.all noOpportunityEntryOk = true
  simp only [covTab, List.all_append, table0_checked, table1_checked, table2_checked,
    table3_checked, table4_checked, table5_checked, table6_checked, table7_checked, Bool.and_self]

/-- The abstract bot shortcut cannot admit this forbidden constructor when
its abstract arguments describe real values. -/
theorem stock_noOpportunity_abstract_call_rejected {f : Clif.Function} {ctx : Ctx}
    {as : List AW} {vs : List V} (held : Cov.Holds2 f ctx as vs) (ty : TypeId) :
    aApply program covTab actor noOpportunityPre aOracle ty TId.opportunistic_def as = none := by
  have bot : as.any AW.isBot = false := by
    cases h : as.any AW.isBot with
    | false => rfl
    | true => exact (holds2_bot h held).elim
  simp [aApply, bot, data_program.t181, T.opportunistic_def, noOpportunityPre]

/-- The same forbidden-constructor check also covers the existing statement,
terminator and branch roots. Rule exclusions and root arguments stay unchanged. -/
theorem stock_noOpportunity_roots_checked :
    (program.rulesOf TId.lower).all (fun r => !closureRootIds.contains r.id ||
      aRule program covTab aext actor noOpportunityPre aOracle [.xv .inst] AW.top r) = true ∧
    (program.rulesOf TId.lower).all (fun r => !(r.id == 964 || r.id == 1037) ||
      aRule program covTab aext actor noOpportunityPre aOracle [.c0] AW.top r) = true ∧
    (program.rulesOf TId.lower_branch).all
      (aRule program covTab aext actor noOpportunityPre aOracle [.c0, .c0] AW.top) = true := by
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- A nonempty actual context build provides the source value in the admission
premise; the reused table is nonempty and includes condition helpers. -/
theorem stock_noOpportunity_table_witness :
    covTab.length = 704 ∧
      (∃ entry ∈ covTab, entry.1 = TId.is_nonzero) ∧
      (∃ (f : Clif.Function) (ctx : Ctx) (ranges : Array (Nat × Nat)) (initial : State)
        (as : List AW) (vs : List V),
        Backend.Proof.Driver.LowerScope f ∧ Stock.buildCtx f = .ok (ctx, ranges, initial) ∧
        ctx.valueReg? 2 = some (.vreg 193 .int) ∧ vs ≠ [] ∧ Cov.Holds2 f ctx as vs ∧
          aApply program covTab actor noOpportunityPre aOracle T.opportunistic_def.ret
            TId.opportunistic_def as = none) ∧
      chkTab program covTab aext actor noOpportunityPre aOracle = true ∧
      (program.rulesOf TId.lower_branch).all
        (aRule program covTab aext actor noOpportunityPre aOracle [.c0, .c0] AW.top) = true := by
  have actual : ∃ (f : Clif.Function) (ctx : Ctx) (ranges : Array (Nat × Nat)) (initial : State),
      Backend.Proof.Driver.LowerScope f ∧ Stock.buildCtx f = .ok (ctx, ranges, initial) ∧
        ctx.valueReg? 2 = some (.vreg 193 .int) := by
    obtain ⟨scope, build, mapped, reg⟩ := buildCtx_mappedInv_witness
    exact ⟨_, _, _, _, scope, build, reg⟩
  obtain ⟨f, ctx, ranges, initial, scope, build, reg⟩ := actual
  refine ⟨by decide +kernel, by decide +kernel, ?_, stock_noOpportunity_table_checked,
    stock_noOpportunity_roots_checked.2.2⟩
  let vs : List V := [.value 2, .regs [.vreg 194 .int]]
  let as : List AW := [.top, .top]
  have held : Cov.Holds2 f ctx as vs := ⟨γ_top _, γ_top _, trivial⟩
  exact ⟨f, ctx, ranges, initial, as, vs, scope, build, reg, by decide, held,
    stock_noOpportunity_abstract_call_rejected held _⟩

end Backend.Stock.Proof
