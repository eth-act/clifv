import FV.Backend.Proof.StockAcquireConstantPendingAliasRefines
import FV.E2E.StockAcquirePendingPairedStutter
import FV.E2E.StockAcquireGuardedRename
import FV.Opt.Proof.SemFacts

namespace E2E.StockAcquirePending
open Backend.DeadCleanup
open Backend Backend.Stock Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
open Backend.Stock.Proof.Acquire810
set_option autoImplicit false
set_option Elab.async false

/-- Actual constants execute in both guarded worlds with the full capture history.
The existing read and call guards remain unchanged. -/
theorem stock_lower_constant_pending_paired_scan_value {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    {info : IInfo} {ty : Clif.Ty} {imm : BitVec ty.width} {x a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.iconst ty imm))
    (results : info.results = [x]) (statementResults : stm.results = [x])
    (mapped : event.ctx.valueReg? x = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {Γ : Rel} {c : BitVec 64} {D : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem}
    (tls : XTls Γ.F X) {env : Clif.Env} {cp : Clif.Program}
    (snapshots : List (SunkReadSnapshot event.ctx env cp)) :
    ScanFallRefines (IndexedSourceInst env cp f event.ctx bi) (pairSem (valueSem Γ.F fc X))
      result.final.alias (PairedPendingScanRel f result event.ctx bi env cp Γ c D snapshots) record := by
  apply paired_pending_scan_of_guarded_stutter_value (tls := tls)
  · intro Rd
    apply stock_lower_constant_pending_alias_refines run scope dominated events records block statement current
      source clif results statementResults mapped recorded emitted
      (refines_valueSemG (F := Γ.F) (ctx := fc) (X := X) (Rd := Rd)
        (syms := Γ.syms) (exts := []) (sigs := []) (sp0 := 0) (Pc := fun _ _ _ _ => False))
      ?_ (mrStable_relW Γ f c) snapshots
    intro aliases i
    apply valueSemG_mapRegs
    refine ⟨fun n cls => resolve_vreg aliases _ n cls,?_⟩
    intro reg real
    cases reg with
    | vreg n cls => exact False.elim (real n cls rfl)
    | _ => simp [Backend.lowerFunction.resolve]
  · intro before after indexed
    obtain ⟨index,advance,stepped⟩ := indexed
    obtain ⟨actual,inst,values,regs,rest,present,original,remaining,outcome,written,updated⟩ := stepped
    have infoEq := Option.some.inj (present.symm.trans source)
    subst actual
    have instEq := Option.some.inj (original.symm.trans clif)
    subst inst
    rw [instOutcome_of_pure (show pureInst (.iconst ty imm) = true from rfl)] at outcome
    exact (evalInst_pure (by rfl) outcome).1

end E2E.StockAcquirePending
