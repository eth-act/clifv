import FV.Backend.Proof.StockAcquireConstantPendingValues

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

/-- Actual constant execution preserves the pending value relation and stable memory.
The source step remains successful. This theorem does not execute past a source fault. -/
theorem stock_lower_constant_pending_source {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    {info : IInfo} {ty0 : Clif.Ty} {imm0 : BitVec ty0.width} {x a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.iconst ty0 imm0))
    (results : stm.results = [x]) (infoResults : info.results = [x])
    (mapped : event.ctx.valueReg? x = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (semantics : ∀ aliases i, isem (i.mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size + 1))) = isem i)
    (clifEnv : Clif.Env) (cp : Clif.Program)
    (snapshots : List (Acquire810.SunkReadSnapshot event.ctx clifEnv cp)) :
    ∃ (ty : Clif.Ty) (imm : BitVec ty.width), Clif.Inst.iconst ty0 imm0 = .iconst ty imm ∧
      ∀ (MR : Clif.Mem → Arm.ArmState → Prop),
        (∀ cm w w', SameWorld F w' w → MR cm w → MR cm w') →
        ∀ (fr fr' : Clif.Frame) (cm cm' : Clif.Mem) (ρ : Nat → CV) (w : Arm.ArmState),
          SourceInstResult clifEnv cp event.ctx record.inst (fr, cm) (fr', cm') →
          MR cm w →
          Acquire810.PendingValuesHeld snapshots (fun y => Demanded record.output.state y ∧
            y ∈ availOf f (availIn f result.ctx) bi j) fr
              (fun k => ρ (aliasNum result.final.alias k)) →
          ∃ ρ' w', seqRun isem (record.output.emitted.toList.map (·.mapRegs
            (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ w =
              some (.fall ρ' w') ∧ MR cm' w' ∧
            Acquire810.PendingValuesHeld snapshots (fun y => Demanded record.input y ∧
              y ∈ availOf f (availIn f result.ctx) bi (j + 1)) fr'
                (fun k => ρ' (aliasNum result.final.alias k)) := by
  obtain ⟨ty, imm, d, constant, _, _, transfer⟩ :=
    stock_lower_constant_pending_values run scope dominated events records block statement current
      source clif results infoResults mapped recorded emitted refines semantics
      snapshots
  refine ⟨ty, imm, constant, ?_⟩
  intro MR preserve fr fr' cm cm' ρ w step memory held
  obtain ⟨info', inst', vals, regs, rest, lookup, original, _, evaluated, written, frame⟩ := step
  have sameInfo : info' = info := Option.some.inj (lookup.symm.trans source)
  subst info'
  have sameInst : inst' = .iconst ty0 imm0 := Option.some.inj (original.symm.trans clif)
  subst inst'
  rw [constant] at evaluated
  simp only [instOutcome, Clif.evalInst, pure] at evaluated
  obtain ⟨values, sameMem⟩ := Prod.mk.inj (Clif.Res.ok.inj evaluated)
  rw [← values, infoResults] at written
  simp only [Clif.Regs.setMany_cons, Clif.Regs.setMany_nil, Option.some.injEq] at written
  subst regs
  obtain ⟨ρ', executed, _, installed⟩ := transfer fr ρ held
  obtain ⟨w', runCode, world⟩ := executed w
  refine ⟨ρ', w', runCode, ?_, ?_⟩
  · rw [← sameMem]
    exact preserve _ _ _ world memory
  · change fr' = _ at frame
    rw [frame]
    change Acquire810.PendingValuesHeld snapshots (fun y => Demanded record.input y ∧
      y ∈ availOf f (availIn f result.ctx) bi (j + 1)) (withValue fr x ⟨ty, imm⟩)
        (fun k => ρ' (aliasNum result.final.alias k))
    exact installed

end Backend.Stock.Proof
