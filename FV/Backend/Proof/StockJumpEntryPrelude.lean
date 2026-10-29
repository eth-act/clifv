module

public import FV.Backend.Proof.StockOriginalEntryPrelude
public import FV.Backend.Proof.StockJumpBodyRefines
public import FV.Backend.Proof.PerEdgeSeq

@[expose] public section

namespace Backend.Stock.Proof.Control
open Backend.Proof Backend.Proof.Driver Isle Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- Execute the ABI prelude of the very same canonical entry core used by
the body/jump proof. Its actual assembly, source parameter aliases and entry
values establish the body guard at the exact instruction offset. -/
theorem jump_entry_prelude {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} {bc : Clif.BlockCall} {isem : Backend.Proof.Sem}
    {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : JumpBodySpec f result b 0 0 bc isem MR env cp)
    {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame}
    (entered : SourceEntry f args fr) (driver : DriverSem isem)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) (stable : MRStable F MR)
    {w : Arm.ArmState} (memory : MR fr.slots cm w)
    (arguments : ArgsAtEntry F f.sig args w) :
    ∃ ρ' w',Star (VStepAt result.code result.edgeArgs isem)
      (.run ⟨0,0,entrySeed spec.core.scan.ctx fr,w⟩)
      (.run ⟨0,spec.preludeCode.size,ρ',w'⟩) ∧
      GuardedScanRel f result spec.core.scan.ctx spec.core.scan.block MR
        spec.core.scan.output.state (0,fr,cm) ρ' w' ∧
      ValuesHeld (fun _ => True) spec.core.scan.ctx fr
        (fun key => ρ' (aliasNum result.final.alias key)) ∧ SameWorld F w' w := by
  have block : f.blocks[0]? = some b := by simpa only [spec.atBlock] using spec.split.block
  have nonempty : 0 < spec.core.code.size := by
    rw [spec.bodyCode]
    simp only [Array.size_append,Array.size_singleton]
    omega
  let entry : EntryCoreSpec f result b := {
    ranges := spec.ranges
    params := spec.params
    core := spec.core
    raw := spec.raw
    preludeCode := spec.preludeCode
    build := spec.build
    sizes := spec.sizes
    assembled := spec.assembled
    events := spec.events
    block := block
    rawCode := spec.rawCode
    placed := spec.placed
    nonempty := nonempty }
  exact original_entry_prelude run scope dominated entry entered driver memorySem stable memory arguments

theorem source_defined_entry_frame {f : Clif.Function} (dominated : Dominated f) (ctx : Ctx)
    {args : List Clif.Val} {fr : Clif.Frame}
    (entered : SourceEntry f args fr) : SourceDefinedAt f ctx 0 0 fr := by
  obtain ⟨b,regs,entry,types,paramTypes,set,frame⟩ := entered
  simp only [Clif.Function.entry?,List.head?_eq_getElem?] at entry
  have nodup : (b.params.map (·.1)).Nodup := (List.nodup_append.mp (block_nodup dominated.ssa entry)).1
  intro x available
  obtain ⟨present,_⟩ := (mem_av entry).mp available
  rcases present with parameter | incoming | ⟨j,stm,earlier,_,_⟩
  · obtain ⟨_,v,_,_,value⟩ := setMany_mem set nodup x parameter
    refine ⟨v,?_⟩
    rw [frame]
    exact value
  · have bound := (inFix_fixOk (f := f) (ctx := ctx) (gn := id)).cand 0 x incoming
    omega
  · omega

end Backend.Stock.Proof.Control
