import FV.Backend.Proof.StockMemoryLoad
import FV.Backend.Proof.StockMemorySelection
import FV.Backend.Proof.StockMemoryLoadSelection
import FV.E2E.Main
import FV.Backend.Proof.MemRefines

namespace Backend.Stock.Memory.LoadFixture
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

def flags : Clif.MemFlags := {trapCode := none}
def function : Clif.Function := {
  name := "mapped_load_return"
  sig := {params := [⟨.i64,.none,.normal⟩],returns := [⟨.i32,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(0,.i64)],term := .jump ⟨1,[]⟩},
    {id := 1,body := [⟨[2],.load .load .i32 flags 0 0⟩],term := .ret [2]}] }
def frame : Clif.Frame := {
  func := function,regs := Clif.Regs.empty.set 0 ⟨.i64,4096⟩,slots := [],
  body := [],term := .ret [2] }
def heap : Clif.Mem := {
  allocs := [⟨4096,4,false⟩],bytes := fun _ => some 165 }
def world : Arm.ArmState := {Arm.ArmState.default with mem := fun _ => 165}
def relation : E2E.Rel := ⟨fun _ => False,fun _ => none,0,0⟩
private def built : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx function).toOption.getD (Proof.sinkCtx,#[],Proof.sinkState)
private def aliases : Array (Option Nat) := (Array.replicate 194 none).set! 193 (some 194)
private def registers (n : Nat) : CV := if n = 192 then ofX 4096 else 0

private theorem frame_dfg : DFGCons built.1 frame := by
  constructor
  · intro x j info cl v defined found original pure lookup
    by_cases zero : x = 0
    · subst x
      have absent : built.1.defInst? 0 = none := rfl
      rw [absent] at defined
      cases defined
    · simp [frame,Clif.Regs.set,Clif.Regs.empty,zero] at lookup
  · intro x t v typed lookup
    by_cases zero : x = 0
    · subst x
      change some (.int 64) = some t at typed
      cases typed
      cases lookup
      rfl
    · simp [frame,Clif.Regs.set,Clif.Regs.empty,zero] at lookup

private theorem pointer_held :
    Proof.ValueHeld built.1 frame (fun k => registers (Proof.aliasNum aliases k)) 0 := by
  intro pv source
  have equal : pv = ⟨.i64,4096⟩ := Option.some.inj source.symm
  subst pv
  exact ⟨192,rfl,rfl⟩

/-- The successful load reads a live, initialized, nonzero four-byte heap. -/
theorem source_load :
    Clif.evalInst frame heap (.load .load .i32 flags 0 0) =
      .ok ([⟨.i32,2779096485⟩],heap) := rfl

theorem memory_world : relation.holds function frame.slots heap world := by
  refine ⟨⟨?_,?_,rfl⟩,?_,E2E.outRel_zero _ _ _⟩
  · intro a b valid byte
    have equal : (165 : BitVec 8) = b := Option.some.inj byte
    subst b
    rfl
  · intro a n valid
    have bound : 4096 ≤ a ∧ a + n ≤ 4100 := by
      simpa [heap,Clif.Mem.valid,Clif.Alloc.contains] using valid
    exact ⟨by omega,fun _ _ h => h⟩
  · intro id b present
    cases present

/-- The generic source/machine bridge has inhabited original world premises and
a real nonzero source result. Registers 0 and 2 are not the selected 192/194. -/
theorem load_source_result_witness (X : ExtSem) :
    ∃ w' out, csem relation.F ⟨0,0⟩ X
      (.load .uload32 (.vreg 194 .int) (.unscaled (.vreg 192 .int) 0) flags)
      [ofX 4096] world = some ([out],w',.next) ∧
      SameWorld relation.F w' world ∧ relation.holds function frame.slots heap w' ∧
      VHolds ⟨.i32,2779096485⟩ out := by
  obtain ⟨w',out,run,same,memory,values⟩ := load_source_result
    (E2E.mrStable_holds relation function)
    (memRefines_csem relation.F ⟨0,0⟩ X rfl (fun _ _ h => by cases h))
    (E2E.memRelOk_holds relation function) memory_world
    (aop := .uload32) (d := 194) (am := .unscaled (.vreg 192 .int) 0) (uses := [ofX 4096])
    (by decide) rfl rfl (by decide) (by decide)
    (by intro pv h; have equal : pv = ⟨.i64,4096⟩ := Option.some.inj h.symm
        subst pv; rfl) source_load
  exact ⟨w',out,run,same,memory,values _ (by simp)⟩

/-- The resolved template executes with the actual dense context mapping and a
nonempty final alias array, preserving every register except fresh result194. -/
theorem mapped_load_witness (X : ExtSem) :
    ∃ ρ' w', seqRun (csem relation.F ⟨0,0⟩ X)
      [(MInst.load .uload32 (.vreg 194 .int) (.unscaled (.vreg 192 .int) 0) flags).mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size + 1))]
      registers world = some (.fall ρ' w') ∧
      SameWorld relation.F w' world ∧ relation.holds function frame.slots heap w' ∧
      VHolds ⟨.i32,2779096485⟩ (ρ' 194) ∧ (∀ k, k ≠ 194 → ρ' k = registers k) := by
  have address := mapped_unscaled_address (sb := 0) (bytes := 4) (w := world)
    pointer_held (show built.1.valueReg? 0 = some (.vreg 192 .int) from rfl)
    frame_dfg (show built.1.valueType? 0 = some (.int 64) from rfl) (off := 0) (by omega)
  obtain ⟨ρ',w',run,same,memory,values,keep⟩ := mapped_unscaled_load
    (E2E.mrStable_holds relation function)
    (memRefines_csem relation.F ⟨0,0⟩ X rfl (fun _ _ h => by cases h))
    (E2E.memRelOk_holds relation function) memory_world
    (d := 194) (show aliases.size ≤ 194 from by decide +kernel)
    pointer_held (show built.1.valueReg? 0 = some (.vreg 192 .int) from rfl)
    frame_dfg (show built.1.valueType? 0 = some (.int 64) from rfl)
    (aop := .uload32) (by decide) rfl rfl (by decide) (by decide) (by omega) source_load
  exact ⟨ρ',w',run,same,memory,values _ (by simp),keep⟩

/-- Actual load helper selection on the dense source context emits the same
fresh load template used by the nonzero-heap execution witness. -/
theorem selected_load_helper_witness :
    ∃ next trace,
      (Isle.Interp.applyTerm Isle.Aarch64.program (Stock.sem built.1) {} 100
        27 533 [.data 89 Isle.Aarch64.VIdx.AMode.Unscaled [.reg (.vreg 192 .int),.op (.simm9 0)],
          .op (.memFlags flags)]).run (Proof.sinkState,#[]) =
        .ok (some (.reg (Proof.sinkState.base.fresh .int).1),next,trace) ∧
      next.base = (Proof.sinkState.base.fresh .int).2.emit
        (.load .uload32 (Proof.sinkState.base.fresh .int).1 (.unscaled (.vreg 192 .int) 0) flags) := by
  exact ⟨_,_,stock_uload32_helper data_program built.1 rfl Proof.sinkState #[] 80 _ _ _ rfl,rfl⟩

/-- Actual rule368's addressing mode executes on the initialized nonzero heap,
with pointer192 and result194 and every other vreg preserved. -/
theorem unsigned_load_witness (X : ExtSem) :
    ∃ ρ' w',seqRun (csem relation.F ⟨0,0⟩ X)
      [.load .uload32 (.vreg 194 .int) (.unsignedOffset (.vreg 192 .int) 0) flags]
      registers world = some (.fall ρ' w') ∧ SameWorld relation.F w' world ∧
      relation.holds function frame.slots heap w' ∧
      VHolds ⟨.i32,2779096485⟩ (ρ' 194) ∧ (∀ k,k ≠ 194 → ρ' k = registers k) := by
  have held : Proof.ValueHeld built.1 frame registers 0 := by
    intro pv source
    have equal : pv = ⟨.i64,4096⟩ := Option.some.inj source.symm
    subst pv
    exact ⟨192,rfl,rfl⟩
  have address := mapped_unsigned_address (sb := 0) (bytes := 4) (w := world)
    held (show built.1.valueReg? 0 = some (.vreg 192 .int) from rfl)
    frame_dfg (show built.1.valueType? 0 = some (.int 64) from rfl) (off := 0) (by decide)
  obtain ⟨ρ',w',run,same,memory,values,keep⟩ := load_source_seqRun
    (E2E.mrStable_holds relation function)
    (memRefines_csem relation.F ⟨0,0⟩ X rfl (fun _ _ h => by cases h))
    (E2E.memRelOk_holds relation function) memory_world
    (d := 194) (am := .unsignedOffset (.vreg 192 .int) 0) (ρ := registers)
    (by intro r member; exact ⟨192,List.mem_singleton.mp member⟩)
    (aop := .uload32) (by decide) rfl rfl (by decide) (by decide) address source_load
  exact ⟨ρ',w',run,same,memory,values _ (by simp),keep⟩

/-- The complete actual load RHS, not a replacement instruction, chooses the
same unsigned addressing mode as the captured source and the semantic witness. -/
theorem selected_load_rhs_witness :
    ∃ trace,(Isle.Interp.evalExpr Isle.Aarch64.program (Stock.sem built.1) {} 120
      Isle.Aarch64.rule_lower_2610.rhs
      (env3 (.value 0) (.op (.memFlags flags)) (.int 0))).run (Proof.sinkState,#[]) =
        .ok (some (.regsVec [[(Proof.sinkState.base.fresh .int).1]]),
          { (Proof.sinkState.mark 0) with base := (Proof.sinkState.base.fresh .int).2.emit (.load .uload32 (Proof.sinkState.base.fresh .int).1 (.unsignedOffset (.vreg 192 .int) 0) flags)},trace) :=
  stock_parameter_load_rhs data_program built.1 rfl rfl rfl flags Proof.sinkState #[] 0

/-- Both nested address helpers are inhabited by the actual parameter context. -/
theorem selected_load_address_witness :
    (Isle.Interp.applyTerm Isle.Aarch64.program (Stock.sem built.1) {} 60 89 575
      [.ty (.int 32),.value 0,.int 0]).run (Proof.sinkState,#[]) =
      .ok (some (.data 89 Isle.Aarch64.VIdx.AMode.UnsignedOffset [.reg (.vreg 192 .int),.op (.uimm12Scaled 0)]),
        Proof.sinkState.mark 0,#[368]) ∧
    (Isle.Interp.applyTerm Isle.Aarch64.program (Stock.sem built.1) {} 80 89 574
      [.ty (.int 32),.value 0,.int 0]).run (Proof.sinkState,#[]) =
      .ok (some (.data 89 Isle.Aarch64.VIdx.AMode.UnsignedOffset [.reg (.vreg 192 .int),.op (.uimm12Scaled 0)]),
        Proof.sinkState.mark 0,#[368,362]) :=
  ⟨stock_parameter_amode_zero data_program built.1 rfl rfl rfl Proof.sinkState #[] 0,
    stock_parameter_load_address data_program built.1 rfl rfl rfl Proof.sinkState #[] 0⟩

end Backend.Stock.Memory.LoadFixture
