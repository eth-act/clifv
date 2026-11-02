import FV.Backend.Proof.StockLoopCarryBounded
import FV.Backend.Proof.StockParameterLoopProbe
import FV.Backend.Proof.LowerDecide
import FV.Backend.Proof.StockScalarCheck

/-! Non-vacuity of the back-edge carry (#140, T7b-3) on the `while` loop `%f0` of
`cranelift/filetests/filetests/inline/control-flow.clif` (`ParameterLoopCfg.Probe.whileLoop`).

On its back edge `block2 → block1` the forward demand premise fails: the header scan demands
`v0` at entry (the loop body reads it), but the latch's terminator scan does not. The header
carry contains `v0`, is available at the latch's entry, and discharges every structural
premise of the latch's carry composition `jump_body_carry_returns_below` and of the forward
edge `block1 → block2` into the loop body. -/

namespace Backend.Stock.Proof.LoopCarry.Witness
open Backend.Proof Backend.Proof.Driver Backend.Stock.ParameterLoopCfg.Probe
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- The loop body: block 2, which ends in the back edge. -/
def latch : Clif.Block :=
  { id := 2, params := [],
    body := [⟨[6],.binary .iadd .i32 3 0⟩,⟨[7],.iconst .i32 1⟩,⟨[8],.binary .iadd .i32 4 7⟩],
    term := .jump ⟨1,[6,8]⟩ }

/-- The loop header: block 1. -/
def header : Clif.Block :=
  { id := 1, params := [(3,.i32),(4,.i32)], body := [⟨[5],.icmp .eq .i32 1 4⟩],
    term := .brif 4 ⟨3,[]⟩ ⟨2,[]⟩ }

private theorem latch_source : whileLoop.blocks[2]? = some latch := rfl
private theorem header_source : whileLoop.blocks[1]? = some header := rfl
private theorem header_found : whileLoop.block? 1 = some header := rfl
private theorem header_index : blockIdx? whileLoop 1 = some 1 := rfl

/-- The facts of the actual lowering of the `while` loop that the witness uses. -/
def Facts (result : Result) : Prop :=
  result.order.nodes[1]? = some (.original 1) ∧
  result.order.nodes[2]? = some (.original 2) ∧
  result.order.successors[2]? = some #[1] ∧
  (∃ event ∈ result.blockScans.toList,event.block = 1) ∧
  (∀ event ∈ result.blockScans.toList,event.block = 1 → event.output.state.demand[0]! ≠ 0) ∧
  (∀ event ∈ result.blockScans.toList,event.block = 2 →
    event.output.records.head?.map (fun term => term.output.state.demand[0]!) = some 0) ∧
  0 ∈ availOf whileLoop (availIn whileLoop result.ctx) 1 0 ∧
  ∀ x ∈ availOf whileLoop (availIn whileLoop result.ctx) 1 0,
    x ∈ availOf whileLoop (availIn whileLoop result.ctx) 2 0

instance (result : Result) : Decidable (Facts result) := by
  unfold Facts
  infer_instance

-- witness: native_decide (the facts of the fixed function's actual lowering only)
private theorem observed : (Stock.lower whileLoop).toOption.map (fun result => decide (Facts result)) =
    some true := by
  native_decide

private theorem class_facts : LowerScope whileLoop ∧ Dominated whileLoop ∧
    ∀ b ∈ whileLoop.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst := by
  have checked := selects_while_loop
  simp only [ParameterLoopCfg.sourceOk,ParameterLoopCfg.sourceLeafEligible,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨⟨⟨⟨controls,bodies⟩,params⟩,returns⟩,scope⟩,dominated⟩,abi⟩ := checked
  refine ⟨lowerScope_of scope,dominated_of dominated,?_⟩
  intro b member stm present
  exact Stock.Scalar.maskMixedBodyEligible_sound
    (List.all_eq_true.mp (List.all_eq_true.mp bodies b member) stm present)

/-- The back edge of the `while` loop needs the carry, and the carry composition of its latch
applies with every structural premise discharged: the header carry `headerCarry` contains `v0`,
which the header scan demands and the latch's terminator scan does not; it is available at the
latch's entry; it covers the back edge (`EdgeCover.of_header`) and the forward edge from the
header into the latch (`EdgeCover.of_demand`). -/
theorem back_edge_carry_witness {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR) (env : Clif.Env) (cp : Clif.Program) :
    ∃ (result : Result) (spec : Control.JumpBodySpec whileLoop result latch 2 2 ⟨1,[6,8]⟩ isem MR env cp)
      (headerSpec : ConditionalValues.ConditionalBodySpec whileLoop result header 1 1 4 ⟨3,[]⟩ ⟨2,[]⟩
        isem MR env cp) (event : BlockScanEvent),
      Stock.lower whileLoop = .ok result ∧ event ∈ result.blockScans.toList ∧ event.block = 1 ∧
      spec.target = 1 ∧ Demanded event.output.state 0 ∧ ¬ Demanded spec.term.output.state 0 ∧
      headerCarry whileLoop result event 0 ∧
      (∀ x,headerCarry whileLoop result event x →
        x ∈ availOf whileLoop (availIn whileLoop result.ctx) spec.core.scan.block 0) ∧
      EdgeCover whileLoop result 1 (header.params.map (·.1)) event.output.state
        (headerCarry whileLoop result event) spec.term.output.state (headerCarry whileLoop result event) ∧
      EdgeCover whileLoop result 2 (latch.params.map (·.1)) spec.core.scan.output.state
        (headerCarry whileLoop result event) headerSpec.term.output.state (headerCarry whileLoop result event) ∧
      ∀ {vals : List Clif.Val} {outMem : Clif.Mem} {fuel : Nat},
        (∀ (left : Nat),left < fuel → ∀ (s : Clif.State) (ρ : Nat → CV) (w : Arm.ArmState),
          s.frame.func = whileLoop → s.callers = [] → s.frame.body = header.body →
          s.frame.term = header.term → SourceDefinedAt whileLoop result.ctx 1 0 s.frame →
          Clif.runLoop env cp left s = .returned vals outMem →
          Inherited.CarryRel whileLoop result event.ctx event.block MR (headerCarry whileLoop result event)
            event.output.state (0,s.frame,s.mem) ρ w →
          RunOkABIAt whileLoop result.code result.edgeArgs isem MR s.frame.slots
            ⟨spec.target,0,ρ,w⟩ (.returned vals outMem)) →
        ∀ (s : Clif.State),s.callers = [] → s.frame.body = latch.body → s.frame.term = latch.term →
          SourceDefinedAt whileLoop result.ctx spec.core.scan.block 0 s.frame →
          Clif.runLoop env cp fuel s = .returned vals outMem → ∀ (ρ : Nat → CV) (w : Arm.ArmState),
          Inherited.CarryRel whileLoop result spec.core.scan.ctx spec.core.scan.block MR
            (headerCarry whileLoop result event) spec.core.scan.output.state (0,s.frame,s.mem) ρ w →
          RunOkABIAt whileLoop result.code result.edgeArgs isem MR s.frame.slots
            ⟨2,spec.preludeCode.size,ρ,w⟩ (.returned vals outMem) := by
  obtain ⟨scope,dominated,family⟩ := class_facts
  have checked := observed
  cases run : Stock.lower whileLoop with
  | error message => rw [run] at checked; cases checked
  | ok result =>
    rw [run] at checked
    have facts : Facts result := of_decide_eq_true (Option.some.inj checked)
    obtain ⟨node1,node2,successors2,⟨event,eventMem,eventBlock⟩,headerDemand,latchDemand,zeroAvailable,
      inclusion⟩ := facts
    obtain ⟨spec⟩ := Control.stock_lower_jump_body_spec run scope dominated family node2 latch_source rfl
      refines driver stable env cp
    obtain ⟨headerSpec⟩ := ConditionalValues.stock_lower_conditional_body_spec run scope dominated family
      node1 header_source rfl refines driver stable env cp
    have row : result.order.successors[2]! = #[1] := by
      simp only [getElem!_def,successors2,Option.getD_some]
    have target : spec.target = 1 := by
      have targets := spec.targets
      rw [row] at targets
      exact (List.cons.inj targets).1.symm
    have targetTag : result.order.nodes[spec.target]? = some (.original 1) := by
      rw [target]
      exact node1
    have latchTerm : ¬ Demanded spec.term.output.state 0 := by
      have head := latchDemand spec.core.scan spec.events spec.atBlock
      rw [spec.split.records] at head
      simp only [List.head?_cons,Option.map_some,Option.some.injEq] at head
      unfold Demanded
      omega
    have carriedHeader : ∀ x,headerCarry whileLoop result event x →
        x ∈ availOf whileLoop (availIn whileLoop result.ctx) 1 0 := by
      intro x carried
      simpa only [eventBlock] using carried.2.1
    have carriedLatch : ∀ x,headerCarry whileLoop result event x →
        x ∈ availOf whileLoop (availIn whileLoop result.ctx) spec.core.scan.block 0 := by
      intro x carried
      rw [spec.atBlock]
      exact inclusion x (carriedHeader x carried)
    have zeroCarried : headerCarry whileLoop result event 0 := by
      refine ⟨headerDemand event eventMem eventBlock,by rw [eventBlock]; exact zeroAvailable,?_⟩
      rw [eventBlock,header_source]
      decide
    have backCover : EdgeCover whileLoop result 1 (header.params.map (·.1)) event.output.state
        (headerCarry whileLoop result event) spec.term.output.state (headerCarry whileLoop result event) := by
      apply EdgeCover.of_header
      intro x demanded available notParameter
      exact headerCarry_covers (by rw [eventBlock]; exact header_source) x demanded
        (by rw [eventBlock]; exact available) notParameter
    have demand := CfgDemand.ordered_scan_demand_of_labels run scope
      (Array.getElem?_eq_some_iff.mp node2).1 (by decide : 1 < 2)
      (by simp only [getElem!_def,node2,Option.getD_some,spec.atBlock])
      (by simp only [getElem!_def,node1,Option.getD_some,headerSpec.atBlock]) spec.events headerSpec.events
      headerSpec.split
    refine ⟨result,spec,headerSpec,event,rfl,eventMem,eventBlock,target,headerDemand event eventMem eventBlock,
      latchTerm,zeroCarried,carriedLatch,backCover,EdgeCover.of_demand demand (fun _ kept => kept),?_⟩
    intro vals outMem fuel continuation s callers remaining atTerm defined returned ρ w held
    exact Control.jump_body_carry_returns_below run scope dominated family refines driver stable spec node2 rfl
      targetTag header_index header_found eventMem eventBlock carriedLatch carriedHeader backCover
      continuation callers remaining atTerm defined returned held

end Backend.Stock.Proof.LoopCarry.Witness
