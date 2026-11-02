import FV.Backend.Proof.StockBranchIntervals
import FV.Backend.Proof.StockComparisonLoopCarry

/-! Branches whose emission defines fresh registers keep the carried and demanded values (#140,
CB-12b).

A branch emission may define a temporary register, for example the `uxth t, w` before
`cbnz t` of an `i16` condition. Such a temporary is allocated in the interval from the core input
`spec.input` to the emission output, the branch interval. `stock_lower_available_alias_outside_branch`
gives the branch interval of the actual traversal core of each retained block scan. The core of a
`ConditionalBodySpec` has the same scan, but its input is not fixed by the scan alone. If every
`emitBranch` run of the terminator in its actual context allocates the same number of registers
(`FixedAllocation`), the two cores have the same input frontier
(`ConditionalBodySpec.branch_alias_outside`): the input is at or above the initial frontier, and
the resolved register of every available value is outside the branch interval.

With this fact, a branch emission whose definitions are in its branch interval keeps:

* the carried values (`branch_carry_of_fresh_defs`, the generalization of
  `branch_carry_of_no_defs`), and
* the guarded post-frame of the body (`guarded_of_branch_frame`). -/

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch

/-- Every `emitBranch` run of the terminator of `spec`, in its actual context and at its actual
terminator slot, from any input and with any targets, allocates as many registers as the retained
emission. -/
def ConditionalBodySpec.FixedAllocation {f : Clif.Function} {result : Result} {b : Clif.Block}
    {label bi c : Nat} {yes no : Clif.BlockCall} {isem : Backend.Proof.Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp) : Prop :=
  ∀ (targets : Array Nat) (input : State) (emission : BranchEmission),
    emitBranch spec.core.scan.ctx f (.brif c yes no) bi spec.core.scan.termInst targets input = .ok emission →
    emission.state.base.nextVreg + spec.input.base.nextVreg =
      input.base.nextVreg + spec.origin.emission.state.base.nextVreg

/-- The scan input of the retained core is the output frontier of its branch emission. -/
theorem ConditionalBodySpec.scan_input_frontier {f : Clif.Function} {result : Result} {b : Clif.Block}
    {label bi c : Nat} {yes no : Clif.BlockCall} {isem : Backend.Proof.Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (termShape : b.term = .brif c yes no) :
    spec.core.scan.input.base.nextVreg = spec.origin.emission.state.base.nextVreg := by
  obtain ⟨emission,afterEdges,retained,branchCall,outgoing,scanInput,scanCtx,branchScan,combined⟩ :=
    conditional_core_calls termShape spec.coreRun
  have same : emission = spec.origin.emission := Option.some.inj (retained.symm.trans spec.origin.retained)
  rw [same] at outgoing
  rw [scanInput]
  exact congrArg LState.nextVreg (outgoing_base_extent outgoing).1

/-- **The branch interval of a `ConditionalBodySpec`.** If every run of its branch emission
allocates the same number of registers, the core input of `spec` is at or above the initial
frontier, and the resolved register of every value available at any source point is below the
core input or at or above the emission output. -/
theorem ConditionalBodySpec.branch_alias_outside {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (termShape : b.term = .brif c yes no) (fixed : spec.FixedAllocation) :
    result.initial.base.nextVreg ≤ spec.input.base.nextVreg ∧
      ∀ {bi' j x key : Nat},x ∈ availOf f (availIn f result.ctx) bi' j →
        result.ctx.valueReg? x = some (.vreg key .int) →
        aliasNum result.final.alias key < spec.input.base.nextVreg ∨
          spec.origin.emission.state.base.nextVreg ≤ aliasNum result.final.alias key := by
  obtain ⟨start,stop,data,targets,input,core,coreRun,scanEq,capped,below,outside⟩ :=
    stock_lower_available_alias_outside_branch run scope dominated spec.events
  have block : f.blocks[bi]? = some b := by simpa only [spec.atBlock] using spec.split.block
  have blockEq : f.blocks[spec.core.scan.block]! = b := by
    rw [spec.atBlock,List.getElem!_eq_getElem?_getD,block]
    rfl
  rw [blockEq] at coreRun
  obtain ⟨emission,afterEdges,retained,branchCall,outgoing,scanInput,scanCtx,branchScan,combined⟩ :=
    conditional_core_calls termShape coreRun
  have origin := stock_lowerBlockCore_scanOrigin coreRun
  rw [← scanCtx,← origin.2.2.2.1,scanEq,spec.atBlock] at branchCall
  have counted := fixed targets input emission branchCall
  have traversalFrontier : core.scan.input.base.nextVreg = emission.state.base.nextVreg := by
    rw [scanInput]
    exact congrArg LState.nextVreg (outgoing_base_extent outgoing).1
  rw [scanEq] at traversalFrontier
  have specFrontier := spec.scan_input_frontier termShape
  have sameInput : input.base.nextVreg = spec.input.base.nextVreg := by omega
  refine ⟨sameInput ▸ capped,?_⟩
  intro bi' j x key available mapped
  rw [← sameInput,← specFrontier]
  exact outside available mapped

/-- The resolved form of a branch emission whose definitions are in its branch interval
defines only registers in that interval: the final aliases are below the initial frontier. -/
private theorem resolved_defs_inside {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {lo hi : Nat} (capped : result.initial.base.nextVreg ≤ lo)
    {code : List MInst} (fresh : ∀ m ∈ code,∀ d ∈ vdefs m,lo ≤ d ∧ d < hi) :
    ∀ m ∈ code.map (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))),
      ∀ key ∈ vdefs m,lo ≤ key ∧ key < hi := by
  intro m member key defined
  obtain ⟨raw,inside,rfl⟩ := List.mem_map.mp member
  rw [Resolved.renamed_defs] at defined
  obtain ⟨d,rawDefined,rfl⟩ := List.mem_map.mp defined
  have interval := fresh raw inside d rawDefined
  have bounded := (stock_lower_allocationBounds run).1
  have identity : aliasNum result.final.alias d = d := by
    apply chaseF_none
    rw [Array.getElem?_eq_none (by omega)]
    rfl
  rw [identity]
  exact interval

/-- A stopped run of a branch emission whose definitions are in its branch interval keeps every
register outside that interval. -/
theorem ConditionalBodySpec.branch_stop_frame {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (termShape : b.term = .brif c yes no) (fixed : spec.FixedAllocation)
    (freshDefs : ∀ m ∈ spec.origin.emission.code.toList,∀ d ∈ vdefs m,
      spec.input.base.nextVreg ≤ d ∧ d < spec.origin.emission.state.base.nextVreg)
    {ρ regs : Nat → CV} {world prefixWorld endWorld : Arm.ArmState} {index : Nat} {inst : MInst}
    {ops : Array Operand} {outs : List CV} {control : Ctl}
    (machine : seqRun isem (spec.origin.emission.code.toList.map
      (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ world =
      some (.stop index inst ops regs prefixWorld outs endWorld control)) :
    ∀ key,key < spec.input.base.nextVreg ∨ spec.origin.emission.state.base.nextVreg ≤ key →
      regs key = ρ key := by
  have capped := (spec.branch_alias_outside run scope dominated termShape fixed).1
  intro key outside
  apply Sequence.stop_frame isem machine key
  intro m member defined
  have interval := resolved_defs_inside run capped freshDefs m member key defined
  omega

/-- **The guarded post-frame through a branch emission with fresh definitions.** A register file
that agrees with `ρ` outside the branch interval, and a world with the same nonflag state, keep
the guarded relation of `ρ` at any source point of the block. -/
theorem ConditionalBodySpec.guarded_of_branch_frame {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (termShape : b.term = .brif c yes no) (fixed : spec.FixedAllocation)
    {st : State} {point : Nat} {fr : Clif.Frame} {cm : Clif.Mem}
    {ρ regs : Nat → CV} {world endWorld : Arm.ArmState}
    (post : GuardedScanRel f result spec.core.scan.ctx spec.core.scan.block MR st (point,fr,cm) ρ world)
    (frame : ∀ key,key < spec.input.base.nextVreg ∨ spec.origin.emission.state.base.nextVreg ≤ key →
      regs key = ρ key)
    (nf : SameWorldNF F endWorld world) :
    GuardedScanRel f result spec.core.scan.ctx spec.core.scan.block MR st (point,fr,cm) regs endWorld := by
  obtain ⟨_,outside⟩ := spec.branch_alias_outside run scope dominated termShape fixed
  have mapEq := (stock_lower_record_context run scope spec.events).2.1
  refine ⟨post.1,post.2.1,stable _ _ _ _ nf post.2.2.1,?_⟩
  intro x needed v read
  obtain ⟨n,mapped,holds⟩ := post.2.2.2 x needed v read
  refine ⟨n,mapped,?_⟩
  change VHolds v (regs (aliasNum result.final.alias n))
  rw [frame _ (outside needed.2 (by rw [← mapEq]; exact mapped))]
  exact holds

/-- **`branch_carry_of_no_defs` for a branch emission with fresh definitions.** The body keeps
every carried value (`scalar_body_carry_refines`). A branch emission with a fixed allocation,
whose definitions are in its branch interval, keeps the register of every value available at
the block entry, because that register is outside the branch interval
(`branch_alias_outside`). -/
theorem ConditionalBodySpec.branch_carry_of_fresh_defs {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (termShape : b.term = .brif c yes no) (fixed : spec.FixedAllocation)
    (freshDefs : ∀ m ∈ spec.origin.emission.code.toList,∀ d ∈ vdefs m,
      spec.input.base.nextVreg ≤ d ∧ d < spec.origin.emission.state.base.nextVreg)
    {needed : Nat → Prop}
    (available : ∀ x,needed x → x ∈ availOf f (availIn f result.ctx) spec.core.scan.block 0)
    {s t : Clif.State}
    (steps : SourceSteps (IndexedSourceInst env cp f spec.core.scan.ctx spec.core.scan.block)
      (List.range' (blockStart f spec.core.scan.block) b.body.length)
      (0,s.frame,s.mem) (b.body.length,t.frame,t.mem))
    {ρ : Nat → CV} {world : Arm.ArmState}
    (held : Inherited.CarryRel f result spec.core.scan.ctx spec.core.scan.block MR needed
      spec.core.scan.output.state (0,s.frame,s.mem) ρ world)
    {index : Nat} {inst : MInst} {ops : Array Operand} {regs : Nat → CV} {prefixWorld : Arm.ArmState}
    {outs : List CV} {endWorld : Arm.ArmState} {control : Ctl}
    (machine : seqRun isem (spec.core.code.toList.map
      (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ world =
      some (.stop index inst ops regs prefixWorld outs endWorld control)) :
    ValuesHeld needed spec.core.scan.ctx t.frame (fun key => regs (aliasNum result.final.alias key)) := by
  have block := spec.split.block
  have formats : ∀ block ∈ f.blocks,∀ stm ∈ block.body,CastComplete.MemoryFormat stm.inst := by
    intro block member stm present
    exact MaskBody.family_formats (family block member stm present)
  obtain ⟨ρ',w',bodyRun,post⟩ := (Inherited.scalar_body_carry_refines run scope dominated spec.events spec.split
    formats (family b (List.mem_of_getElem? block)) available refines driver stable (env := env) (cp := cp)).1
    (0,s.frame,s.mem) (b.body.length,t.frame,t.mem)
    (by simpa only [List.range'_eq_map_range,sourceBodyIndices,List.reverse_reverse] using steps)
    ρ world (by simpa only [spec.split.state] using held)
  rw [spec.bodyCode,Array.toList_append,List.map_append,seqRun_append_fall isem bodyRun] at machine
  cases branch : seqRun isem (spec.origin.emission.code.toList.map
      (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ' w' with
  | none =>
    rw [branch] at machine
    cases machine
  | some ending =>
    rw [branch] at machine
    cases ending with
    | fall _ _ => cases machine
    | stop index' inst' ops' regs' prefixWorld' outs' endWorld' control' =>
      simp only [Option.map_some,Option.some.injEq,SeqEnd.shift,SeqEnd.stop.injEq] at machine
      obtain ⟨_,_,_,registers,_⟩ := machine
      subst registers
      have frame := spec.branch_stop_frame run scope dominated termShape fixed freshDefs branch
      obtain ⟨_,outside⟩ := spec.branch_alias_outside run scope dominated termShape fixed
      have mapEq := (stock_lower_record_context run scope spec.events).2.1
      intro x need v read
      obtain ⟨n,mapped,holds⟩ := post.2 x need v read
      refine ⟨n,mapped,?_⟩
      change VHolds v (regs' (aliasNum result.final.alias n))
      rw [frame _ (outside (available x need) (by rw [← mapEq]; exact mapped))]
      exact holds

end Backend.Stock.Proof.ConditionalValues
