import FV.Backend.Proof.StockMaskBodyRefines
import FV.Backend.Proof.StockLocalTrapRefines
import FV.Backend.Proof.StockReturnScanShape
import FV.Backend.Proof.StockScalarContract
import FV.Backend.Proof.IselCtlTerm

/-!
# Stock refinement of scalar blocks that end in `trap`

A one-block function whose body is in the mask family and whose terminator is `trap c` never
returns. When its source run traps, either a body statement trapped first (the existing local
trap prefix) or the whole body ran and the terminator trapped with `c`
(`trap_source_execution`). On the machine side the second case composes the entry prelude, the
body's fall-through code and the terminator chunk, which is exactly `udf c`
(`trap_term_emitted`). Together these give the scalar `Domain` of such functions
(`Scalar.domain_of_maskTrap`), with the return obligation vacuous.
-/

namespace Backend.Stock.Proof.TrapBody
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

private theorem local_step {env : Clif.Env} {cp : Clif.Program}
    {s : Clif.State} {stm : Clif.Stmt} {rest : List Clif.Stmt}
    (remaining : s.frame.body = stm :: rest) (family : LocalBody.LocalInst stm.inst) :
    Clif.step env cp s = Clif.StepResult.ofRes (Clif.evalInst s.frame s.mem stm.inst)
      (fun (vs,cm) => Clif.continueWith s rest stm.results vs cm) := by
  cases shape : stm.inst <;> simp only [shape,LocalBody.LocalInst,pureInst] at family <;> try cases family
  all_goals unfold Clif.step; simp only [remaining,shape]

private theorem local_family {b : Clif.Block} (family : ∀ stm ∈ b.body,MaskBody.Family stm.inst) :
    ∀ stm ∈ b.body,LocalBody.LocalInst stm.inst := by
  intro stm member
  rcases family stm member with (scalar | ⟨op,ty,x,y,shape⟩) | ⟨ty,x,shape⟩ | shape
  · exact LocalBody.LocalInst.of_pure (HighMulBody.family_pure scalar)
  · simp [LocalBody.LocalInst,shape]
  · simp [LocalBody.LocalInst,shape]
  · simp [LocalBody.LocalInst,shape]

/-- At the end of the body, the `trap c` terminator traps with `c`. -/
private theorem trap_term_step {env : Clif.Env} {cp : Clif.Program} {s : Clif.State}
    (empty : s.frame.body = []) {c : Clif.TrapCode} (terminal : s.frame.term = .trap c) :
    Clif.step env cp s = .trapped c := by
  rw [Clif.step_term env cp s empty,terminal]
  rfl

/-- A local body that ends in `trap` never returns. -/
theorem trap_source_noreturn {env : Clif.Env} {cp : Clif.Program} {b : Clif.Block}
    (family : ∀ stm ∈ b.body,LocalBody.LocalInst stm.inst)
    {fuel j : Nat} {s : Clif.State} (remaining : s.frame.body = b.body.drop j)
    {c : Clif.TrapCode} (terminal : s.frame.term = .trap c)
    {vals : List Clif.Val} {mem : Clif.Mem} :
    Clif.runLoop env cp fuel s ≠ .returned vals mem := by
  induction fuel generalizing j s with
  | zero => intro returned; cases returned
  | succ fuel ih =>
    intro returned
    by_cases inside : j < b.body.length
    · let stm := b.body[j]
      have statement : b.body[j]? = some stm := List.getElem?_eq_getElem inside
      have head : s.frame.body = stm :: b.body.drop (j+1) := by
        rw [remaining,List.drop_eq_getElem_cons inside]
      have instFamily := family stm (List.mem_of_getElem? statement)
      rw [Clif.runLoop_succ,local_step head instFamily] at returned
      cases evaluated : Clif.evalInst s.frame s.mem stm.inst with
      | trap c' => simp only [evaluated,Clif.StepResult.ofRes] at returned; cases returned
      | stuck message => simp only [evaluated,Clif.StepResult.ofRes] at returned; cases returned
      | ok pair =>
        obtain ⟨vs,cm⟩ := pair
        simp only [evaluated,Clif.StepResult.ofRes,Clif.continueWith] at returned
        cases written : s.frame.regs.setMany stm.results vs with
        | none => simp only [written] at returned; cases returned
        | some regs =>
          simp only [written] at returned
          exact ih (s := {s with frame := {s.frame with regs,body := b.body.drop (j+1)},mem := cm})
            (j := j+1) rfl terminal returned
    · have empty : s.frame.body = [] := by
        rw [remaining]
        exact List.drop_eq_nil_of_le (by omega)
      rw [Clif.runLoop_succ,trap_term_step empty terminal] at returned
      cases returned

/-- A trapped run of a local body that ends in `trap c` either traps in a body statement, with
the existing indexed trap prefix, or runs the whole body and traps at the terminator with `c`. -/
theorem trap_source_execution {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) {b : Clif.Block} {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body)
    (family : ∀ stm ∈ b.body,LocalBody.LocalInst stm.inst)
    {env : Clif.Env} {cp : Clif.Program} {fuel j : Nat} {s : Clif.State}
    (bound : j ≤ b.body.length) (remaining : s.frame.body = b.body.drop j)
    {c : Clif.TrapCode} (terminal : s.frame.term = .trap c)
    {code : Clif.TrapCode} (trapped : Clif.runLoop env cp fuel s = .trapped code) :
    SourceTrapSteps (IndexedSourceInst env cp f event.ctx event.block)
      (LocalBody.IndexedSourceTrap env cp f event.ctx event.block)
      (List.range' (blockStart f event.block+j) (b.body.length-j)) (j,s.frame,s.mem) code ∨
    (code = c ∧ ∃ s',SourceSteps (IndexedSourceInst env cp f event.ctx event.block)
      (List.range' (blockStart f event.block+j) (b.body.length-j)) (j,s.frame,s.mem) s') := by
  induction fuel generalizing j s with
  | zero => cases trapped
  | succ fuel ih =>
    by_cases done : j = b.body.length
    · have empty : s.frame.body = [] := by simpa [done] using remaining
      rw [Clif.runLoop_succ,trap_term_step empty terminal] at trapped
      simp only [Clif.Outcome.trapped.injEq] at trapped
      subst trapped
      refine Or.inr ⟨rfl,(j,s.frame,s.mem),?_⟩
      rw [done,Nat.sub_self,List.range'_zero]
      exact .nil _
    · have inside : j < b.body.length := by omega
      let stm := b.body[j]
      have statement : b.body[j]? = some stm := List.getElem?_eq_getElem inside
      have head : s.frame.body = stm :: b.body.drop (j+1) := by
        rw [remaining,List.drop_eq_getElem_cons inside]
      have instFamily := family stm (List.mem_of_getElem? statement)
      have length : b.body.length-j = (b.body.length-(j+1))+1 := by omega
      rw [length,List.range'_succ]
      rw [Clif.runLoop_succ,local_step head instFamily] at trapped
      cases evaluated : Clif.evalInst s.frame s.mem stm.inst with
      | trap c' =>
        simp only [evaluated,Clif.StepResult.ofRes,Clif.Outcome.trapped.injEq] at trapped
        cases trapped
        apply Or.inl
        apply SourceTrapSteps.here
        apply LocalBody.actual_local_source_trap run events split statement instFamily head
        rw [local_step head instFamily,evaluated]
        rfl
      | stuck message => simp only [evaluated,Clif.StepResult.ofRes] at trapped; cases trapped
      | ok pair =>
        obtain ⟨vs,cm⟩ := pair
        simp only [evaluated,Clif.StepResult.ofRes,Clif.continueWith] at trapped
        cases written : s.frame.regs.setMany stm.results vs with
        | none => simp only [written] at trapped; cases trapped
        | some regs =>
          simp only [written] at trapped
          let t : Clif.State := {s with frame := {s.frame with regs,body := b.body.drop (j+1)},mem := cm}
          have next : Clif.step env cp s = .next t := by
            rw [local_step head instFamily,evaluated]
            simp only [Clif.StepResult.ofRes,Clif.continueWith,written]
            rfl
          have source := LocalBody.actual_local_source_step run events split
            (record := ⟨blockStart f event.block+j,default,default⟩) statement rfl instFamily head next
          rcases ih (s := t) (j := j+1) (by omega) rfl terminal trapped with tail | ⟨same,s',tail⟩
          · have prefixStep := SourceTrapSteps.next source tail
            exact Or.inl (by simpa only [Nat.add_assoc,Nat.add_comm 1 j] using prefixStep)
          · have prefixStep := SourceSteps.cons source tail
            exact Or.inr ⟨same,s',by simpa only [Nat.add_assoc,Nat.add_comm 1 j] using prefixStep⟩

/-- The terminator chunk of an actual `trap c` scan is exactly `udf c`. -/
theorem trap_term_emitted {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body) {c : Clif.TrapCode}
    (trap : b.term = .trap c) : term.output.emitted = #[.udf c] := by
  obtain ⟨record,body',step,split',records,_,_,recorded,emitted⟩ :=
    stock_lower_retTrap_emitted run scope events split.block (by rw [trap]; rfl)
  have sameTerm : term = record := by
    have both := split.records.symm.trans split'.records
    exact (List.cons.inj both).1
  subst sameTerm
  obtain ⟨original,data,found,prepared,slot⟩ := stock_lower_blockScan_term_data run scope events
  have same := Option.some.inj (found.symm.trans split.block)
  subst original
  rw [trap] at prepared
  change Backend.termData (.trap c) = .ok data at prepared
  rw [termData_trap] at prepared
  cases prepared
  rw [← split'.termInst] at slot
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  obtain ⟨state,_,_⟩ := Control.stock_named_trap_shape slot receipt.rootRun
  have binding := receipt.binding
  simp only [getElem!_def,slot,List.zip_nil_left] at binding
  change Except.ok (receipt.next,#[]) = Except.ok (receipt.bound,receipt.copies) at binding
  obtain ⟨boundEq,copiesEq⟩ := Prod.mk.inj (Except.ok.inj binding)
  have empty : (scanState term.input term.inst).base.emitted = #[] := by
    unfold scanState
    dsimp only
    split <;> rfl
  rw [receipt.code,← boundEq,← copiesEq,state]
  simp only [LState.emit,empty,Array.append_empty]
  rfl

private theorem body_segment {vb : VBlock} {pre chunk post : Array MInst}
    (parts : vb.insts = pre ++ chunk ++ post) : SegAt vb pre.size chunk.toList := by
  intro k hk
  have bound : k < chunk.size := by simpa using hk
  rw [parts,Array.append_assoc,Array.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [Array.getElem?_append_left bound]
  simp [bound]

/-- Actual ABI entry and a trapped source run of a mask-family block that ends in `trap` reach a
real coded trap of the Stock code: either inside the body, or at the terminator's `udf`. -/
theorem actual_entry_trap_refines_frame {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} (blocks : f.blocks = [b])
    (family : ∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {c : Clif.TrapCode} (terminal : b.term = .trap c)
    {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame} (entered : SourceEntry f args fr)
    {env : Clif.Env} {cp : Clif.Program} {fuel : Nat} {code : Clif.TrapCode}
    (trapped : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .trapped code)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    {w : Arm.ArmState} (memory : MR fr.slots cm w) (arguments : ArgsAtEntry F f.sig args w) :
    ∃ ρ,VTrapFrom result.code isem ⟨0,0,ρ,w⟩ code := by
  obtain ⟨event,vb,pre,chunk,ρ',w',events,zero,placed,pieces,execution,mem',values,same,
    after,bodyCode⟩ := stock_lower_entry_prelude_refines_frame run scope dominated entered driver
      memorySem stable memory arguments
  obtain ⟨term,body,split,normal,trapping⟩ := MaskBody.actual_body_refines run scope dominated blocks
    family events refines driver stable (env := env) (cp := cp)
  have facts := entered
  obtain ⟨b',regs,entry,argTypes,paramTypes,set,frame⟩ := facts
  have sameBlock : b' = b := by
    have found : some b = some b' := by
      simpa only [Clif.Function.entry?,blocks,List.head?_cons] using entry
    exact Option.some.inj found.symm
  subst b'
  have held := stock_lower_entered_values_guarded_frame run scope dominated events entered values
    event.output.state w' mem'
  let resolve := Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)
  have emitted := trap_term_emitted run scope events split terminal
  have parts : vb.insts = pre ++ body.code.map (·.mapRegs resolve) ++
      (term.output.emitted.map (·.mapRegs resolve) ++ after) := by
    rw [pieces,bodyCode,split.code,Array.map_append]
    simp only [Array.append_assoc,resolve]
  have segment : SegAt vb pre.size (body.code.toList.map (·.mapRegs resolve)) := by
    simpa only [Array.toList_map] using body_segment parts
  have size : vb.insts.size = pre.size + body.code.size + 1 + after.size := by
    rw [parts,emitted]
    simp only [Array.size_append,Array.size_map,List.size_toArray,List.length_cons,List.length_nil]
    omega
  have preSegment : SegAt vb 0 pre.toList := by
    intro k bounded
    have inside : k < pre.size := by simpa only [Array.length_toList] using bounded
    rw [Nat.zero_add,pieces,Array.getElem?_append_left inside]
    simp [inside]
  have path := seqRun_fall_star (vc := result.code) (sem := isem) placed preSegment
    (by simp only [Nat.zero_add,Array.length_toList]; omega) execution
  simp only [Nat.zero_add,Array.length_toList] at path
  rcases trap_source_execution run events split (local_family family) (s := ⟨fr,[],cm⟩) (j := 0)
    (by omega) (by rw [frame]; simp) (by rw [frame]; exact terminal) trapped with
    sourceTrap | ⟨codeEq,s',steps⟩
  · have trap := trapping (0,fr,cm) code
      (by simpa only [Nat.add_zero,Nat.sub_zero,List.range'_eq_map_range] using sourceTrap) ρ' w' held
    exact ⟨entrySeed event.ctx fr,(DivBody.trapRun_at placed segment trap).prefix path⟩
  · rw [codeEq]
    obtain ⟨ρ'',w'',bodyRun,_⟩ := normal (0,fr,cm) s'
      (by simpa only [Nat.add_zero,Nat.sub_zero,List.range'_eq_map_range] using steps) ρ' w' held
    have bodyPath := seqRun_fall_star (vc := result.code) (sem := isem) placed segment
      (by simp only [List.length_map,Array.length_toList]; omega) bodyRun
    simp only [List.length_map,Array.length_toList] at bodyPath
    have atTrap : vb.insts[pre.size + body.code.size]? = some (.udf c) := by
      rw [parts,emitted,Array.getElem?_append_right (by simp only [Array.size_append,Array.size_map]; omega)]
      simp only [Array.size_append,Array.size_map,Nat.sub_self]
      rw [Array.getElem?_append_left (by simp),Array.getElem?_map]
      rfl
    obtain ⟨w3,halted,_⟩ := refines (.udf c) [] w'' [] w'' (ispec_udf c w'')
    exact ⟨entrySeed event.ctx fr,0,pre.size + body.code.size,ρ'',w'',vb,.udf c,#[],[],w3,
      path.trans bodyPath,placed,atTrap,rfl,halted,rfl⟩

end Backend.Stock.Proof.TrapBody

namespace Backend.Stock.Scalar
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof

/-- Mask-family bodies that end in `trap` meet the scalar source contract. The source never
returns, so the return obligation is vacuous; traps come from the body or the terminator. -/
theorem domain_of_maskTrap {f : Clif.Function}
    (scope : LowerScope f) (dominated : Dominated f) (abi : sigAbiOk f.sig = true)
    {b : Clif.Block} (blocks : f.blocks = [b])
    (family : ∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {c : Clif.TrapCode} (terminal : b.term = .trap c)
    (ordinary : (sigRets f.sig).any (·.purpose == .sret) = false) : Domain f := by
  refine ⟨scope,dominated,abi,ordinary,?_,?_⟩
  · intro result run args cm fr entered env cp fuel vals mem returned F isem refines driver
      sb syms memorySem MR stable w memory arguments
    exfalso
    obtain ⟨b',regs,entry,argTypes,paramTypes,set,frame⟩ := entered
    have sameBlock : b' = b := by
      have found : some b = some b' := by
        simpa only [Clif.Function.entry?,blocks,List.head?_cons] using entry
      exact Option.some.inj found.symm
    subst b'
    exact TrapBody.trap_source_noreturn (TrapBody.local_family family) (s := ⟨fr,[],cm⟩) (j := 0)
      (by rw [frame]; simp) (by rw [frame]; exact terminal) returned
  · intro result run args cm fr entered env cp fuel code trapped F isem refines driver
      sb syms memorySem MR stable w memory arguments
    exact TrapBody.actual_entry_trap_refines_frame run scope dominated blocks family terminal
      entered trapped refines driver memorySem stable memory arguments

end Backend.Stock.Scalar
