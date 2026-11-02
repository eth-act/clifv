import FV.Backend.Proof.StockMemoryAccessAllocated
import FV.Backend.Proof.StockMemoryAccessLineFacts
import FV.Backend.Proof.StockMemoryAccessEncodingFault

namespace Backend.Stock.Proof.MemoryFaults
open Backend.Proof Backend.Proof.Driver E2E
set_option autoImplicit false
set_option Elab.async false

/-- The actual checked load item is the real machine load line with its original trap flag. -/
theorem load_unsigned_line {R : RL} {s : Arm.ArmState} {b k d pointer offset sb : Nat}
    {allocs : Array Loc} {items : List RItem} {values : Loc → CV} {world : Arm.ArmState}
    {block : VBlock} {flags : Clif.MemFlags}
    (related : Q R s (.run ⟨b,.op k allocs :: items,values,world⟩))
    (found : R.vc.blocks[b]? = some block)
    (located : block.insts[k]? = some (.load .uload64 (.vreg d .int)
      (.unsignedOffset (.vreg pointer .int) offset) flags)) :
    ∃ j destination base,destination < 29 ∧ base < 29 ∧
      R.L[j]? = some (.ins (.load .uload64 (.x destination) (.unsignedOffset (.x base) offset)) flags.trapCode) ∧
      Arm.r .PC s = R.pcOf j ∧ Arm.r .ERR s = .None ∧ s.program = R.fb.program R.base ∧
      ∀ operands,(MInst.load .uload64 (.vreg d .int) (.unsignedOffset (.vreg pointer .int) offset) flags).operands =
        .ok operands →
        ((operands.zip allocs).toList.filter (·.1.isUse)).map (values ·.2) = [regVal s (.x base)] := by
  obtain ⟨j,actualItems,pre,regs,inst,c1,c2,ls1,ls2,ps1,psm,ps2,T,cc,wh,operands,
    rfl,atItems,split,assigned,first,ops,static,checked,tail,lines1,lines2,traps,dropped,pc,state⟩ :=
    q_op related found located
  have actualOps : (MInst.load .uload64 (.vreg d .int) (.unsignedOffset (.vreg pointer .int) offset) flags).operands =
      .ok #[⟨d,.int,.def,.late,.reg⟩,⟨pointer,.int,.use,.early,.reg⟩] := rfl
  rw [actualOps] at ops
  cases ops
  obtain ⟨size,locations,unique,clobbers⟩ := checkStatic_facts static
  obtain ⟨rd,rn,rfl⟩ := regs2 (by simpa using size.symm)
  have destinationLoc : cc.locOk (.reg rd) .int = true :=
    (locations (⟨d,.int,.def,.late,.reg⟩,.reg rd) (by simp)).1
  have baseLoc : cc.locOk (.reg rn) .int = true :=
    (locations (⟨pointer,.int,.use,.early,.reg⟩,.reg rn) (by simp)).1
  obtain ⟨destination,rfl,destinationBound,d16,d17,d18⟩ := locOk_int destinationLoc
  obtain ⟨base,rfl,baseBound,b16,b17,b18⟩ := locOk_int baseLoc
  have baseAlloc : (Reg.x base).allocatable = true := by
    simp only [CheckCtx.locOk,Loc.cls?,Bool.and_eq_true] at baseLoc
    exact baseLoc.2
  have assign : (MInst.load .uload64 (.vreg d .int) (.unsignedOffset (.vreg pointer .int) offset) flags).assign
      #[.x destination,.x base] = .ok (.load .uload64 (.x destination) (.unsignedOffset (.x base) offset) flags) := rfl
  rw [assign] at assigned
  cases assigned
  have code : c1 = [.inst (.load .uload64 (.x destination) (.unsignedOffset (.x base) offset) flags)] := by
    rcases first with normal | args | returns
    · exact normal.1
    · obtain ⟨args,impossible,empty⟩ := args
      cases impossible
    · obtain ⟨returns,impossible,empty⟩ := returns
      cases impossible
  rw [code] at lines1
  have actualLines := codeLinesE_single lines1
  simp only [MInst.lines,memFinalize,pure,Except.pure,bind,Except.bind,Except.ok.injEq,Prod.mk.injEq] at actualLines
  obtain ⟨rfl,rfl⟩ := actualLines
  have kept : ftList ([.ins (.load .uload64 (.x destination) (.unsignedOffset (.x base) offset)) flags.trapCode] ++
      (ls2 ++ nxtOf R.af b)) =
      [.ins (.load .uload64 (.x destination) (.unsignedOffset (.x base) offset)) flags.trapCode] ++
        ftList (ls2 ++ nxtOf R.af b) := by
    apply ftList_prefix
    intro line member
    have same := List.mem_singleton.mp member
    subst line
    constructor
    · intro target code impossible
      cases impossible
    · intro inst same
      rw [← (Line.ins.inj same).1]
      rfl
  simp only [List.nil_append] at dropped
  rw [kept] at dropped
  have atLine : R.L[j]? = some (.ins (.load .uload64 (.x destination) (.unsignedOffset (.x base) offset)) flags.trapCode) := by
    have zero := congrArg (·[0]?) dropped
    cases code : flags.trapCode <;>
      simpa [code,List.getElem?_drop,relaxLines,relaxLine,Line.relaxable?,Insn.relaxTarget?,Insn.condTarget?] using zero
  have held : values (.reg (.x base)) = regVal s (.x base) :=
    state.store (.reg (.x base)) (fun r same => by cases same; exact baseAlloc) trivial
  refine ⟨j,destination,base,destinationBound,baseBound,atLine,pc,state.err,state.prog,?_⟩
  intro operands provided
  rw [actualOps] at provided
  cases provided
  simpa [Operand.isUse] using held

end Backend.Stock.Proof.MemoryFaults
