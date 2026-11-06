import FV.Backend.Proof.StockAcquireAllocated
import FV.Backend.Proof.StockAcquireLineFault

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver E2E
set_option autoImplicit false
set_option Elab.async false

/-- A non-terminator item is not its block's last (`cfg_back`), as `q_op` requires. -/
private theorem k_lt_of_notTerm {R : RL} (hR : R.Wf) {b k : Nat} {vb : VBlock} {i : MInst}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i)
    (ht : i.isTerminator = false) : k + 1 < vb.insts.size := by
  obtain ⟨c, ins, _, hc, -⟩ := hR.check
  obtain ⟨preds, hcfg⟩ := hc.cfg
  obtain ⟨t, hb, htt⟩ := cfg_back hcfg hvb
  have hks := (Array.getElem?_eq_some_iff.1 hi).1
  refine Nat.lt_of_le_of_ne hks fun he => ?_
  rw [Array.back?_eq_getElem?, ← he, Nat.add_sub_cancel, hi] at hb
  cases hb
  rw [ht] at htt
  cases htt

/-- The actual checked load item is the real machine load line with its original trap flag. -/
theorem acquire_byte_line {R : RL} (wellFormed : R.Wf) {s : Arm.ArmState} {b k d pointer : Nat}
    {allocs : Array Loc} {items : List RItem} {values : Loc → CV} {world : Arm.ArmState}
    {block : VBlock} {flags : Clif.MemFlags}
    (related : Q R s (.run ⟨b,.op k allocs :: items,values,world⟩))
    (found : R.vc.blocks[b]? = some block)
    (located : block.insts[k]? = some (.loadAcquire (.int 8) (.vreg d .int) (.vreg pointer .int) flags)) :
    ∃ j destination base,destination < 29 ∧ base < 29 ∧
      R.L[j]? = some (.ins (.ldar 8 (.x destination) (.x base)) flags.trapCode) ∧
      Arm.r .PC s = R.pcOf j ∧ Arm.r .ERR s = .None ∧ s.program = R.fb.program R.base ∧
      ∀ operands,(MInst.loadAcquire (.int 8) (.vreg d .int) (.vreg pointer .int) flags).operands =
        .ok operands →
        ((operands.zip allocs).toList.filter (·.1.isUse)).map (values ·.2) = [regVal s (.x base)] := by
  obtain ⟨j,actualItems,pre,regs,inst,c1,c2,X,ls1,ps1,psm,psm',ps2,x,cc,wh,operands,
    rfl,atItems,split,assigned,first,ops,static,checked,tail,lines1,linesX,linesT,traps,dropped,pc,state,
    segment,segChecked⟩ :=
    q_op wellFormed related found located (k_lt_of_notTerm wellFormed found located rfl)
  have actualOps : (MInst.loadAcquire (.int 8) (.vreg d .int) (.vreg pointer .int) flags).operands =
      .ok #[⟨pointer,.int,.use,.early,.reg⟩,⟨d,.int,.def,.late,.reg⟩] := rfl
  rw [actualOps] at ops
  cases ops
  obtain ⟨size,locations,unique,clobbers⟩ := checkStatic_facts static
  obtain ⟨rn,rd,rfl⟩ := regs2 (by simpa using size.symm)
  have destinationLoc : cc.locOk (.reg rd) .int = true :=
    (locations (⟨d,.int,.def,.late,.reg⟩,.reg rd) (by simp)).1
  have baseLoc : cc.locOk (.reg rn) .int = true :=
    (locations (⟨pointer,.int,.use,.early,.reg⟩,.reg rn) (by simp)).1
  obtain ⟨destination,rfl,destinationBound,d16,d17,d18⟩ := locOk_int destinationLoc
  obtain ⟨base,rfl,baseBound,b16,b17,b18⟩ := locOk_int baseLoc
  have baseAlloc : (Reg.x base).allocatable = true := by
    simp only [CheckCtx.locOk,Loc.cls?,Bool.and_eq_true] at baseLoc
    exact baseLoc.2
  have assign : (MInst.loadAcquire (.int 8) (.vreg d .int) (.vreg pointer .int) flags).assign
      #[.x base,.x destination] = .ok (.loadAcquire (.int 8) (.x destination) (.x base) flags) := rfl
  rw [assign] at assigned
  cases assigned
  have code : c1 = [.inst (.loadAcquire (.int 8) (.x destination) (.x base) flags)] := by
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
  have atLine : R.L[j]? = some (.ins (.ldar 8 (.x destination) (.x base)) flags.trapCode) := by
    have zero := congrArg (·[0]?) dropped
    cases code : flags.trapCode <;>
      simpa [code,CTy.bits,List.getElem?_drop,relaxLines,relaxLine,Line.relaxable?,Insn.relaxTarget?,Insn.condTarget?] using zero
  have held : values (.reg (.x base)) = regVal s (.x base) :=
    state.store (.reg (.x base)) (fun r same => by cases same; exact baseAlloc) trivial
  refine ⟨j,destination,base,destinationBound,baseBound,atLine,pc,state.err,state.prog,?_⟩
  intro operands provided
  rw [actualOps] at provided
  cases provided
  simpa [Operand.isUse] using held

end Backend.Stock.Proof.Acquire810
