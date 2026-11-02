import FV.Backend.Proof.StockShiftSemantics
import FV.Backend.Proof.StockShiftRhsObserved
import FV.Backend.Proof.StockShiftMatch
namespace Backend.Stock.Proof.ScalarShift
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

/-- A complete actual shift fragment computes its original amount modulo
width through final aliases and preserves values outside its fresh interval. -/
def ShiftValueOut (F : BitVec 64 → Prop) (isem : Backend.Proof.Sem) (op : ALUOp)
    (w a : Nat) (amount : Clif.Val) (st next : State) (out : V)
    (aliases : Array (Option Nat)) (ρ : Nat → CV) : Prop :=
  ∃ (ms : List MInst) (d : Nat) (ρ' : Nat → CV),out = .reg (.vreg d .int) ∧
    next.base.emitted = st.base.emitted ++ ms.toArray ∧ st.base.nextVreg ≤ next.base.nextVreg ∧
    (st.base.nextVreg ≤ d ∧ d < next.base.nextVreg) ∧
    (∀ m ∈ ms,∀ r ∈ vdefs m,st.base.nextVreg ≤ r ∧ r < next.base.nextVreg) ∧
    PRun F isem (ms.map (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ ρ' ∧
    opnd (szOf w) (ρ' (aliasNum aliases d)) =
      shiftF op (opnd (szOf w) (ρ (aliasNum aliases a))) (amount.bits.toNat % w) ∧
    ∀ n,n < st.base.nextVreg ∨ next.base.nextVreg ≤ n → ρ' n = ρ n

private theorem fresh_alias {aliases : Array (Option Nat)} {d : Nat} (bounded : aliases.size ≤ d) :
    aliasNum aliases d = d := by
  apply chaseF_none
  rw [Array.getElem?_eq_none bounded]
  rfl
private theorem marked (st : State) (x : Nat) (bound : x < st.demand.size) : Demanded (st.mark x) x := by
  rw [Demanded,(mark_demand st x bound).1]
  omega

private theorem one_fragment {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} {op : ALUOp}
    {w a : Nat} {amount : Clif.Val} {st next : State} {out : V} {mi : MInst}
    {aliases : Array (Option Nat)} {ρ ρ' : Nat → CV} (bounded : aliases.size ≤ st.base.nextVreg)
    (outEq : out = .reg (.vreg st.base.nextVreg .int))
    (baseEq : next.base = (st.base.fresh .int).2.emit mi) (defs : vdefs mi = [st.base.nextVreg])
    (execution : PRun F isem [mi.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))] ρ ρ')
    (value : opnd (szOf w) (ρ' st.base.nextVreg) =
      shiftF op (opnd (szOf w) (ρ (aliasNum aliases a))) (amount.bits.toNat % w))
    (kept : ∀ n,n ≠ st.base.nextVreg → ρ' n = ρ n) :
    ShiftValueOut F isem op w a amount st next out aliases ρ := by
  refine ⟨[mi],st.base.nextVreg,ρ',outEq,?_,?_,?_,?_,execution,?_,?_⟩
  · rw [baseEq]; simp only [LState.fresh,LState.emit]; apply Array.ext'; simp
  · rw [baseEq]; simp only [LState.fresh,LState.emit]; omega
  · rw [baseEq]; simp only [LState.fresh,LState.emit]; omega
  · intro m member r defined
    simp only [List.mem_singleton] at member
    subst m
    rw [defs,List.mem_singleton] at defined
    subst r
    rw [baseEq]; simp only [LState.fresh,LState.emit]; omega
  · rw [fresh_alias bounded]; exact value
  · intro n outside
    apply kept
    rw [baseEq] at outside
    simp only [LState.fresh,LState.emit] at outside
    omega

private theorem register_case {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) (wide : Bool) {k y a n : Nat} {op : ALUOp} (operation : Backend.Proof.ShiftOp k op)
    {fr : Clif.Frame} {amount : Clif.Val} (source : fr.regs y = some amount)
    {st next : State} {out : V} {tr trace : Array RuleId} {aliases : Array (Option Nat)} {ρ : Nat → CV}
    (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ x r,ctx.valueReg? x = some r → x < st.demand.size)
    (held : ValuesHeld (fun z => z = y ∧ Demanded next z) ctx fr (fun z => ρ (aliasNum aliases z)))
    (rhs : (evalExpr p (Stock.sem ctx) {} (n+40) (shiftRegisterRule wide).rhs
      (env3 (.data 59 k []) (.reg (.vreg a .int)) (.value y))).run (st,tr) = .ok (some out,next,trace)) :
    ShiftValueOut F isem op (shiftWidth wide) a amount st next out aliases ρ := by
  obtain ⟨safe,ry,mapped,outEq,stateEq⟩ := stock_shift_rrr_rhs_observed hp ctx wide operation.ofIdx rhs
  obtain ⟨ny,rfl⟩ := inv.valueReg y ry mapped
  have needed : Demanded next y := by rw [stateEq]; exact marked st y (extent y _ mapped)
  have input := held.read ⟨rfl,needed⟩ source mapped
  obtain ⟨ρ',execution,value,kept⟩ := stock_shift_rrr_resolved refines operation.isShift
    (w := shiftWidth wide) (by cases wide <;> simp [shiftWidth]) bounded input (a := a)
  apply one_fragment bounded outEq (congrArg State.base stateEq) (ρ' := ρ')
    (mi := .aluRRR op (szOf (shiftWidth wide)) (.vreg st.base.nextVreg .int) (.vreg a .int) (.vreg ny .int))
    rfl execution value kept

private theorem immediate_case {p : Program} (hp : Data p) {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {ctx : Ctx} {k w a n : Nat} {op : ALUOp}
    (operation : Backend.Proof.ShiftOp k op) (width : IW w) {amount : Clif.Val} {c : Int} {shift : Nat}
    (amountEq : shift = amount.bits.toNat % w) (fits : shift < (szOf w).bits)
    {st next : State} {out : V} {tr trace : Array RuleId} {aliases : Array (Option Nat)} {ρ : Nat → CV}
    (bounded : aliases.size ≤ st.base.nextVreg)
    (rhs : (evalExpr p (Stock.sem ctx) {} (n+30) rule_lower_1631.rhs
      (env5 (.data 59 k []) (.ty (.int w)) (.reg (.vreg a .int)) (.int c) (.op (.immShift shift)))).run
      (st,tr) = .ok (some out,next,trace)) : ShiftValueOut F isem op w a amount st next out aliases ρ := by
  obtain ⟨trace',expected⟩ := stock_shift_imm_rhs hp ctx width.le operation.ofIdx st tr n (.vreg a .int) c shift
  have same := Except.ok.inj (rhs.symm.trans expected)
  have outEq := Option.some.inj (congrArg Prod.fst same)
  have stateEq := congrArg (fun q => q.2.1) same
  obtain ⟨ρ',execution,value,kept⟩ := stock_shift_imm_resolved refines operation.isShift width bounded fits (ρ := ρ) (a := a)
  rw [amountEq] at value
  exact one_fragment bounded outEq (congrArg State.base stateEq) rfl execution value kept

private theorem mask_case {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {k w y a n : Nat} {op : ALUOp} (operation : Backend.Proof.ShiftOp k op)
    (width : w = 8 ∨ w = 16) {fr : Clif.Frame} {amount : Clif.Val} (source : fr.regs y = some amount)
    {st next : State} {out : V} {tr trace : Array RuleId} {aliases : Array (Option Nat)} {ρ : Nat → CV}
    (bounded : aliases.size ≤ st.base.nextVreg) (separate : aliasNum aliases a ≠ st.base.nextVreg)
    (extent : ∀ x r,ctx.valueReg? x = some r → x < st.demand.size)
    (held : ValuesHeld (fun z => z = y ∧ Demanded next z) ctx fr (fun z => ρ (aliasNum aliases z)))
    (rhs : (evalExpr p (Stock.sem ctx) {} (n+60) rule_lower_1612.rhs (shiftMaskEnv k w (.vreg a .int) y)).run
      (st,tr) = .ok (some out,next,trace)) : ShiftValueOut F isem op w a amount st next out aliases ρ := by
  obtain ⟨safe,ry,mapped,outEq,stateEq⟩ := stock_shift_mask_rhs_observed hp ctx width operation.ofIdx rhs
  obtain ⟨ny,rfl⟩ := inv.valueReg y ry mapped
  have needed : Demanded next y := by rw [stateEq]; exact marked st y (extent y _ mapped)
  have input := held.read ⟨rfl,needed⟩ source mapped
  have valid : ImmLogic.ofNat? (w-1) .size32 = some ⟨w-1,.size32⟩ := by rcases width with rfl | rfl <;> rfl
  obtain ⟨ρ',execution,value,kept⟩ := stock_shift_mask_resolved refines operation.isShift width bounded separate input valid (a := a)
  let ms : List MInst := [.aluRRImmLogic .and .size32 (.vreg st.base.nextVreg .int) (.vreg ny .int) ⟨w-1,.size32⟩,
    .aluRRR op .size32 (.vreg (st.base.nextVreg+1) .int) (.vreg a .int) (.vreg st.base.nextVreg .int)]
  refine ⟨ms,st.base.nextVreg+1,ρ',outEq,?_,?_,?_,?_,execution,?_,?_⟩
  · rw [stateEq]; simp only [State.mark,LState.fresh,LState.emit,ms]; apply Array.ext'; simp
  · rw [stateEq]; simp only [State.mark,LState.fresh,LState.emit]; omega
  · rw [stateEq]; simp only [State.mark,LState.fresh,LState.emit]; omega
  · intro m member r defined
    simp only [ms,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    all_goals
      change r ∈ [_] at defined
      rw [List.mem_singleton] at defined
      subst r
      rw [stateEq]; simp only [State.mark,LState.fresh,LState.emit]; omega
  · rw [fresh_alias (by omega : aliases.size ≤ st.base.nextVreg+1)]
    have sizeEq : szOf w = .size32 := by rcases width with rfl | rfl <;> rfl
    rw [sizeEq]; exact value
  · intro n outside
    apply kept
    all_goals rw [stateEq] at outside; simp only [State.mark,LState.fresh,LState.emit] at outside; omega

/-- Every successful actual do_shift selection establishes its complete fresh
fragment and the original count value. Local scratch separation is discharged
from original record availability in the retained-record/source bridge. -/
theorem stock_do_shift_values_of_count {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {n k w a y : Nat} {op : ALUOp} (operation : Backend.Proof.ShiftOp k op)
    (width : IW w) (enough : 100 ≤ n) {fr : Clif.Frame} (dfg : DFGCons ctx fr)
    {amount : Clif.Val} (source : fr.regs y = some amount)
    {st next : State} {tr trace : Array RuleId} {out : V} {aliases : Array (Option Nat)} {ρ : Nat → CV}
    (bounded : aliases.size ≤ st.base.nextVreg) (separate : aliasNum aliases a ≠ st.base.nextVreg)
    (extent : ∀ x r,ctx.valueReg? x = some r → x < st.demand.size)
    (held : ValuesHeld (fun z => z = y ∧ Demanded next z) ctx fr (fun z => ρ (aliasNum aliases z)))
    (run : ApplyInternal p (Stock.sem ctx) {} n 27 703 (shiftArgs k w (.vreg a .int) y) (st,tr) out (next,trace)) :
    ShiftValueOut F isem op w a amount st next out aliases ρ := by
  obtain ⟨rule,pre,post,candidates,rejected,m,env,middle,finish,rules,matchBound,matched,rhs,stateEq⟩ :=
    applyTerm_internal_some_first rfl hp.t703 term_703_kind rfl run
  have count : (p.rulesOf 703).length = 4 := by rw [hp.r703]; rfl
  obtain ⟨mf,rfl⟩ : ∃ mf,m = mf+10 := ⟨m-10,by omega⟩
  have finishEq : finish = next := (congrArg Prod.fst stateEq).symm
  subst finish
  rw [hp.r703] at candidates
  isel_rule_cases candidates
  · obtain ⟨c,shift,envEq,middleEq,amountEq,fits⟩ := stock_shift_imm_match_receipts hp inv dfg width source matched
    rw [envEq,middleEq] at rhs
    obtain ⟨nf,fuelEq⟩ : ∃ nf,n = nf+30 := ⟨n-30,by omega⟩
    rw [fuelEq] at rhs
    exact immediate_case hp refines operation width amountEq fits bounded rhs
  · obtain ⟨widthEq,envEq,middleEq⟩ := stock_shift_rrr_match_receipts hp ctx false matched
    rw [envEq,middleEq] at rhs
    rw [widthEq]
    obtain ⟨nf,fuelEq⟩ : ∃ nf,n = nf+40 := ⟨n-40,by omega⟩
    rw [fuelEq] at rhs
    exact register_case hp inv refines false operation source bounded extent held rhs
  · obtain ⟨widthEq,envEq,middleEq⟩ := stock_shift_rrr_match_receipts hp ctx true matched
    rw [envEq,middleEq] at rhs
    rw [widthEq]
    obtain ⟨nf,fuelEq⟩ : ∃ nf,n = nf+40 := ⟨n-40,by omega⟩
    rw [fuelEq] at rhs
    exact register_case hp inv refines true operation source bounded extent held rhs
  · obtain ⟨narrow,envEq,middleEq⟩ := stock_shift_mask_match_receipts hp ctx width matched
    rw [envEq,middleEq] at rhs
    obtain ⟨nf,fuelEq⟩ : ∃ nf,n = nf+60 := ⟨n-60,by omega⟩
    rw [fuelEq] at rhs
    exact mask_case hp inv refines operation narrow source bounded separate extent held rhs
/-- The original demanded-frame variant is retained as a wrapper around
count-restricted coverage; unrelated source values need not be read by the
helper itself. -/
theorem stock_do_shift_values {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {n k w a y : Nat} {op : ALUOp} (operation : Backend.Proof.ShiftOp k op)
    (width : IW w) (enough : 100 ≤ n) {fr : Clif.Frame} (dfg : DFGCons ctx fr)
    {amount : Clif.Val} (source : fr.regs y = some amount)
    {st next : State} {tr trace : Array RuleId} {out : V} {aliases : Array (Option Nat)} {ρ : Nat → CV}
    (bounded : aliases.size ≤ st.base.nextVreg) (separate : aliasNum aliases a ≠ st.base.nextVreg)
    (extent : ∀ x r,ctx.valueReg? x = some r → x < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun z => ρ (aliasNum aliases z)))
    (run : ApplyInternal p (Stock.sem ctx) {} n 27 703 (shiftArgs k w (.vreg a .int) y) (st,tr) out (next,trace)) :
    ShiftValueOut F isem op w a amount st next out aliases ρ := by
  exact stock_do_shift_values_of_count hp inv refines operation width enough dfg source bounded separate extent
    (held.mono (fun _ needed => needed.2)) run

/-- Every successful actual scalar shift allocates a result. This structural
fact is independent of machine-value and scratch-separation hypotheses and
lets the source bridge derive separation from original record availability. -/
theorem stock_do_shift_allocates {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {n k w a y : Nat} {op : ALUOp}
    (operation : Backend.Proof.ShiftOp k op) (width : IW w) (enough : 100 ≤ n)
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {amount : Clif.Val} (source : fr.regs y = some amount)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : ApplyInternal p (Stock.sem ctx) {} n 27 703 (shiftArgs k w (.vreg a .int) y) (st,tr) out (next,trace)) :
    st.base.nextVreg < next.base.nextVreg := by
  obtain ⟨rule,pre,post,candidates,rejected,m,env,middle,finish,rules,matchBound,matched,rhs,stateEq⟩ :=
    applyTerm_internal_some_first rfl hp.t703 term_703_kind rfl run
  have count : (p.rulesOf 703).length = 4 := by rw [hp.r703]; rfl
  obtain ⟨mf,rfl⟩ : ∃ mf,m = mf+10 := ⟨m-10,by omega⟩
  have finishEq : finish = next := (congrArg Prod.fst stateEq).symm
  subst finish
  rw [hp.r703] at candidates
  isel_rule_cases candidates
  · obtain ⟨c,shift,envEq,middleEq,amountEq,fits⟩ := stock_shift_imm_match_receipts hp inv dfg width source matched
    rw [envEq,middleEq] at rhs
    obtain ⟨nf,fuelEq⟩ : ∃ nf,n = nf+30 := ⟨n-30,by omega⟩
    rw [fuelEq] at rhs
    obtain ⟨trace',expected⟩ := stock_shift_imm_rhs hp ctx width.le operation.ofIdx st tr nf (.vreg a .int) c shift
    have same := Except.ok.inj (rhs.symm.trans expected)
    have final := congrArg (fun q => q.2.1.base.nextVreg) same
    simp only [LState.fresh,LState.emit] at final
    omega
  · obtain ⟨widthEq,envEq,middleEq⟩ := stock_shift_rrr_match_receipts hp ctx false matched
    rw [envEq,middleEq] at rhs
    obtain ⟨nf,fuelEq⟩ : ∃ nf,n = nf+40 := ⟨n-40,by omega⟩
    rw [fuelEq] at rhs
    obtain ⟨_,ry,mapped,_,final⟩ := stock_shift_rrr_rhs_observed hp ctx false operation.ofIdx rhs
    rw [final]; simp only [State.mark,LState.fresh,LState.emit]; omega
  · obtain ⟨widthEq,envEq,middleEq⟩ := stock_shift_rrr_match_receipts hp ctx true matched
    rw [envEq,middleEq] at rhs
    obtain ⟨nf,fuelEq⟩ : ∃ nf,n = nf+40 := ⟨n-40,by omega⟩
    rw [fuelEq] at rhs
    obtain ⟨_,ry,mapped,_,final⟩ := stock_shift_rrr_rhs_observed hp ctx true operation.ofIdx rhs
    rw [final]; simp only [State.mark,LState.fresh,LState.emit]; omega
  · obtain ⟨narrow,envEq,middleEq⟩ := stock_shift_mask_match_receipts hp ctx width matched
    rw [envEq,middleEq] at rhs
    obtain ⟨nf,fuelEq⟩ : ∃ nf,n = nf+60 := ⟨n-60,by omega⟩
    rw [fuelEq] at rhs
    obtain ⟨_,ry,mapped,_,final⟩ := stock_shift_mask_rhs_observed hp ctx narrow operation.ofIdx rhs
    rw [final]; simp only [State.mark,LState.fresh,LState.emit]; omega
end Backend.Stock.Proof.ScalarShift
