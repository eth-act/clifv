import FV.Backend.Proof.StockLogicalSemantics
import FV.Backend.Proof.StockLogicalObserved
import FV.Backend.Proof.StockLogicalFixtures

namespace Backend.Stock.Proof.LogicalSemantics
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

def LogicalValueOut (F : BitVec 64 → Prop) (isem : Backend.Proof.Sem) (cop : Clif.BinaryOp)
    (ty : Clif.Ty) (u v : BitVec ty.width) (st after : State) (out : V)
    (aliases : Array (Option Nat)) (ρ : Nat → CV) : Prop :=
  ∃ (mi : MInst) (ρ' : Nat → CV), out = .reg (.vreg st.base.nextVreg .int) ∧
    after.base = (st.base.fresh .int).2.emit mi ∧
    PRun F isem [mi.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size + 1))] ρ ρ' ∧
    VHolds ⟨ty,Clif.Sem.binary cop u v⟩ (ρ' st.base.nextVreg) ∧
    ∀ n, n ≠ st.base.nextVreg → ρ' n = ρ n

private theorem marked (st : State) (x : Nat) (bound : x < st.demand.size) : Demanded (st.mark x) x := by
  rw [Demanded,(mark_demand st x bound).1]
  omega
private theorem twice_marked (st : State) (x y : Nat) (bx : x < st.demand.size) (by_ : y < st.demand.size) :
    Demanded ((st.mark x).mark y) x ∧ Demanded ((st.mark x).mark y) y := by
  have afterBound : y < (st.mark x).demand.size := by rw [(mark_demand st x bx).2.2]; exact by_
  exact ⟨(demanded_mark_iff (st.mark x) y x afterBound).mpr (Or.inr (marked st x bx)),
    marked (st.mark x) y afterBound⟩

private theorem register_case {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {k : Nat} {op : ALUOp} {cop : Clif.BinaryOp}
    (tag : ALUOp.ofIdx? k = some op) (operation : LogicPair op cop) {ty : Clif.Ty} (width : ty.width ≤ 64)
    {x y n : Nat} {u v : BitVec ty.width} {fr : Clif.Frame}
    (sourceX : fr.getAs x ty = .ok u) (sourceY : fr.getAs y ty = .ok v)
    {st after : State} {out : V} {tr trace : Array RuleId} {aliases : Array (Option Nat)} {ρ : Nat → CV}
    (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ x r, ctx.valueReg? x = some r → x < st.demand.size)
    (held : ValuesHeld (Demanded after) ctx fr (fun z => ρ (aliasNum aliases z)))
    (rhs : (evalExpr p (Stock.sem ctx) {} (n + 40) rule_inst_3916.rhs
      (env4 (.data 59 k []) (.ty (.int ty.width)) (.value x) (.value y))).run (st,tr) = .ok (some out,after,trace)) :
    LogicalValueOut F isem cop ty u v st after out aliases ρ := by
  obtain ⟨safeX,safeY,rx,ry,mx,my,outEq,stateEq⟩ := stock_logical_rrr_rhs_observed hp ctx tag width rhs
  obtain ⟨nx,rfl⟩ := inv.valueReg x rx mx
  obtain ⟨ny,rfl⟩ := inv.valueReg y ry my
  have needed : Demanded after x ∧ Demanded after y := by
    rw [stateEq]
    exact twice_marked st x y (extent x _ mx) (extent y _ my)
  have operands : ValuesHeld (fun z => z = x ∨ z = y) ctx fr (fun z => ρ (aliasNum aliases z)) := by
    apply held.mono
    intro z either
    rcases either with rfl | rfl
    · exact needed.1
    · exact needed.2
  obtain ⟨ρ',execution,value,kept⟩ := stock_alu_rrr_resolved refines operation.alu width bounded mx my operands sourceX sourceY
  refine ⟨.aluRRR op (szOf ty.width) (.vreg st.base.nextVreg .int) (.vreg nx .int) (.vreg ny .int),
    ρ',outEq,?_,execution,value,kept⟩
  exact congrArg State.base stateEq

private theorem immediate_case {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {k : Nat} {op : ALUOp} {cop : Clif.BinaryOp}
    (tag : ALUOp.ofIdx? k = some op) (operation : LogicPair op cop) {ty : Clif.Ty} (width : ty.width ≤ 64)
    (left : Bool) {x y m n : Nat} {u v : BitVec ty.width} {fr : Clif.Frame} (dfg : DFGCons ctx fr)
    (sourceX : fr.getAs x ty = .ok u) (sourceY : fr.getAs y ty = .ok v)
    {st after : State} {out : V} {tr trace : Array RuleId} {aliases : Array (Option Nat)} {ρ : Nat → CV}
    (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ x r, ctx.valueReg? x = some r → x < st.demand.size)
    (held : ValuesHeld (Demanded after) ctx fr (fun z => ρ (aliasNum aliases z)))
    {env : Isle.Interp.Env V} {middle : State × Array RuleId}
    (matched : (matchRule p (Stock.sem ctx) {} (m + 10) (if left then rule_inst_3923 else rule_inst_3920)
      [.data 59 k [],.ty (.int ty.width),.value x,.value y]).run (st,tr) = .ok (some env,middle))
    (rhs : (evalExpr p (Stock.sem ctx) {} (n + 40) (if left then rule_inst_3923 else rule_inst_3920).rhs env).run
      middle = .ok (some out,after,trace)) : LogicalValueOut F isem cop ty u v st after out aliases ρ := by
  have constant : fr.getAs (if left then x else y) ty = .ok (if left then u else v) := by
    cases left <;> assumption
  obtain ⟨imm,envEq,middleEq,immValue,valid⟩ := stock_logical_imm_match_receipts hp inv dfg left width constant matched
  rw [envEq,middleEq] at rhs
  obtain ⟨safe,rx,mapped,outEq,stateEq⟩ := stock_logical_imm_rhs_observed hp ctx left tag width (x := x) (y := y) rhs
  obtain ⟨nx,rfl⟩ := inv.valueReg (if left then y else x) rx mapped
  have needed : Demanded after (if left then y else x) := by
    rw [stateEq]
    exact marked st _ (extent _ _ mapped)
  have operands : ValuesHeld (fun z => z = (if left then y else x)) ctx fr (fun z => ρ (aliasNum aliases z)) := by
    apply held.mono
    intro z equal
    subst z
    exact needed
  have sourceOther : fr.getAs (if left then y else x) ty = .ok (if left then v else u) := by
    cases left <;> assumption
  have bits : (BitVec.ofNat (szOf ty.width).bits imm.value).setWidth ty.width = (if left then u else v) := by
    rw [immValue]
    exact setWidth_ofNat_toNat (szOf_bits width) _
  obtain ⟨ρ',execution,value,kept⟩ := stock_logical_imm_resolved refines operation width bounded mapped operands sourceOther valid bits
  have original : VHolds ⟨ty,Clif.Sem.binary cop u v⟩ (ρ' st.base.nextVreg) := by
    cases left
    · exact value
    · change VHolds ⟨ty,Clif.Sem.binary cop v u⟩ (ρ' st.base.nextVreg) at value
      rw [operation.comm] at value
      exact value
  refine ⟨.aluRRImmLogic op (szOf ty.width) (.vreg st.base.nextVreg .int) (.vreg nx .int) imm,
    ρ',outEq,?_,execution,original,kept⟩
  exact congrArg State.base stateEq

private theorem shift_case {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {k : Nat} {op : ALUOp} {cop : Clif.BinaryOp}
    (tag : ALUOp.ofIdx? k = some op) (operation : LogicPair op cop) {ty : Clif.Ty} (width : ty.width ≤ 64)
    (left : Bool) {x y m n : Nat} {u v : BitVec ty.width} {fr : Clif.Frame} (dfg : DFGCons ctx fr)
    (sourceX : fr.getAs x ty = .ok u) (sourceY : fr.getAs y ty = .ok v)
    {st after : State} {out : V} {tr trace : Array RuleId} {aliases : Array (Option Nat)} {ρ : Nat → CV}
    (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ x r, ctx.valueReg? x = some r → x < st.demand.size)
    (held : ValuesHeld (Demanded after) ctx fr (fun z => ρ (aliasNum aliases z)))
    {env : Isle.Interp.Env V} {middle : State × Array RuleId}
    (matched : (matchRule p (Stock.sem ctx) {} (m + 10) (if left then rule_inst_3931 else rule_inst_3928)
      [.data 59 k [],.ty (.int ty.width),.value x,.value y]).run (st,tr) = .ok (some env,middle))
    (rhs : (evalExpr p (Stock.sem ctx) {} (n + 40) (if left then rule_inst_3931 else rule_inst_3928).rhs env).run
      middle = .ok (some out,after,trace)) : LogicalValueOut F isem cop ty u v st after out aliases ρ := by
  have shifted : fr.getAs (if left then x else y) ty = .ok (if left then u else v) := by
    cases left <;> assumption
  obtain ⟨z,kk,sh,uz,envEq,middleEq,sourceZ,lsl,amount,shiftValue⟩ :=
    stock_logical_shift_match_receipts hp inv dfg left width shifted matched
  rw [envEq,middleEq] at rhs
  obtain ⟨safe,safeZ,rx,rz,mapped,mappedZ,outEq,stateEq⟩ :=
    stock_logical_shift_rhs_observed hp ctx left tag width (x := x) (y := y) rhs
  obtain ⟨nx,rfl⟩ := inv.valueReg (if left then y else x) rx mapped
  obtain ⟨nz,rfl⟩ := inv.valueReg z rz mappedZ
  have needed : Demanded after (if left then y else x) ∧ Demanded after z := by
    rw [stateEq]
    exact twice_marked st _ z (extent _ _ mapped) (extent z _ mappedZ)
  have operands : ValuesHeld (fun q => q = (if left then y else x) ∨ q = z) ctx fr
      (fun q => ρ (aliasNum aliases q)) := by
    apply held.mono
    intro q either
    rcases either with rfl | rfl
    · exact needed.1
    · exact needed.2
  have sourceOther : fr.getAs (if left then y else x) ty = .ok (if left then v else u) := by
    cases left <;> assumption
  obtain ⟨ρ',execution,value,kept⟩ := stock_logical_shift_resolved refines operation width bounded
    mapped mappedZ operands sourceOther sourceZ lsl amount
  rw [← shiftValue] at value
  have original : VHolds ⟨ty,Clif.Sem.binary cop u v⟩ (ρ' st.base.nextVreg) := by
    cases left
    · exact value
    · change VHolds ⟨ty,Clif.Sem.binary cop v u⟩ (ρ' st.base.nextVreg) at value
      rw [operation.comm] at value
      exact value
  refine ⟨.aluRRRShift op (szOf ty.width) (.vreg st.base.nextVreg .int) (.vreg nx .int) (.vreg nz .int) sh,
    ρ',outEq,?_,execution,original,kept⟩
  exact congrArg State.base stateEq

private theorem register_match {p : Program} (hp : Data p) (ctx : Ctx)
    (k w x y : Nat) (st : State) (tr : Array RuleId) (m : Nat) :
    (matchRule p (Stock.sem ctx) {} (m + 2) rule_inst_3916
      [.data 59 k [],.ty (.int w),.value x,.value y]).run (st,tr) =
      .ok (some (env4 (.data 59 k []) (.ty (.int w)) (.value x) (.value y)),st,tr) := by
  cases hp
  isel_eval [rule_inst_3916]

/-- Every actual successful logical helper case computes the original binary
value through mapped/final-alias operands and writes only its fresh destination.
Demanded held values are taken in the baseline restricted source frame. -/
theorem stock_logical_helper_values {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {k : Nat} {op : ALUOp} {cop : Clif.BinaryOp}
    (tag : ALUOp.ofIdx? k = some op) (operation : LogicPair op cop) {ty : Clif.Ty} (width : ty.width ≤ 64)
    {x y n : Nat} {u v : BitVec ty.width} {fr : Clif.Frame} (dfg : DFGCons ctx fr)
    (sourceX : fr.getAs x ty = .ok u) (sourceY : fr.getAs y ty = .ok v)
    {st after : State} {out : V} {tr trace : Array RuleId} {aliases : Array (Option Nat)} {ρ : Nat → CV}
    (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ x r, ctx.valueReg? x = some r → x < st.demand.size)
    (held : ValuesHeld (Demanded after) ctx fr (fun z => ρ (aliasNum aliases z)))
    (helper : (applyTerm p (Stock.sem ctx) {} (n + 60) 27 565
      [.data 59 k [],.ty (.int ty.width),.value x,.value y]).run (st,tr) = .ok (some out,after,trace)) :
    LogicalValueOut F isem cop ty u v st after out aliases ρ := by
  obtain ⟨r,member,m,env,middle,final,finalTrace,fuel,matched,rhs,stateTrace⟩ :=
    applyTerm_internal_some (p := p) (sem := Stock.sem ctx) (cfg := {}) rfl hp.t565 term_565_kind rfl helper
  simp only [Prod.mk.injEq] at stateTrace
  obtain ⟨rfl,_⟩ := stateTrace
  rw [hp.r565] at member fuel
  simp only [List.length_cons,List.length_nil] at fuel
  obtain ⟨m',rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10,by omega⟩
  have evaluated : (evalExpr p (Stock.sem ctx) {} ((n + 19) + 40) r.rhs env).run middle =
      .ok (some out,after,finalTrace) := rhs
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact immediate_case hp inv refines tag operation width true dfg sourceX sourceY bounded extent held matched evaluated
  · exact shift_case hp inv refines tag operation width true dfg sourceX sourceY bounded extent held matched evaluated
  · exact immediate_case hp inv refines tag operation width false dfg sourceX sourceY bounded extent held matched evaluated
  · exact shift_case hp inv refines tag operation width false dfg sourceX sourceY bounded extent held matched evaluated
  · rw [register_match hp ctx k ty.width x y st tr (m' + 8)] at matched
    simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at matched
    obtain ⟨rfl,rfl,rfl⟩ := matched
    exact register_case hp inv refines tag operation width sourceX sourceY bounded extent held evaluated

/-- Every selected helper form has a real sparse-ID execution with an original
DFG-consistent frame and held demanded inputs. Fused constants/shift results are
not required in the machine file; the actual selected rule ID is checked. -/
theorem stock_logical_helper_values_witness (form : LogicalForm) :
    ∃ (out : V) (after : State) (trace : Array RuleId),
      MappedCtxInv (formFunction form) (formBuilt form).1 ∧ DFGCons (formBuilt form).1 (formFrame form) ∧
      (applyTerm program (Stock.sem (formBuilt form).1) {} 60 27 565
        [.data 59 2 [],.ty (.int 64),.value (formX form),.value (formY form)]).run ((formBuilt form).2.2,#[]) =
          .ok (some out,after,trace) ∧ trace.back? = some (formRule form) ∧
      LogicalValueOut (fun _ => True) ispec .bor .i64 (BitVec.ofNat 64 (formValueX form))
        (BitVec.ofNat 64 (formValueY form)) (formBuilt form).2.2 after out #[] (formRegs form) := by
  have actual := formRun form
  cases run : (applyTerm program (Stock.sem (formBuilt form).1) {} 60 27 565
      [.data 59 2 [],.ty (.int 64),.value (formX form),.value (formY form)]).run ((formBuilt form).2.2,#[]) with
  | error err => simp [run,Except.toOption] at actual
  | ok result =>
    obtain ⟨value,after,trace⟩ := result
    cases value with
    | none => simp [run,Except.toOption] at actual
    | some out =>
      simp only [run,Except.toOption,Option.any_some,Option.isSome_some,Bool.true_and,Bool.and_eq_true,
        decide_eq_true_eq] at actual
      obtain ⟨demand,selected⟩ := actual
      have sourceX : (formFrame form).getAs (formX form) .i64 = .ok (BitVec.ofNat 64 (formValueX form)) := by
        cases form <;> rfl
      have sourceY : (formFrame form).getAs (formY form) .i64 = .ok (BitVec.ofNat 64 (formValueY form)) := by
        cases form <;> rfl
      have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
      have result := stock_logical_helper_values data_program (formInv form) self (k := 2) (op := .orr)
        rfl (Or.inr (Or.inl rfl)) (by decide) (formDFG form) sourceX sourceY (aliases := #[]) (ρ := formRegs form)
        (by simp) (formExtent form) (formHeld form demand) (n := 0) run
      exact ⟨out,after,trace,formInv form,formDFG form,rfl,selected,result⟩

end Backend.Stock.Proof.LogicalSemantics
