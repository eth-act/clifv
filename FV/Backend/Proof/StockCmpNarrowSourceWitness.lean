module

public import FV.Backend.Proof.StockCmpNarrowSourceValues

@[expose] public section

namespace Backend.Stock.Proof.ScalarCmp.NarrowSourceWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.ScalarCmp
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
private def ty (half : Bool) : Clif.Ty := if half then .i16 else .i8
private def cc (signed : Bool) : Clif.IntCC := if signed then .slt else .ult
private def function (signed half : Bool) : Clif.Function := {
  name := "stock_cmp_narrow_source_values"
  sig := {params := [⟨ty half,.none,.normal⟩,⟨ty half,.none,.normal⟩],returns := [⟨.i8,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,ty half),(31,ty half)],body := [⟨[100],.icmp (cc signed) (ty half) 7 31⟩],term := .ret [100]}] }
private def built (signed half : Bool) : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx (function signed half)).toOption.getD (sinkCtx,#[],sinkState)
private def frame (signed half : Bool) (a b : BitVec (ty half).width) : Clif.Frame := {
  func := function signed half
  regs := fun x => if x = 7 then some ⟨ty half,a⟩ else if x = 31 then some ⟨ty half,b⟩ else none
  slots := [],body := [⟨[100],.icmp (cc signed) (ty half) 7 31⟩],term := .ret [100] }
private def dirty {n : Nat} (a : BitVec n) : CV := BitVec.ofNat 128 (2^100+a.toNat)
private theorem dirty_low (half : Bool) (a : BitVec (ty half).width) :
    (dirty a).setWidth (ty half).width = a := by
  have small : (ty half).width ≤ 128 := by cases half <;> decide
  unfold dirty
  rw [BitVec.setWidth_ofNat_of_le small]
  apply BitVec.eq_of_toNat_eq
  have upper : 2^100 % 2^(ty half).width = 0 := by cases half <;> decide +kernel
  simp only [BitVec.toNat_ofNat,Nat.add_mod,upper,Nat.zero_add,Nat.mod_eq_of_lt a.isLt]
private def regs (signed half : Bool) (a b : BitVec (ty half).width) (key : Nat) : CV :=
  if key = 192 then dirty a else if key = 193 then dirty b else 0
/-- Real constructed source contexts at both narrow widths and signednesses
inhabit the actual RHS/715/source-value pipeline for arbitrary input words.
Dirty upper bits are retained; complete retained Stock.lower/source-step
witnesses remain a separate obligation. -/
theorem stock_cmp_narrow_source_values_witness (signed half : Bool) (a b : BitVec (ty half).width) :
    ∃ st middle next condition out emitTrace trace,
      (evalExpr program (Stock.sem (built signed half).1) {} 1000
        (if signedCC (cc signed) then rule_inst_5108 else rule_inst_5117).rhs
        #[some (.data 145 (ccIdx (cc signed)) []),some (.value 7),
          some (.ty (.int (if half then 16 else 8))),some (.value 31)]).run (st,#[]) =
        .ok (some condition,middle,emitTrace) ∧
      ApplyInternal program (Stock.sem (built signed half).1) {} 999 27 715 [condition]
        (middle,#[]) out (next,trace) ∧
      ∃ d,out = .reg (.vreg d .int) ∧
        ∀ world,Runs (fun _ => True) ispec ([MInst.extend (.vreg st.base.nextVreg .int) (.vreg 192 .int)
          (signedCC (cc signed)) (ty half).width 32,
          .aluRRRExtend .subS .size32 .xzr (.vreg st.base.nextVreg .int) (.vreg 193 .int)
            (if signedCC (cc signed) then (if half then ExtendOp.sxth else .sxtb) else (if half then ExtendOp.uxth else .uxtb)),
          .cset (.vreg d .int) (condOf (cc signed))].map
            (·.mapRegs (Backend.lowerFunction.resolve #[] 1))) (regs signed half a b) world (fun ρ' _ =>
              VHolds ⟨.i8,Clif.Sem.bool8 (Clif.Sem.intcc (cc signed) a b)⟩ (ρ' d) ∧
              ∀ k,k < st.base.nextVreg ∨ next.base.nextVreg ≤ k → ρ' k = regs signed half a b k) := by
  let ctx := (built signed half).1
  let st := (built signed half).2.2
  have scope : LowerScope (function signed half) := lowerScope_of (by cases signed <;> cases half <;> decide +kernel)
  have build : Stock.buildCtx (function signed half) = .ok (built signed half) := by
    cases signed <;> cases half <;> rfl
  have inv : MappedCtxInv (function signed half) ctx := buildCtx_mappedInv scope build
  have typeX : ctx.valueType? 7 = some (.int (if half then 16 else 8)) := by cases signed <;> cases half <;> rfl
  have mapX : ctx.valueReg? 7 = some (.vreg 192 .int) := by cases signed <;> cases half <;> rfl
  have mapY : ctx.valueReg? 31 = some (.vreg 193 .int) := by cases signed <;> cases half <;> rfl
  have absentX : ctx.defInst? 7 = none := by cases signed <;> cases half <;> rfl
  have safeX : DemandAllowed ctx st 7 := by intro i impossible; rw [absentX] at impossible; cases impossible
  have absentY : ctx.defInst? 31 = none := by cases signed <;> cases half <;> rfl
  have safeY : DemandAllowed ctx st 31 := by intro i impossible; rw [absentY] at impossible; cases impossible
  obtain ⟨emitTrace,emitter⟩ := stock_cmp_narrow_rhs data_program ctx (signedCC (cc signed)) half (cc signed)
    typeX mapX mapY st safeX safeY #[] 840
  let middle : State := {(st.mark 7).mark 31 with base := ((st.base.fresh .int).2.emit
    (.extend (st.base.fresh .int).1 (.vreg 192 .int) (signedCC (cc signed)) (if half then 16 else 8) 32))}
  let mi : V := .data 58 8 [.data 59 10 [],.data 93 0 [],.reg .xzr,.reg (st.base.fresh .int).1,
    .reg (.vreg 193 .int),.data 84 (if signedCC (cc signed) then (if half then 5 else 4) else (if half then 1 else 0)) []]
  let e := if signedCC (cc signed) then (if half then ExtendOp.sxth else .sxtb) else (if half then ExtendOp.uxth else .uxtb)
  have decoded : MInst.ofV mi = some (.aluRRRExtend .subS .size32 .xzr (st.base.fresh .int).1 (.vreg 193 .int) e) := by
    cases signed <;> cases half <;> rfl
  obtain ⟨trace,call⟩ := stock_cmp_condition_flags data_program ctx (cfg := {}) rfl middle #[] 880 decoded (condOf (cc signed))
  have enough : (119:Nat) ≤ 999 := by decide
  have extent : ∀ z r,ctx.valueReg? z = some r → z < st.demand.size := by
    intro z r mapped
    have bound : ctx.valReg.size ≤ st.demand.size := by cases signed <;> cases half <;> decide +kernel
    have index : z < ctx.valReg.size := by
      by_cases inside : z < ctx.valReg.size
      · exact inside
      · have absent := Array.getElem?_eq_none (show ctx.valReg.size ≤ z by omega)
        unfold Ctx.valueReg? at mapped
        rw [absent] at mapped
        cases mapped
    omega
  have held : ∀ next,ValuesHeld (Demanded next) ctx (frame signed half a b)
      (fun key => regs signed half a b (aliasNum #[] key)) := by
    intro next z needed val lookup
    by_cases seven : z = 7
    · subst z
      change some ⟨ty half,a⟩ = some val at lookup
      cases lookup
      refine ⟨192,mapX,?_⟩
      change (regs signed half a b 192).setWidth (ty half).width = a
      exact dirty_low half a
    · by_cases thirtyone : z = 31
      · subst z
        change some ⟨ty half,b⟩ = some val at lookup
        cases lookup
        refine ⟨193,mapY,?_⟩
        change (regs signed half a b 193).setWidth (ty half).width = b
        exact dirty_low half b
      · simp [frame,seven,thirtyone] at lookup
  have separated : ∀ r,ctx.valueReg? 31 = some (.vreg r .int) → aliasNum #[] r ≠ st.base.nextVreg := by
    intro r mapped
    rw [mapY] at mapped
    cases mapped
    cases signed <;> cases half <;> decide +kernel
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  obtain ⟨nx,ny,d,mx,my,output,lower,upper,fragment,execution⟩ := stock_cmp_narrow_condition_source_values
    data_program inv half (cc signed) rfl (fr := frame signed half a b) (u := a) (v := b) (by cases half <;> rfl) (by cases half <;> rfl) typeX enough emitter call self
    (aliases := #[]) (by simp) extent (held _) separated
  rw [mapX] at mx
  rw [mapY] at my
  cases mx
  cases my
  exact ⟨st,middle,_,_,_,emitTrace,trace,emitter,call,d,output,execution⟩
end Backend.Stock.Proof.ScalarCmp.NarrowSourceWitness
