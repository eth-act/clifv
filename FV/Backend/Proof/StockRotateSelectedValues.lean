import FV.Backend.Proof.StockSelectionReceipts
import FV.Backend.Proof.StockExtendRequests
import FV.Backend.Proof.StockRotateImmediateMatch
namespace Backend.Stock.Proof.ScalarRotate
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem type_match {ctx : Ctx} {r : Rule} {name : String} {target i w : Nat} {q : Pattern}
    (args : r.args = [.term 18 209 [.constPrim 14 name,q]])
    (primitive : (Backend.sem ctx).prim 14 name = some (.ty (.int target)))
    {info : IInfo} (source : ctx.insts[i]? = some info) (type : info.resTys.head? = some (.int w))
    {st : LState} {env env' : Isle.Interp.Env V}
    (matched : matchArgs program (Backend.sem ctx) st r.args [.inst i] env = .ok (some env')) : w = target := by
  rw [args] at matched
  obtain ⟨first,head,_⟩ := matchArgs_cons_inv matched
  obtain ⟨fields,extracted,patterns⟩ := matchPat_extract_inv data_program.t209 term_209_kind rfl head
  rw [Backend.Proof.sem_extract] at extracted
  have expected := ext_inst_data_value ctx st source
  rw [type,Option.getD_some] at expected
  rw [expected] at extracted
  cases extracted
  obtain ⟨middle,typeMatch,_⟩ := matchArgs_cons_inv patterns
  have eq : ∀ a b,(Backend.sem ctx).eq a b = (a == b) := fun _ _ => rfl
  simp only [matchPat.eq_5,primitive,eq] at typeMatch
  split at typeMatch
  · rename_i same
    have types := beq_iff_eq.mp same
    exact CTy.int.inj (V.ty.inj types)
  · cases typeMatch
private theorem wide_match_width {ctx : Ctx} {left wide : Bool} {i w : Nat} {info : IInfo}
    (source : ctx.insts[i]? = some info) (type : info.resTys.head? = some (.int w))
    {st : LState} {env env' : Isle.Interp.Env V}
    (matched : matchArgs program (Backend.sem ctx) st (rotateWideImmRule left wide).args [.inst i] env = .ok (some env')) :
    w = rotateWidth wide := by
  cases left <;> cases wide
  · exact type_match (name := "I32") (target := 32) rfl rfl source type matched
  · exact type_match (name := "I64") (target := 64) rfl rfl source type matched
  · exact type_match (name := "I32") (target := 32) rfl rfl source type matched
  · exact type_match (name := "I64") (target := 64) rfl rfl source type matched
private theorem wide_imm_value {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) (left : Bool) {ty : Clif.Ty} (width : ty.width = 32 ∨ ty.width = 64)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} {d x amount : Nat}
    (bounded : aliases.size ≤ d) (count : amount < ty.width)
    {u : BitVec ty.width} (held : VHolds ⟨ty,u⟩ (ρ (aliasNum aliases x))) :
    ∃ ρ',PRun F isem
      [(MInst.aluRRImmShift .extr (szOf ty.width) (.vreg d .int) (.vreg x .int)
        (rotateImmediate left ty.width amount)).mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size+1))] ρ ρ' ∧
      VHolds ⟨ty,rotateWideBits left u amount⟩ (ρ' d) ∧ ∀ z,z ≠ d → ρ' z = ρ z := by
  rcases width with small | large
  · rcases (show ty = .i32 ∨ ty = .f32 by revert small; cases ty <;> simp [Clif.Ty.width])
      with rfl | rfl <;>
    simpa only [Clif.Ty.width,szOf,Nat.reduceLeDiff,ite_true,VHolds,OperandSize.bits] using
      stock_rotate_wide_imm_resolved refines left .size32 count bounded held
  · rcases (show ty = .i64 ∨ ty = .f64 by revert large; cases ty <;> simp [Clif.Ty.width])
      with rfl | rfl <;>
    simpa only [Clif.Ty.width,szOf,Nat.reduceLeDiff,ite_false,VHolds,OperandSize.bits] using
      stock_rotate_wide_imm_resolved refines left .size64 count bounded held
/-- Actual selected wide immediate rotations derive width, original constant
count, source request and full output state internally, then compute the
original value through final aliases with fresh-write preservation. -/
theorem stock_rotate_selected_wide_immediate_values {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) (left wide : Bool) {i x y : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.binary (rotateOp left) ty x y))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {u : BitVec ty.width} (getX : fr.getAs x ty = .ok u)
    {amount : Clif.Val} (getY : fr.regs y = some amount)
    {st next : State} {out : V} {rules : List RuleId} (selected : LowerSelection ctx i st out next rules)
    (chosen : selected.rule = rotateWideImmRule left wide) {aliases : Array (Option Nat)} {ρ : Nat → CV}
    (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ v r,ctx.valueReg? v = some r → v < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun k => ρ (aliasNum aliases k))) :
    ∃ (nx count : Nat) (ρ' : Nat → CV),ty.width = rotateWidth wide ∧
      ctx.valueReg? x = some (.vreg nx .int) ∧ count = amount.bits.toNat % ty.width ∧ count < ty.width ∧
      out = .regsVec [[.vreg st.base.nextVreg .int]] ∧
      next = {st.mark x with base := ((st.base.fresh .int).2.emit
        (.aluRRImmShift .extr (szOf ty.width) (st.base.fresh .int).1 (.vreg nx .int)
          (rotateImmediate left ty.width count)))} ∧
      PRun F isem [(MInst.aluRRImmShift .extr (szOf ty.width) (.vreg st.base.nextVreg .int)
        (.vreg nx .int) (rotateImmediate left ty.width count)).mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size+1))] ρ ρ' ∧
      VHolds ⟨ty,rotateWideBits left u amount.bits.toNat⟩ (ρ' st.base.nextVreg) ∧
      ∀ z,z ≠ st.base.nextVreg → ρ' z = ρ z := by
  obtain ⟨width,data,type⟩ := stock_rotate_source_data inv left source clif
  have enough := selected.fuelBound
  have roots : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl
  obtain ⟨m,fuelEq⟩ : ∃ m,selected.matchFuel = m+20 := ⟨selected.matchFuel-20,by omega⟩
  have matched := selected.matchedRun
  rw [chosen,fuelEq] at matched
  obtain ⟨initial,args,_⟩ := matchRule_some_inv matched
  rw [stock_matchArgs] at args
  have physical := wide_match_width source type args
  have supported : ty.width = 32 ∨ ty.width = 64 := by
    cases wide
    · exact .inl physical
    · exact .inr physical
  have narrow : ¬ (ty.width = 8 ∨ ty.width = 16) := by rcases supported with h | h <;> omega
  have rootEq : rotateRule left true ty.width = rotateWideImmRule left wide := by
    simp only [rotateRule,narrow,ite_false,ite_true]
    cases wide <;> simp [physical,rotateWidth]
  rw [← rootEq] at matched
  obtain ⟨j,literal,constantTy,bits,c,count,defined,found,original,value,envEq,middleEq,countEq,countBound⟩ :=
    stock_rotate_immediate_receipts data_program inv left dfg width source type data getY matched
  have rhs := selected.rhsRun
  rw [chosen,envEq] at rhs
  rw [middleEq] at rhs
  simp only [rotateImmediateEnv,narrow,ite_false] at rhs
  change (evalExpr program (Stock.sem ctx) {} (999949+50) (rotateWideImmRule left wide).rhs
    (env3 (.value x) (.int c) (.op (.immShift count)))).run (st,#[]) = .ok (some out,next,selected.rhsTrace) at rhs
  obtain ⟨safe,rx,mapped⟩ := stock_rotate_wide_immediate_requests data_program ctx left wide rhs
  obtain ⟨nx,rfl⟩ := inv.valueReg x rx mapped
  obtain ⟨trace,forward⟩ := stock_rotate_wide_imm_rhs data_program ctx left wide mapped
    (by rw [← physical]; exact countBound) c st safe #[] 999949
  rw [forward] at rhs
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at rhs
  obtain ⟨outEq,nextEq,_⟩ := rhs
  have input := held.read (by
      rw [← nextEq,Demanded]
      change (st.mark x).demand[x]! ≠ 0
      rw [(mark_demand st x (extent x _ mapped)).1]; omega) (getAs_ok getX) mapped
  obtain ⟨ρ',execution,result,kept⟩ := wide_imm_value refines left supported bounded countBound input
  refine ⟨nx,count,ρ',physical,mapped,countEq,countBound,?_,?_,execution,?_,kept⟩
  · simpa only [LState.fresh] using outEq.symm
  · rw [physical]; exact nextEq.symm
  · simpa only [countEq,rotateWideBits,Nat.mod_mod] using result
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem negate_raw (ctx : Ctx) (st : State) (w amount : Nat) :
    Stock.externCtor ctx T.negate_imm_shift [.ty (.int w),.op (.immShift amount)] st =
      .ok (.op (.immShift (Nat.land ((w+256-amount)%256) (w-1))),st) := by
  rw [stock_ctor_baseOnly ctx T.negate_imm_shift _ st (by decide)]
  rfl
/-- Successful narrow immediate execution derives source type and guarded
mapping through its actual extension call and original frame consistency. -/
theorem stock_rotate_narrow_immediate_requests {p : Program} (hp : Data p) (ctx : Ctx) (left : Bool)
    {w x amount n : Nat} (width : w = 8 ∨ w = 16) {constant : Int}
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {ty : Clif.Ty} (same : ty.width = w)
    {u : BitVec ty.width} (getX : fr.getAs x ty = .ok u)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+140) (rotateNarrowRule left true).rhs
      (env4 (.ty (.int w)) (.value x) (.int constant) (.op (.immShift amount)))).run (st,tr) = .ok (some out,next,trace)) :
    ctx.valueType? x = some (.int w) ∧ DemandAllowed ctx st x ∧ ∃ rx,ctx.valueReg? x = some rx := by
  have hp' := hp
  have negate := fun q => negate_raw ctx q w amount
  cases hp
  cases left
  all_goals
    isel_inv [*,rotateNarrowRule,rule_lower_1778,rule_lower_1852,sem_ctor] at run
    all_goals isel_destruct <;> subst_vars
    have shape := ScalarShift.stock_zext32_out hp' (ctx := ctx) (cfg := {}) (n := n+133) rfl (by omega)
      (show ApplyInternal p (Stock.sem ctx) {} (n+133) 27 556 [.value x] (st,tr) _ _ from by assumption)
    obtain ⟨t,typed,safe,rx,mapped,form⟩ := shape
    have typeEq : t = .int ty.width := by
      have h := (dfg.2 x t ⟨ty,u⟩ typed (getAs_ok getX)).symm
      exact h.trans (ofClif_int_width (ty := ty) (isInt_of_width_lt_32 (by omega)))
    rw [typeEq] at typed
    exact ⟨typed,safe,rx,mapped⟩
end Backend.Stock.Proof.ScalarRotate
