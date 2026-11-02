import FV.Backend.Proof.IselCtlRuleIds
import FV.Backend.Proof.StockSelectionReceipts
import FV.Backend.Proof.IselFamAluBBitrev
import FV.Backend.Proof.StockBitrevRhs
import FV.Backend.Proof.StockBitrevSemantics
namespace Backend.Stock.Proof.ScalarBit
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
section Data
attribute [local semireducible] Isle.Aarch64.program
private theorem source_data {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i x : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.unary .bitrev ty x)) :
    IW ty.width ∧ info.data = .data 152 29 [.data 151 106 [],.value x] ∧
      info.resTys.head? = some (.int ty.width) := by
  have accepted := inv.instE i info _ source clif
  have supported : eTy ty = true := by simpa [Compile.instE,Compile.unaryTyE,Compile.unaryE,Compile.tyE,eTy] using accepted
  have raw := inv.data i info _ source clif
  obtain ⟨types,result,typed,len⟩ := inv.resTys i info _ source clif
  simp only [Clif.Inst.resultTypes] at result
  cases result
  refine ⟨?_,?_,by rw [typed]; simp [ofClif_int_width (isInt_of_eTy supported)]⟩
  · cases ty <;> simp [eTy,Clif.Ty.width,IW] at supported ⊢
  · have expected : instData f (.unary .bitrev ty x) = .ok (.data 152 29 [.data 151 106 [],.value x]) := by
      simp only [instData,unaryOpcode,supported,ite_true]; rfl
    exact Except.ok.inj (raw.symm.trans expected)
end Data
private def rootEnv (w x : Nat) : Isle.Interp.Env V :=
  if w = 8 ∨ w = 16 then env1 (.value x) else env2 (.ty (.int w)) (.value x)
private theorem root_match {ctx : Ctx} {i x w : Nat} {info : IInfo}
    (width : IW w) (source : ctx.insts[i]? = some info)
    (type : info.resTys.head? = some (.int w)) (data : info.data = .data 152 29 [.data 151 106 [],.value x])
    (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule program (Stock.sem ctx) {} (n+2) (bitrevRule w) [.inst i]).run (st,tr) =
      .ok (some (rootEnv w x),st,tr) := by
  rcases width with rfl | rfl | rfl | rfl
  · simpa [bitrevRule,rootEnv,bitrevNarrowRule] using stock_bitrev_narrow_match data_program ctx false source type data st tr n
  · simpa [bitrevRule,rootEnv,bitrevNarrowRule] using stock_bitrev_narrow_match data_program ctx true source type data st tr n
  · simpa [bitrevRule,rootEnv] using stock_bitrev_wide_match data_program ctx source type data st tr n
  · simpa [bitrevRule,rootEnv] using stock_bitrev_wide_match data_program ctx source type data st tr n
private theorem root_rhs {ctx : Ctx} {w x : Nat} (width : IW w) {rx : Reg}
    (mapped : ctx.valueReg? x = some rx) (st : State) (safe : DemandAllowed ctx st x)
    (tr : Array RuleId) (n : Nat) :
    ∃ trace,(evalExpr program (Stock.sem ctx) {} (n+40) (bitrevRule w).rhs (rootEnv w x)).run (st,tr) =
      .ok (some (.regsVec [[.vreg (bitrevResult w st.base.nextVreg) .int]]),
        {st.mark x with base := bitrevBase w st.base rx},trace) := by
  rcases width with rfl | rfl | rfl | rfl
  · simpa [bitrevRule,rootEnv,bitrevNarrowRule,bitrevNarrowShift,bitrevResult,bitrevBase] using stock_bitrev_narrow_rhs data_program ctx false mapped st safe tr n
  · simpa [bitrevRule,rootEnv,bitrevNarrowRule,bitrevNarrowShift,bitrevResult,bitrevBase] using stock_bitrev_narrow_rhs data_program ctx true mapped st safe tr n
  · simpa [bitrevRule,rootEnv,bitrevResult,bitrevBase,LState.fresh] using stock_bitrev_wide_rhs data_program ctx (w := 32) (by decide) mapped st safe tr n
  · simpa [bitrevRule,rootEnv,bitrevResult,bitrevBase,LState.fresh] using stock_bitrev_wide_rhs data_program ctx (w := 64) (by decide) mapped st safe tr n
private theorem root_requests {ctx : Ctx} {w x n : Nat} (width : IW w)
    {st next : State} {out : V} {trace : Array RuleId}
    (run : (evalExpr program (Stock.sem ctx) {} (n+40) (bitrevRule w).rhs (rootEnv w x)).run (st,#[]) = .ok (some out,next,trace)) :
    DemandAllowed ctx st x ∧ ∃ rx,ctx.valueReg? x = some rx := by
  rcases width with rfl | rfl | rfl | rfl
  · simp only [bitrevRule,rootEnv,Nat.reduceEqDiff,ite_true,or_true] at run
    exact stock_bitrev_narrow_rhs_requests data_program ctx false run
  · simp only [bitrevRule,rootEnv,Nat.reduceEqDiff,ite_true,ite_false,or_true] at run
    exact stock_bitrev_narrow_rhs_requests data_program ctx true run
  · simp only [bitrevRule,rootEnv,Nat.reduceEqDiff,ite_true,ite_false,false_or] at run
    exact stock_bitrev_wide_rhs_requests data_program ctx run
  · simp only [bitrevRule,rootEnv,Nat.reduceEqDiff,ite_true,ite_false,false_or] at run
    exact stock_bitrev_wide_rhs_requests data_program ctx run
/-- Actual scalar bit-reversal selections establish original values through
final aliases and preserve registers outside their one/two-register allocation. -/
theorem stock_bitrev_selected_values {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i x : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.unary .bitrev ty x))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {u : BitVec ty.width} (get : fr.getAs x ty = .ok u)
    {st next : State} {out : V} {rules : List RuleId} (selected : LowerSelection ctx i st out next rules)
    (chosen : selected.rule = bitrevRule ty.width) {aliases : Array (Option Nat)} {ρ : Nat → CV}
    (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ x r,ctx.valueReg? x = some r → x < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun k => ρ (aliasNum aliases k))) :
    ∃ (nx : Nat) (ρ' : Nat → CV),ctx.valueReg? x = some (.vreg nx .int) ∧
      out = .regsVec [[.vreg (bitrevResult ty.width st.base.nextVreg) .int]] ∧
      next = {st.mark x with base := bitrevBase ty.width st.base (.vreg nx .int)} ∧
      PRun F isem ((bitrevCode ty.width st.base.nextVreg nx).map (·.mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.unary .bitrev u⟩ (ρ' (bitrevResult ty.width st.base.nextVreg)) ∧
      ∀ n,n < st.base.nextVreg ∨ st.base.nextVreg+bitrevAlloc ty.width ≤ n → ρ' n = ρ n := by
  obtain ⟨width,data,type⟩ := source_data inv source clif
  have enough := selected.fuelBound
  have count : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl
  obtain ⟨m,fuelEq⟩ : ∃ m,selected.matchFuel = m+2 := ⟨selected.matchFuel-2,by omega⟩
  have matched := selected.matchedRun
  rw [chosen,fuelEq,root_match width source type data st #[] m] at matched
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at matched
  obtain ⟨envEq,stateEq,traceEq⟩ := matched
  have rhs := selected.rhsRun
  rw [chosen,← envEq,← stateEq,← traceEq] at rhs
  change (evalExpr program (Stock.sem ctx) {} (999959+40) (bitrevRule ty.width).rhs
    (rootEnv ty.width x)).run (st,#[]) = .ok (some out,next,selected.rhsTrace) at rhs
  obtain ⟨safe,rx,mapped⟩ := root_requests width rhs
  obtain ⟨nx,rfl⟩ := inv.valueReg x rx mapped
  obtain ⟨trace,forward⟩ := root_rhs width mapped st safe #[] 999959
  rw [forward] at rhs
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at rhs
  obtain ⟨outEq,nextEq,traceEq⟩ := rhs
  have inputHeld : ValuesHeld (fun z => z = x) ctx fr (fun k => ρ (aliasNum aliases k)) := by
    apply held.mono
    intro z same; subst z
    rw [← nextEq,Demanded]
    change (st.mark x).demand[x]! ≠ 0
    rw [(mark_demand st x (extent x _ mapped)).1]
    omega
  obtain ⟨ρ',execution,value,kept⟩ := stock_bitrev_resolved refines width bounded mapped inputHeld get
  exact ⟨nx,ρ',mapped,outEq.symm,nextEq.symm,execution,value,kept⟩
/-- Actual first-match selection excludes both narrow widths for the wide fallback. -/
theorem stock_bitrev_fallback_width {ctx : Ctx} {i x w : Nat} {info : IInfo}
    (source : ctx.insts[i]? = some info) (type : info.resTys.head? = some (.int w))
    (data : info.data = .data 152 29 [.data 151 106 [],.value x])
    {st next : State} {out : V} {rules : List RuleId} (selected : LowerSelection ctx i st out next rules)
    (chosen : selected.rule = rule_lower_1946) : w ≠ 8 ∧ w ≠ 16 := by
  have atPre : ((program.rulesOf T.lower.id).map Rule.id)[selected.pre.length]? = some rule_lower_1946.id := by
    rw [selected.candidates,chosen,List.map_append,List.map_cons,List.getElem?_append_right (by simp)]
    simp
  have at441 : ((program.rulesOf T.lower.id).map Rule.id)[441]? = some rule_lower_1946.id := by
    rw [show T.lower.id = TId.lower from rfl,List.getElem?_map,lower_idx_1946 data_program]
    rfl
  have preBound : selected.pre.length < ((program.rulesOf T.lower.id).map Rule.id).length := by
    rw [selected.candidates,List.length_map,List.length_append,List.length_cons]
    omega
  have lengthEq : selected.pre.length = 441 := lower_ids_nodup.eq_of_getElem?_eq preBound (atPre.trans at441.symm)
  have count : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl
  have candidates : program.rulesOf TId.lower = selected.pre ++ selected.rule :: selected.post := selected.candidates
  constructor
  · intro eight
    have first := lower_idx_1931 data_program
    rw [candidates,List.getElem?_append_left (by omega)] at first
    obtain ⟨fuel,bound,after,rejected⟩ := selected.rejected _ (List.mem_of_getElem? first)
    obtain ⟨n,fuelEq⟩ : ∃ n,fuel = n+2 := ⟨fuel-2,by omega⟩
    rw [eight] at type
    have matched := stock_bitrev_narrow_match data_program ctx false source type data st #[] n
    simp only [bitrevNarrowRule,Bool.false_eq_true,ite_false,ite_true] at matched
    rw [fuelEq,matched] at rejected
    cases rejected
  · intro sixteen
    have first := lower_idx_1937 data_program
    rw [candidates,List.getElem?_append_left (by omega)] at first
    obtain ⟨fuel,bound,after,rejected⟩ := selected.rejected _ (List.mem_of_getElem? first)
    obtain ⟨n,fuelEq⟩ : ∃ n,fuel = n+2 := ⟨fuel-2,by omega⟩
    rw [sixteen] at type
    have matched := stock_bitrev_narrow_match data_program ctx true source type data st #[] n
    simp only [bitrevNarrowRule,Bool.false_eq_true,ite_false,ite_true] at matched
    rw [fuelEq,matched] at rejected
    cases rejected
end Backend.Stock.Proof.ScalarBit
