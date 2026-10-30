import FV.Backend.Proof.IselCtlRuleIds
import FV.Backend.Proof.StockRequestSuccess
import FV.Backend.Proof.StockPopcountSemantics
import FV.Backend.Proof.StockRootOpcodeMatch
namespace Backend.Stock.Proof.ScalarPopcount
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem sem_unData (ctx : Ctx) (t : Nat) (v : V) :
    (Stock.sem ctx).unData t v = (Backend.sem ctx).unData t v := rfl
private theorem sem_eq (ctx : Ctx) (a b : V) : (Stock.sem ctx).eq a b = (a == b) := rfl
private theorem sem_prim (ctx : Ctx) (name : String) :
    (Stock.sem ctx).prim 14 name = (CTy.ofName? name).map V.ty := rfl
section Data
attribute [local semireducible] Isle.Aarch64.program
private theorem popcount_source_data {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i x : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.unary .popcnt ty x)) :
    IW ty.width ∧ info.data = .data 152 29 [.data 151 111 [],.value x] ∧
      info.resTys.head? = some (.int ty.width) := by
  have accepted := inv.instE i info _ source clif
  have supported : eTy ty = true := by simpa [Compile.instE,Compile.unaryTyE,Compile.unaryE,Compile.tyE,eTy] using accepted
  have raw := inv.data i info _ source clif
  obtain ⟨types,result,typed,len⟩ := inv.resTys i info _ source clif
  simp only [Clif.Inst.resultTypes] at result
  cases result
  refine ⟨?_,?_,by rw [typed]; simp [ofClif_int_width (isInt_of_eTy supported)]⟩
  · cases ty <;> simp [eTy,Clif.Ty.width,IW] at supported ⊢
  · have expected : instData f (.unary .popcnt ty x) = .ok (.data 152 29 [.data 151 111 [],.value x]) := by
      simp [instData,unaryOpcode,supported] <;> rfl
    exact Except.ok.inj (raw.symm.trans expected)
end Data
theorem stock_popcount_match {p : Program} (hp : Data p) (ctx : Ctx)
    {i x w : Nat} {info : IInfo} (width : IW w) (source : ctx.insts[i]? = some info)
    (type : info.resTys.head? = some (.int w))
    (data : info.data = .data 152 29 [.data 151 111 [],.value x])
    (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+2) (popcountRule w) [.inst i]).run (st,tr) =
      .ok (some (popcountEnv w x),st,tr) := by
  have extraction := ext_inst_data_value ctx st.base source
  rw [data,type,Option.getD_some] at extraction
  cases hp
  rcases width with rfl | rfl | rfl | rfl
  all_goals simp only [popcountRule,popcountEnv,ite_false,ite_true,Nat.reduceEqDiff] at extraction ⊢
  all_goals isel_eval [*,rule_lower_2074,rule_lower_2080,rule_lower_2086,rule_lower_2092,
    sem_extract,sem_unData,sem_prim,sem_eq]
theorem stock_popcount_requests {p : Program} (hp : Data p) (ctx : Ctx)
    {w x n : Nat} (width : IW w)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+120) (popcountRule w).rhs (popcountEnv w x)).run (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st x ∧ ∃ rx,ctx.valueReg? x = some rx := by
  cases request : Stock.externCtor ctx T.put_in_reg [.value x] st with
  | fail =>
    have denied : (evalExpr p (Stock.sem ctx) {} (n+120) (popcountRule w).rhs (popcountEnv w x)).run (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      rcases width with rfl | rfl | rfl | rfl
      all_goals simp only [popcountRule,popcountEnv,ite_false,ite_true,
        Nat.reduceEqDiff,false_or,or_false,true_or,or_true]
      all_goals isel_eval [*,popcountRule,popcountEnv,rule_lower_2074,rule_lower_2080,rule_lower_2086,rule_lower_2092,
        sem_ctor,sem_extract,sem_unData,sem_eq,sem_prim]
      all_goals intro impossible; cases impossible
    exact False.elim (denied run)
  | unmodeled err =>
    have denied : (evalExpr p (Stock.sem ctx) {} (n+120) (popcountRule w).rhs (popcountEnv w x)).run (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      rcases width with rfl | rfl | rfl | rfl
      all_goals simp only [popcountRule,popcountEnv,ite_false,ite_true,
        Nat.reduceEqDiff,false_or,or_false,true_or,or_true]
      all_goals isel_eval [*,popcountRule,popcountEnv,rule_lower_2074,rule_lower_2080,rule_lower_2086,rule_lower_2092,
        sem_ctor,sem_extract,sem_unData,sem_eq,sem_prim]
      all_goals intro impossible; cases impossible
    exact False.elim (denied run)
  | ok pair =>
    obtain ⟨v,q⟩ := pair
    obtain ⟨safe,rx,mapped,_,_⟩ := (stock_put_in_reg_iff ctx st x v q).mp request
    exact ⟨safe,rx,mapped⟩
/-- Selected popcount execution derives guarded mapping and computes original values. -/
theorem stock_popcount_selected_values {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i x : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.unary .popcnt ty x))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {u : BitVec ty.width} (get : fr.getAs x ty = .ok u)
    {st next : State} {out : V} {rules : List RuleId} (selected : LowerSelection ctx i st out next rules)
    (chosen : selected.rule = popcountRule ty.width) {aliases : Array (Option Nat)} {ρ : Nat → CV}
    (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ x r,ctx.valueReg? x = some r → x < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun k => ρ (aliasNum aliases k))) :
    ∃ (nx : Nat) (ρ' : Nat → CV),ctx.valueReg? x = some (.vreg nx .int) ∧
      out = .regsVec [[.vreg (popcountResult ty.width st.base.nextVreg) .int]] ∧
      next = {st.mark x with base := popcountBase ty.width st.base (.vreg nx .int)} ∧
      PRun F isem ((popcountCode ty.width st.base.nextVreg nx).map (·.mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ ρ' ∧
      VHolds ⟨ty,u.cpop⟩ (ρ' (popcountResult ty.width st.base.nextVreg)) ∧
      ∀ n,n < st.base.nextVreg ∨ st.base.nextVreg+popcountAlloc ty.width ≤ n → ρ' n = ρ n := by
  obtain ⟨width,data,type⟩ := popcount_source_data inv source clif
  have enough := selected.fuelBound
  have count : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl
  obtain ⟨m,fuelEq⟩ : ∃ m,selected.matchFuel = m+2 := ⟨selected.matchFuel-2,by omega⟩
  have matched := selected.matchedRun
  rw [chosen,fuelEq,stock_popcount_match data_program ctx width source type data st #[] m] at matched
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at matched
  obtain ⟨envEq,stateEq,traceEq⟩ := matched
  have rhs := selected.rhsRun
  rw [chosen,← envEq,← stateEq,← traceEq] at rhs
  change (evalExpr program (Stock.sem ctx) {} (999879+120) (popcountRule ty.width).rhs
    (popcountEnv ty.width x)).run (st,#[]) = .ok (some out,next,selected.rhsTrace) at rhs
  obtain ⟨safe,rx,mapped⟩ := stock_popcount_requests data_program ctx width rhs
  obtain ⟨nx,rfl⟩ := inv.valueReg x rx mapped
  obtain ⟨trace,forward⟩ := stock_popcount_rhs data_program ctx width mapped st safe #[] 999879
  rw [forward] at rhs
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at rhs
  obtain ⟨outEq,nextEq,traceEq⟩ := rhs
  have input := held.read (by
    rw [← nextEq,Demanded]
    change (st.mark x).demand[x]! ≠ 0
    rw [(mark_demand st x (extent x _ mapped)).1]; omega) (getAs_ok get) mapped
  obtain ⟨ρ',execution,value,kept⟩ := stock_popcount_resolved refines width bounded input
  exact ⟨nx,ρ',mapped,outEq.symm,nextEq.symm,execution,value,kept⟩
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
private theorem inventory : sourceOpcodeIds 111 = [937,938,939,940] := by decide +kernel
/-- Actual original opcode/type matching derives the selected popcount root. -/
theorem stock_selected_popcount_rule {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i x : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.unary .popcnt ty x))
    {st next : State} {out : V} {trace : List RuleId}
    (selected : LowerSelection ctx i st out next trace) : selected.rule = popcountRule ty.width := by
  obtain ⟨width,data,type⟩ := popcount_source_data inv source clif
  have member := stock_selected_source_opcode_ids inv source clif data selected
  rw [inventory] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  have roots : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl
  have enough := selected.fuelBound
  obtain ⟨fuel,fuelEq⟩ : ∃ fuel,selected.matchFuel = fuel+1 := ⟨selected.matchFuel-1,by omega⟩
  have matched := selected.matchedRun
  rw [fuelEq] at matched
  obtain ⟨bound,args,_⟩ := matchRule_some_inv matched
  rw [stock_matchArgs] at args
  rcases member with h8 | h16 | h32 | h64
  · have candidate : rule_lower_2074 ∈ program.rulesOf T.lower.id := by
      rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
    have chosen : selected.rule = rule_lower_2074 := eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate h8
    rw [chosen] at args
    have actualWidth := type_match (target := 8) (name := "I8") rfl rfl source type args
    rw [chosen,actualWidth]
    rfl
  · have candidate : rule_lower_2080 ∈ program.rulesOf T.lower.id := by
      rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
    have chosen : selected.rule = rule_lower_2080 := eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate h16
    rw [chosen] at args
    have actualWidth := type_match (target := 16) (name := "I16") rfl rfl source type args
    rw [chosen,actualWidth]
    rfl
  · have candidate : rule_lower_2086 ∈ program.rulesOf T.lower.id := by
      rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
    have chosen : selected.rule = rule_lower_2086 := eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate h32
    rw [chosen] at args
    have actualWidth := type_match (target := 32) (name := "I32") rfl rfl source type args
    rw [chosen,actualWidth]
    rfl
  · have candidate : rule_lower_2092 ∈ program.rulesOf T.lower.id := by
      rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
    have chosen : selected.rule = rule_lower_2092 := eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate h64
    rw [chosen] at args
    have actualWidth := type_match (target := 64) (name := "I64") rfl rfl source type args
    rw [chosen,actualWidth]
    rfl
end Backend.Stock.Proof.ScalarPopcount
