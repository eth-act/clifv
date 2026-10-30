import FV.Backend.Proof.IselCtlRuleIds
import FV.Backend.Proof.IselFamAluBClz
import FV.Backend.Proof.StockCountSemantics
import FV.Backend.Proof.StockRootOpcodeMatch
namespace Backend.Stock.Proof.ScalarCount
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
section Data
attribute [local semireducible] Isle.Aarch64.program
private theorem count_source_data {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx) (trailing : Bool)
    {i x : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.unary (countOp trailing) ty x)) :
    IW ty.width ∧ info.data = .data 152 29 [.data 151 (countOpcode trailing) [],.value x] ∧
      info.resTys.head? = some (.int ty.width) := by
  have accepted := inv.instE i info _ source clif
  have supported : eTy ty = true := by cases trailing <;> simpa [countOp,Compile.instE,Compile.unaryTyE,Compile.unaryE,Compile.tyE,eTy] using accepted
  have raw := inv.data i info _ source clif
  obtain ⟨types,result,typed,len⟩ := inv.resTys i info _ source clif
  simp only [Clif.Inst.resultTypes] at result
  cases result
  refine ⟨?_,?_,by rw [typed]; simp [ofClif_int_width (isInt_of_eTy supported)]⟩
  · cases ty <;> simp [eTy,Clif.Ty.width,IW] at supported ⊢
  · have expected : instData f (.unary (countOp trailing) ty x) = .ok (.data 152 29 [.data 151 (countOpcode trailing) [],.value x]) := by
      cases trailing <;> simp [countOp,countOpcode,instData,unaryOpcode,supported] <;> rfl
    exact Except.ok.inj (raw.symm.trans expected)
end Data
def countBase (trailing : Bool) (w : Nat) (st : LState) (rx : Reg) : LState :=
  if w = 8 ∨ w = 16 then countNarrowBase trailing w st rx else countWideBase trailing w st rx
private theorem root_rhs {ctx : Ctx} (trailing : Bool) {w x : Nat} (width : IW w)
    (typed : ¬ trailing → w = 8 ∨ w = 16 → ctx.valueType? x = some (.int w))
    {rx : Reg} (mapped : ctx.valueReg? x = some rx) (st : State) (safe : DemandAllowed ctx st x)
    (tr : Array RuleId) (n : Nat) :
    ∃ trace,(evalExpr program (Stock.sem ctx) {} (n+80) (countRule trailing w).rhs (countEnv w x)).run (st,tr) =
      .ok (some (.regsVec [[.vreg (countResult trailing w st.base.nextVreg) .int]]),
        {st.mark x with base := countBase trailing w st.base rx},trace) := by
  by_cases narrow : w = 8 ∨ w = 16
  · cases trailing
    · simpa [countEnv,countResult,countAlloc,countBase,narrow,Nat.add_sub_assoc] using
        stock_clz_narrow_rhs data_program ctx narrow (typed (by decide) narrow) mapped st safe tr n
    · simpa [countEnv,countResult,countAlloc,countBase,narrow,Nat.add_sub_assoc,Nat.add_assoc] using
        stock_ctz_narrow_rhs data_program ctx narrow mapped st safe tr (n+40)
  · have wide : w = 32 ∨ w = 64 := by rcases width with h | h | h | h <;> simp_all
    cases trailing
    · simpa [countResult,countAlloc,countBase,narrow,Nat.add_sub_assoc,Nat.add_assoc] using
        stock_count_wide_rhs data_program ctx false wide mapped st safe tr (n+40)
    · simpa [countResult,countAlloc,countBase,narrow,Nat.add_sub_assoc,Nat.add_assoc] using
        stock_count_wide_rhs data_program ctx true wide mapped st safe tr (n+40)
private theorem root_requests {ctx : Ctx} (trailing : Bool) {w x n : Nat} (width : IW w)
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {ty : Clif.Ty} (same : ty.width = w)
    {u : BitVec ty.width} (get : fr.getAs x ty = .ok u)
    {st next : State} {out : V} {trace : Array RuleId}
    (run : (evalExpr program (Stock.sem ctx) {} (n+80) (countRule trailing w).rhs (countEnv w x)).run (st,#[]) = .ok (some out,next,trace)) :
    DemandAllowed ctx st x ∧ (∃ rx,ctx.valueReg? x = some rx) ∧
      (¬ trailing → w = 8 ∨ w = 16 → ctx.valueType? x = some (.int w)) := by
  by_cases narrow : w = 8 ∨ w = 16
  · simp only [countEnv,narrow,ite_true] at run
    cases trailing
    · obtain ⟨t,typed⟩ := stock_count_clz_narrow_type data_program ctx narrow run
      have eq : t = .int w := by
        have h := (dfg.2 x t ⟨ty,u⟩ typed (getAs_ok get)).symm
        exact h.trans (by simpa only [same] using
          ofClif_int_width (ty := ty) (isInt_of_width_lt_32 (by omega)))
      rw [eq] at typed
      obtain ⟨safe,mapped⟩ := stock_count_clz_narrow_requests data_program ctx narrow typed run
      exact ⟨safe,mapped,fun _ _ => typed⟩
    · have run40 : (evalExpr program (Stock.sem ctx) {} ((n+40)+40) (countRule true w).rhs (env1 (.value x))).run (st,#[]) = .ok (some out,next,trace) := by simpa only [Nat.add_assoc] using run
      obtain ⟨safe,mapped⟩ := stock_count_ctz_narrow_requests data_program ctx narrow run40
      exact ⟨safe,mapped,by simp⟩
  · have wide : w = 32 ∨ w = 64 := by rcases width with h | h | h | h <;> simp_all
    have run40 : (evalExpr program (Stock.sem ctx) {} ((n+40)+40) (countRule trailing w).rhs (countEnv w x)).run (st,#[]) = .ok (some out,next,trace) := by simpa only [Nat.add_assoc] using run
    obtain ⟨safe,mapped⟩ := stock_count_wide_requests data_program ctx trailing wide run40
    exact ⟨safe,mapped,fun _ small => False.elim (narrow small)⟩
/-- Actual scalar count selections establish original values through
final aliases and preserve registers outside their one/two-register allocation. -/
theorem stock_count_selected_values {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx) (trailing : Bool)
    {i x : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.unary (countOp trailing) ty x))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {u : BitVec ty.width} (dfg : DFGCons ctx fr) (get : fr.getAs x ty = .ok u)
    {st next : State} {out : V} {rules : List RuleId} (selected : LowerSelection ctx i st out next rules)
    (chosen : selected.rule = countRule trailing ty.width) {aliases : Array (Option Nat)} {ρ : Nat → CV}
    (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ x r,ctx.valueReg? x = some r → x < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun k => ρ (aliasNum aliases k))) :
    ∃ (nx : Nat) (ρ' : Nat → CV),ctx.valueReg? x = some (.vreg nx .int) ∧
      out = .regsVec [[.vreg (countResult trailing ty.width st.base.nextVreg) .int]] ∧
      next = {st.mark x with base := countBase trailing ty.width st.base (.vreg nx .int)} ∧
      PRun F isem ((countCode trailing ty.width st.base.nextVreg nx).map (·.mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.unary (countOp trailing) u⟩ (ρ' (countResult trailing ty.width st.base.nextVreg)) ∧
      ∀ n,n < st.base.nextVreg ∨ st.base.nextVreg+countAlloc trailing ty.width ≤ n → ρ' n = ρ n := by
  obtain ⟨width,data,type⟩ := count_source_data inv trailing source clif
  have enough := selected.fuelBound
  have count : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl
  obtain ⟨m,fuelEq⟩ : ∃ m,selected.matchFuel = m+2 := ⟨selected.matchFuel-2,by omega⟩
  have matched := selected.matchedRun
  rw [chosen,fuelEq,stock_count_match data_program ctx trailing width source type data st #[] m] at matched
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at matched
  obtain ⟨envEq,stateEq,traceEq⟩ := matched
  have rhs := selected.rhsRun
  rw [chosen,← envEq,← stateEq,← traceEq] at rhs
  change (evalExpr program (Stock.sem ctx) {} (999919+80) (countRule trailing ty.width).rhs
    (countEnv ty.width x)).run (st,#[]) = .ok (some out,next,selected.rhsTrace) at rhs
  obtain ⟨safe,⟨rx,mapped⟩,typed⟩ := root_requests trailing width dfg rfl get rhs
  obtain ⟨nx,rfl⟩ := inv.valueReg x rx mapped
  obtain ⟨trace,forward⟩ := root_rhs trailing width typed mapped st safe #[] 999919
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
  obtain ⟨ρ',execution,value,kept⟩ := stock_count_resolved refines trailing width bounded mapped inputHeld get
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
private theorem clz_inventory : sourceOpcodeIds 107 = [919, 920, 922] := by decide +kernel
/-- Actual first-match selection excludes both narrow widths for the wide fallback. -/
private theorem clz_fallback_width {ctx : Ctx} {i x w : Nat} {info : IInfo}
    (source : ctx.insts[i]? = some info) (type : info.resTys.head? = some (.int w))
    (data : info.data = .data 152 29 [.data 151 107 [],.value x])
    {st next : State} {out : V} {rules : List RuleId} (selected : LowerSelection ctx i st out next rules)
    (chosen : selected.rule = rule_lower_1961) : w ≠ 8 ∧ w ≠ 16 := by
  have atPre : ((program.rulesOf T.lower.id).map Rule.id)[selected.pre.length]? = some rule_lower_1961.id := by
    rw [selected.candidates,chosen,List.map_append,List.map_cons,List.getElem?_append_right (by simp)]
    simp
  have at442 : ((program.rulesOf T.lower.id).map Rule.id)[442]? = some rule_lower_1961.id := by
    rw [show T.lower.id = TId.lower from rfl,List.getElem?_map,lower_idx_1961 data_program]
    rfl
  have preBound : selected.pre.length < ((program.rulesOf T.lower.id).map Rule.id).length := by
    rw [selected.candidates,List.length_map,List.length_append,List.length_cons]
    omega
  have lengthEq : selected.pre.length = 442 := lower_ids_nodup.eq_of_getElem?_eq preBound (atPre.trans at442.symm)
  have count : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl
  have candidates : program.rulesOf TId.lower = selected.pre ++ selected.rule :: selected.post := selected.candidates
  constructor
  · intro eight
    have first := lower_idx_1951 data_program
    rw [candidates,List.getElem?_append_left (by omega)] at first
    obtain ⟨fuel,bound,after,rejected⟩ := selected.rejected _ (List.mem_of_getElem? first)
    obtain ⟨n,fuelEq⟩ : ∃ n,fuel = n+2 := ⟨fuel-2,by omega⟩
    rw [eight] at type
    have matched := stock_count_match data_program ctx false (.inl rfl) source type data st #[] n
    simp only [countRule,countEnv,Bool.false_eq_true,Nat.reduceEqDiff,false_or,or_true,ite_false,ite_true] at matched
    rw [fuelEq,matched] at rejected
    cases rejected
  · intro sixteen
    have first := lower_idx_1955 data_program
    rw [candidates,List.getElem?_append_left (by omega)] at first
    obtain ⟨fuel,bound,after,rejected⟩ := selected.rejected _ (List.mem_of_getElem? first)
    obtain ⟨n,fuelEq⟩ : ∃ n,fuel = n+2 := ⟨fuel-2,by omega⟩
    rw [sixteen] at type
    have matched := stock_count_match data_program ctx false (.inr (.inl rfl)) source type data st #[] n
    simp only [countRule,countEnv,Bool.false_eq_true,Nat.reduceEqDiff,false_or,or_true,ite_false,ite_true] at matched
    rw [fuelEq,matched] at rejected
    cases rejected
/-- Original source opcode/type data and actual matching derive the selected
count rule internally. -/
private theorem selected_clz_rule {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i x : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.unary (countOp false) ty x))
    {st next : State} {out : V} {trace : List RuleId}
    (selected : LowerSelection ctx i st out next trace) : selected.rule = countRule false ty.width := by
  obtain ⟨width,data,type⟩ := count_source_data inv false source clif
  have member := stock_selected_source_opcode_ids inv source clif data selected
  simp only [countOpcode,Bool.false_eq_true,ite_false] at member data
  rw [clz_inventory] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  have count : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl
  have enough := selected.fuelBound
  obtain ⟨fuel,fuelEq⟩ : ∃ fuel,selected.matchFuel = fuel+1 := ⟨selected.matchFuel-1,by omega⟩
  have matched := selected.matchedRun
  rw [fuelEq] at matched
  obtain ⟨bound,args,_⟩ := matchRule_some_inv matched
  rw [stock_matchArgs] at args
  rcases member with first | second | last
  · have candidate : rule_lower_1951 ∈ program.rulesOf T.lower.id := by
      rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
    have chosen : selected.rule = rule_lower_1951 := eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate first
    rw [chosen] at args
    have actualWidth := type_match (target := 8) (name := "I8") rfl rfl source type args
    rw [chosen,actualWidth]
    rfl
  · have candidate : rule_lower_1955 ∈ program.rulesOf T.lower.id := by
      rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
    have chosen : selected.rule = rule_lower_1955 := eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate second
    rw [chosen] at args
    have actualWidth := type_match (target := 16) (name := "I16") rfl rfl source type args
    rw [chosen,actualWidth]
    rfl
  · have candidate : rule_lower_1961 ∈ program.rulesOf T.lower.id := by
      rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
    have chosen : selected.rule = rule_lower_1961 := eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate last
    obtain ⟨notByte,notHalf⟩ := clz_fallback_width source type data selected chosen
    simp only [countRule,Bool.false_eq_true,ite_true,notByte,notHalf,ite_false]
    exact chosen
private theorem ctz_inventory : sourceOpcodeIds 109 = [924, 925, 927] := by decide +kernel
/-- Actual first-match selection excludes both narrow widths for the wide fallback. -/
private theorem ctz_fallback_width {ctx : Ctx} {i x w : Nat} {info : IInfo}
    (source : ctx.insts[i]? = some info) (type : info.resTys.head? = some (.int w))
    (data : info.data = .data 152 29 [.data 151 109 [],.value x])
    {st next : State} {out : V} {rules : List RuleId} (selected : LowerSelection ctx i st out next rules)
    (chosen : selected.rule = rule_lower_1995) : w ≠ 8 ∧ w ≠ 16 := by
  have atPre : ((program.rulesOf T.lower.id).map Rule.id)[selected.pre.length]? = some rule_lower_1995.id := by
    rw [selected.candidates,chosen,List.map_append,List.map_cons,List.getElem?_append_right (by simp)]
    simp
  have at443 : ((program.rulesOf T.lower.id).map Rule.id)[443]? = some rule_lower_1995.id := by
    rw [show T.lower.id = TId.lower from rfl,List.getElem?_map,lower_idx_1995 data_program]
    rfl
  have preBound : selected.pre.length < ((program.rulesOf T.lower.id).map Rule.id).length := by
    rw [selected.candidates,List.length_map,List.length_append,List.length_cons]
    omega
  have lengthEq : selected.pre.length = 443 := lower_ids_nodup.eq_of_getElem?_eq preBound (atPre.trans at443.symm)
  have count : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl
  have candidates : program.rulesOf TId.lower = selected.pre ++ selected.rule :: selected.post := selected.candidates
  constructor
  · intro eight
    have first := lower_idx_1982 data_program
    rw [candidates,List.getElem?_append_left (by omega)] at first
    obtain ⟨fuel,bound,after,rejected⟩ := selected.rejected _ (List.mem_of_getElem? first)
    obtain ⟨n,fuelEq⟩ : ∃ n,fuel = n+2 := ⟨fuel-2,by omega⟩
    rw [eight] at type
    have matched := stock_count_match data_program ctx true (.inl rfl) source type data st #[] n
    simp only [countRule,countEnv,Bool.false_eq_true,Nat.reduceEqDiff,false_or,or_true,ite_false,ite_true] at matched
    rw [fuelEq,matched] at rejected
    cases rejected
  · intro sixteen
    have first := lower_idx_1986 data_program
    rw [candidates,List.getElem?_append_left (by omega)] at first
    obtain ⟨fuel,bound,after,rejected⟩ := selected.rejected _ (List.mem_of_getElem? first)
    obtain ⟨n,fuelEq⟩ : ∃ n,fuel = n+2 := ⟨fuel-2,by omega⟩
    rw [sixteen] at type
    have matched := stock_count_match data_program ctx true (.inr (.inl rfl)) source type data st #[] n
    simp only [countRule,countEnv,Bool.false_eq_true,Nat.reduceEqDiff,false_or,or_true,ite_false,ite_true] at matched
    rw [fuelEq,matched] at rejected
    cases rejected
/-- Original source opcode/type data and actual matching derive the selected
count rule internally. -/
private theorem selected_ctz_rule {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i x : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.unary (countOp true) ty x))
    {st next : State} {out : V} {trace : List RuleId}
    (selected : LowerSelection ctx i st out next trace) : selected.rule = countRule true ty.width := by
  obtain ⟨width,data,type⟩ := count_source_data inv true source clif
  have member := stock_selected_source_opcode_ids inv source clif data selected
  simp only [countOpcode,ite_true] at member data
  rw [ctz_inventory] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  have count : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl
  have enough := selected.fuelBound
  obtain ⟨fuel,fuelEq⟩ : ∃ fuel,selected.matchFuel = fuel+1 := ⟨selected.matchFuel-1,by omega⟩
  have matched := selected.matchedRun
  rw [fuelEq] at matched
  obtain ⟨bound,args,_⟩ := matchRule_some_inv matched
  rw [stock_matchArgs] at args
  rcases member with first | second | last
  · have candidate : rule_lower_1982 ∈ program.rulesOf T.lower.id := by
      rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
    have chosen : selected.rule = rule_lower_1982 := eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate first
    rw [chosen] at args
    have actualWidth := type_match (target := 8) (name := "I8") rfl rfl source type args
    rw [chosen,actualWidth]
    rfl
  · have candidate : rule_lower_1986 ∈ program.rulesOf T.lower.id := by
      rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
    have chosen : selected.rule = rule_lower_1986 := eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate second
    rw [chosen] at args
    have actualWidth := type_match (target := 16) (name := "I16") rfl rfl source type args
    rw [chosen,actualWidth]
    rfl
  · have candidate : rule_lower_1995 ∈ program.rulesOf T.lower.id := by
      rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
    have chosen : selected.rule = rule_lower_1995 := eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate last
    obtain ⟨notByte,notHalf⟩ := ctz_fallback_width source type data selected chosen
    simp only [countRule,Bool.false_eq_true,ite_true,notByte,notHalf,ite_false]
    exact chosen
/-- Original source data and actual first matching derive the count rule;
no selected-rule certificate is required by this interface. -/
theorem stock_selected_count_rule {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    (trailing : Bool) {i x : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.unary (countOp trailing) ty x))
    {st next : State} {out : V} {trace : List RuleId}
    (selected : LowerSelection ctx i st out next trace) : selected.rule = countRule trailing ty.width := by
  cases trailing
  · exact selected_clz_rule inv source clif selected
  · exact selected_ctz_rule inv source clif selected
end Backend.Stock.Proof.ScalarCount
