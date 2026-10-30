import FV.Backend.Proof.IselRulesALUA
import FV.Backend.Proof.StockSourceView
import FV.Backend.Proof.IselCovForm
import FV.Backend.Proof.StockAddSubRhs
namespace Backend.Stock.Proof.ScalarAddSub
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem sem_unData (ctx : Ctx) (t : Nat) (v : V) :
    (Stock.sem ctx).unData t v = (Backend.sem ctx).unData t v := rfl
private theorem binary_patterns {p : Program} (hp : Data p) {ctx : Ctx}
    {i x y w opcode : Nat} {info : IInfo} (source : ctx.insts[i]? = some info)
    (type : info.resTys.head? = some (.int w))
    (data : info.data = .data 152 2 [.data 151 opcode [],.values [x,y]])
    {typePat opcodePat px py : Pattern} {st : State} {env env' : Isle.Interp.Env V}
    (matched : matchArgs p (Stock.sem ctx) st
      [.term 18 209 [typePat,.term 152 2449 [opcodePat,.term 147 1614 [px,py]]]]
      [.inst i] env = .ok (some env')) :
    ∃ ex ey, matchPat p (Stock.sem ctx) st px (.value x) ex = .ok (some ey) ∧
      ∃ ez,matchPat p (Stock.sem ctx) st py (.value y) ey = .ok (some ez) := by
  rw [stock_matchArgs] at matched
  obtain ⟨first,head,_⟩ := matchArgs_cons_inv matched
  obtain ⟨fields,extracted,patterns⟩ := matchPat_extract_inv hp.t209 term_209_kind rfl head
  rw [Backend.Proof.sem_extract] at extracted
  have expected := ext_inst_data_value ctx st.base source
  rw [data,type,Option.getD_some] at expected
  rw [expected] at extracted
  cases extracted
  obtain ⟨typed,_,rest⟩ := matchArgs_cons_inv patterns
  obtain ⟨formatted,formatMatch,_⟩ := matchArgs_cons_inv rest
  obtain ⟨formatFields,unFormat,formatPatterns⟩ := matchPat_enum_inv hp.t2449 term_2449_kind formatMatch
  have formatEq := sem_unData_inv unFormat
  simp only [V.data.injEq] at formatEq
  obtain ⟨_,_,fieldEq⟩ := formatEq
  rw [← fieldEq] at formatPatterns
  obtain ⟨opEnv,_,valuePatterns⟩ := matchArgs_cons_inv formatPatterns
  obtain ⟨middle,left,right⟩ := values2_match_inv hp ctx valuePatterns
  rw [← stock_matchPat] at left right
  exact ⟨opEnv,middle,left,_,right⟩
section RawShape
attribute [local semireducible] Isle.Aarch64.program
private theorem iconst_data {f : Clif.Function} {ty : Clif.Ty} {u : BitVec ty.width}
    (supported : eTy ty = true) : instData f (.iconst ty u) =
      .ok (.data 152 35 [.data 151 57 [],.int (imm64OfIconst ty u)]) := by
  simp only [instData,supported,ite_true]; rfl
end RawShape
private theorem literal_operand {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {fr : Clif.Frame} (dfg : DFGCons ctx fr)
    {y slot : Nat} {ty : Clif.Ty} {u : BitVec ty.width} (get : fr.getAs y ty = .ok u)
    {st : State} {env env' : Isle.Interp.Env V}
    (pattern : matchPat p (Stock.sem ctx) st
      (.term 15 1 [.term 18 209 [.wildcard 14,.term 152 2482 [.term 151 2341 [],
        .term 134 144 [.term 4 325 [.bind 64 slot (.wildcard 64)]]]]])
      (.value y) env = .ok (some env')) :
    ∃ (j : Nat) (info : IInfo) (imm : Imm12),ctx.defInst? y = some j ∧ ctx.insts[j]? = some info ∧
      info.clif = some (.iconst ty u) ∧ Imm12.ofNat? (u64 (imm64OfIconst ty u)) = some imm := by
  rw [stock_matchPat] at pattern
  obtain ⟨j,info,fs,e0,defined,found,data,rest⟩ :=
    defInst_match_inv hp ctx hp.t2482 term_2482_kind hp.t2341 term_2341_kind pattern
  obtain ⟨cl,original,raw⟩ := ctxInv_clif inv.identityView defined found
  rw [data] at raw
  obtain ⟨ty',c,rfl,rfl⟩ := instData_iconst_inv raw
  have value := dfg_single dfg defined found original rfl (getAs_ok get) (a := ⟨ty',c⟩)
    (fun vals cm cm' run => by rw [evalInst_iconst] at run; cases run; rfl)
  cases value
  obtain ⟨imm,valid,_⟩ := imm12_args_inv hp ctx rest
  exact ⟨j,info,imm,defined,found,original,valid⟩
theorem stock_addsub_imm_match {p : Program} (hp : Data p) (ctx : Ctx) (subtract left : Bool)
    (side : subtract = true → left = false) {i x y w j : Nat} {kk : Int} {info infoj : IInfo} {imm : Imm12}
    (source : ctx.insts[i]? = some info) (type : info.resTys.head? = some (.int w)) (width : w ≤ 64)
    (data : info.data = .data 152 2 [.data 151 (if subtract then 74 else 73) [],.values [x,y]])
    (defined : ctx.defInst? (if left then x else y) = some j) (found : ctx.insts[j]? = some infoj)
    (constantData : infoj.data = .data 152 35 [.data 151 57 [],.int kk])
    (immediate : Imm12.ofNat? (u64 kk) = some imm) (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+10) (immRule subtract left) [.inst i]).run (st,tr) =
      .ok (some (immEnv left w (if left then y else x) imm),st,tr) := by
  have extraction := ext_inst_data_value ctx st.base source
  rw [data,type,Option.getD_some] at extraction
  have constant := ext_inst_data_value ctx st.base found
  rw [constantData] at constant
  have definition := ext_def_inst_some ctx st.base defined
  have operand := ext_imm12_from_u64_some ctx st.base immediate
  cases hp
  cases subtract <;> cases left
  · simp only [immRule,immEnv,Bool.false_eq_true,ite_false,ite_true] at *
    isel_eval [*,rule_lower_90,sem_extract,sem_unData,ext_ty_int_ref_scalar_64_extract ctx st.base width,ext_value_array_2,ext_u64_from_imm64]
    all_goals rfl
  · simp only [immRule,immEnv,Bool.false_eq_true,ite_false,ite_true] at *
    isel_eval [*,rule_lower_93,sem_extract,sem_unData,ext_ty_int_ref_scalar_64_extract ctx st.base width,ext_value_array_2,ext_u64_from_imm64]
    all_goals rfl
  · simp only [immRule,immEnv,Bool.false_eq_true,ite_false,ite_true] at *
    isel_eval [*,rule_lower_805,sem_extract,sem_unData,ext_ty_int_ref_scalar_64_extract ctx st.base width,ext_value_array_2,ext_u64_from_imm64]
    all_goals rfl
  · cases side rfl
/-- Positive immediate matching derives the literal from original DFG values,
its valid encoding and canonical environment from the actual successful match. -/
theorem stock_addsub_imm_match_receipts {p : Program} (hp : Data p)
    {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx) (subtract left : Bool)
    (side : subtract = true → left = false) {i x y n : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (type : info.resTys.head? = some (.int ty.width)) (width : ty.width ≤ 64)
    (data : info.data = .data 152 2 [.data 151 (if subtract then 74 else 73) [],.values [x,y]])
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {v : BitVec ty.width}
    (get : fr.getAs (if left then x else y) ty = .ok v)
    {st : State} {tr : Array RuleId} {env : Isle.Interp.Env V} {middle : State × Array RuleId}
    (matched : (matchRule p (Stock.sem ctx) {} (n+10) (immRule subtract left) [.inst i]).run (st,tr) = .ok (some env,middle)) :
    ∃ imm,env = immEnv left ty.width (if left then y else x) imm ∧ middle = (st,tr) ∧
      imm.value = v.toNat ∧ imm.bits < 4096 := by
  have originalOperand : ∃ (j : Nat) (infoj : IInfo) (imm : Imm12),
      ctx.defInst? (if left then x else y) = some j ∧ ctx.insts[j]? = some infoj ∧
      infoj.clif = some (.iconst ty v) ∧ Imm12.ofNat? (u64 (imm64OfIconst ty v)) = some imm := by
    obtain ⟨initial,args,_⟩ := matchRule_some_inv matched
    cases subtract <;> cases left
    · simp only [immRule,Bool.false_eq_true,ite_false,ite_true] at args data get ⊢
      obtain ⟨ex,ey,_,ez,pattern⟩ := binary_patterns hp source type data args
      exact literal_operand hp inv dfg get pattern
    · simp only [immRule,Bool.false_eq_true,ite_false,ite_true] at args data get ⊢
      obtain ⟨ex,ey,pattern,_⟩ := binary_patterns hp source type data args
      exact literal_operand hp inv dfg get pattern
    · simp only [immRule,Bool.false_eq_true,ite_false,ite_true] at args data get ⊢
      obtain ⟨ex,ey,_,ez,pattern⟩ := binary_patterns hp source type data args
      exact literal_operand hp inv dfg get pattern
    · cases side rfl
  obtain ⟨j,infoj,imm,defined,found,original,valid⟩ := originalOperand
  have accepted := inv.instE j infoj _ found original
  have supported : eTy ty = true := by simpa [Compile.instE,Compile.tyE,eTy] using accepted
  have raw := inv.data j infoj _ found original
  have expected : instData f (.iconst ty v) = .ok (.data 152 35 [.data 151 57 [],.int (imm64OfIconst ty v)]) := iconst_data supported
  have shape := Except.ok.inj (raw.symm.trans expected)
  have forward := stock_addsub_imm_match hp ctx subtract left side source type width data defined found shape valid st tr n
  rw [forward] at matched
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at matched
  obtain ⟨envEq,stateEq⟩ := matched
  obtain ⟨immValue,immBound⟩ := imm12_ofNat_value valid (u64_lt _)
  rw [u64_imm64OfIconst width] at immValue
  exact ⟨imm,envEq.symm,stateEq.symm,immValue,immBound⟩
end Backend.Stock.Proof.ScalarAddSub
