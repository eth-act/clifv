import FV.Backend.Proof.IselCovForm
import FV.Backend.Proof.IselFamALUAExt
import FV.Backend.Proof.StockLogicalLookthrough
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
/-- Actual extended roots match original source data and expose their canonical
Stock environment without changing scheduling state. -/
theorem stock_addsub_extend_match {p : Program} (hp : Data p) (ctx : Ctx) (subtract left : Bool)
    (side : subtract = true → left = false) {i x y z w b : Nat} {info : IInfo}
    (source : ctx.insts[i]? = some info) (type : info.resTys.head? = some (.int w)) (width : w ≤ 64)
    (data : info.data = .data 152 2 [.data 151 (if subtract then 74 else 73) [],.values [x,y]])
    {cop : Clif.ExtendOp} {ty' : Clif.Ty} {e : ExtendOp}
    (defined : ctx.defClif? (if left then x else y) = some (.extend cop ty' z))
    (operandType : ctx.valueType? z = some (.int b)) (extended : extOpOf cop b = some e)
    (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+10) (extendRule subtract left) [.inst i]).run (st,tr) =
      .ok (some (extendEnv left w (if left then y else x) z e),st,tr) := by
  have extraction := ext_inst_data_value ctx st.base source
  rw [data,type,Option.getD_some] at extraction
  have extension := ext_extended_some ctx st.base defined operandType extended
  cases hp
  cases subtract <;> cases left
  · simp only [extendRule,extendEnv,Bool.false_eq_true,ite_false,ite_true] at *
    isel_eval [*,rule_lower_108,ext_ty_int_ref_scalar_64_extract ctx st.base width,ext_value_array_2,sem_extract,sem_unData]
  · simp only [extendRule,extendEnv,Bool.false_eq_true,ite_false,ite_true] at *
    isel_eval [*,rule_lower_111,ext_ty_int_ref_scalar_64_extract ctx st.base width,ext_value_array_2,sem_extract,sem_unData]
  · simp only [extendRule,extendEnv,Bool.false_eq_true,ite_false,ite_true] at *
    isel_eval [*,rule_lower_816,ext_ty_int_ref_scalar_64_extract ctx st.base width,ext_value_array_2,sem_extract,sem_unData]
  · cases side rfl
/-- A successful actual extended operand pattern gives the original definition
and narrow source value, independent of the machine register map. -/
theorem stock_addsub_extended_pattern_value {p : Program} (hp : Data p) {ctx : Ctx}
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {y slot : Nat} {ty : Clif.Ty} {v : BitVec ty.width}
    (get : fr.getAs y ty = .ok v) {st : State} {env env' : Isle.Interp.Env V}
    (matched : matchPat p (Stock.sem ctx) st (.term 15 345 [.bind 121 slot (.wildcard 121)])
      (.value y) env = .ok (some env')) :
    ∃ (cop : Clif.ExtendOp) (ty' : Clif.Ty) (z b : Nat) (e : ExtendOp) (a : Clif.Val),
      ctx.defClif? y = some (.extend cop ty' z) ∧ ctx.valueType? z = some (.int b) ∧
      extOpOf cop b = some e ∧ fr.regs z = some a ∧ a.ty.width = b ∧
      v = extVal cop ty.width a.bits := by
  obtain ⟨fields,extracted,_⟩ := matchPat_extract_inv hp.t345 term_345_kind rfl matched
  rw [sem_extract] at extracted
  obtain ⟨cop,ty',z,b,e,defined,typed,extended,_⟩ := ext_extended_inv ctx st.base extracted
  obtain ⟨a,source,width,value⟩ := extend_value dfg defined typed get
  exact ⟨cop,ty',z,b,e,a,defined,typed,extended,source,width,value⟩
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
/-- Original extended operands are recovered from actual root matching. -/
theorem stock_addsub_extend_match_value {p : Program} (hp : Data p) (ctx : Ctx) (subtract left : Bool)
    (side : subtract = true → left = false) {i x y w n : Nat} {info : IInfo}
    (source : ctx.insts[i]? = some info) (type : info.resTys.head? = some (.int w))
    (data : info.data = .data 152 2 [.data 151 (if subtract then 74 else 73) [],.values [x,y]])
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {ty : Clif.Ty} {v : BitVec ty.width}
    (get : fr.getAs (if left then x else y) ty = .ok v)
    {st : State} {tr : Array RuleId} {env : Isle.Interp.Env V} {middle : State × Array RuleId}
    (matched : (matchRule p (Stock.sem ctx) {} (n+10) (extendRule subtract left) [.inst i]).run (st,tr) =
      .ok (some env,middle)) :
    ∃ (cop : Clif.ExtendOp) (ty' : Clif.Ty) (z b : Nat) (e : ExtendOp) (a : Clif.Val),
      ctx.defClif? (if left then x else y) = some (.extend cop ty' z) ∧
      ctx.valueType? z = some (.int b) ∧ extOpOf cop b = some e ∧
      fr.regs z = some a ∧ a.ty.width = b ∧ v = extVal cop ty.width a.bits := by
  obtain ⟨initial,args,_⟩ := matchRule_some_inv matched
  cases subtract <;> cases left
  · simp only [extendRule,Bool.false_eq_true,ite_false] at args data get ⊢
    obtain ⟨ex,ey,_,ez,pattern⟩ := binary_patterns hp source type data args
    exact stock_addsub_extended_pattern_value hp dfg get pattern
  · simp only [extendRule,Bool.false_eq_true,ite_false,ite_true] at args data get ⊢
    obtain ⟨ex,ey,pattern,_⟩ := binary_patterns hp source type data args
    exact stock_addsub_extended_pattern_value hp dfg get pattern
  · simp only [extendRule,Bool.false_eq_true,ite_false,ite_true] at args data get ⊢
    obtain ⟨ex,ey,_,ez,pattern⟩ := binary_patterns hp source type data args
    exact stock_addsub_extended_pattern_value hp dfg get pattern
  · cases side rfl
section SourceData
attribute [local semireducible] Isle.Aarch64.program
/-- Original accepted add/subtract instructions determine the exact raw opcode,
operand data and type used by the Stock matcher. -/
theorem stock_addsub_source_data {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    (subtract : Bool) {i x y : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.binary (if subtract then .isub else .iadd) ty x y)) :
    ty.width ≤ 64 ∧ info.data = .data 152 2 [.data 151 (if subtract then 74 else 73) [],.values [x,y]] ∧
      info.resTys.head? = some (.int ty.width) := by
  have accepted := inv.instE i info _ source clif
  have supported : eTy ty = true := by
    cases subtract <;> simpa [Compile.instE,Compile.binaryE,Compile.tyE,eTy] using accepted
  have raw := inv.data i info _ source clif
  obtain ⟨types,result,typed,_⟩ := inv.resTys i info _ source clif
  simp only [Clif.Inst.resultTypes] at result
  cases result
  refine ⟨?_,?_,by rw [typed]; simp [ofClif_int_width (isInt_of_eTy supported)]⟩
  · cases ty <;> simp [eTy,Clif.Ty.width] at supported ⊢
  · have expected : instData f (.binary (if subtract then .isub else .iadd) ty x y) =
        .ok (.data 152 2 [.data 151 (if subtract then 74 else 73) [],.values [x,y]]) := by
      cases subtract <;> simp [instData,binaryOpcode,supported] <;> rfl
    exact Except.ok.inj (raw.symm.trans expected)
end SourceData
/-- Actual successful extended matching determines the canonical environment
and original source value; neither is an independent caller certificate. -/
theorem stock_addsub_extend_match_receipts {p : Program} (hp : Data p) (ctx : Ctx) (subtract left : Bool)
    (side : subtract = true → left = false) {i x y w n : Nat} {info : IInfo}
    (source : ctx.insts[i]? = some info) (type : info.resTys.head? = some (.int w)) (width : w ≤ 64)
    (data : info.data = .data 152 2 [.data 151 (if subtract then 74 else 73) [],.values [x,y]])
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {ty : Clif.Ty} {v : BitVec ty.width}
    (get : fr.getAs (if left then x else y) ty = .ok v)
    {st : State} {tr : Array RuleId} {env : Isle.Interp.Env V} {middle : State × Array RuleId}
    (matched : (matchRule p (Stock.sem ctx) {} (n+10) (extendRule subtract left) [.inst i]).run (st,tr) =
      .ok (some env,middle)) :
    ∃ (cop : Clif.ExtendOp) (ty' : Clif.Ty) (z b : Nat) (e : ExtendOp) (a : Clif.Val),
      ctx.defClif? (if left then x else y) = some (.extend cop ty' z) ∧
      ctx.valueType? z = some (.int b) ∧ extOpOf cop b = some e ∧
      fr.regs z = some a ∧ a.ty.width = b ∧ v = extVal cop ty.width a.bits ∧
      env = extendEnv left w (if left then y else x) z e ∧ middle = (st,tr) := by
  obtain ⟨cop,ty',z,b,e,a,defined,typed,extended,getZ,sourceWidth,value⟩ :=
    stock_addsub_extend_match_value hp ctx subtract left side source type data dfg get matched
  have forward := stock_addsub_extend_match hp ctx subtract left side source type width data defined typed extended st tr n
  rw [forward] at matched
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at matched
  obtain ⟨envEq,stateEq⟩ := matched
  exact ⟨cop,ty',z,b,e,a,defined,typed,extended,getZ,sourceWidth,value,envEq.symm,stateEq.symm⟩
section RawShape
attribute [local semireducible] Isle.Aarch64.program
private theorem iconst_data {f : Clif.Function} {ty : Clif.Ty} {u : BitVec ty.width}
    (supported : eTy ty = true) : instData f (.iconst ty u) =
      .ok (.data 152 35 [.data 151 57 [],.int (imm64OfIconst ty u)]) := by
  simp only [instData,supported,ite_true]
  rfl
private theorem ishl_data {f : Clif.Function} {ty : Clif.Ty} {z b : Nat}
    (supported : eTy ty = true) : instData f (.binary .ishl ty z b) =
      .ok (.data 152 2 [.data 151 103 [],.values [z,b]]) := by
  simp only [instData,binaryOpcode,supported,ite_true]
  rfl
end RawShape
private theorem shift_ctor (ctx : Ctx) (st : State) (w : Nat) (kk : Int) :
    (Stock.sem ctx).ctor T.lshl_from_imm64 [.ty (.int w),.int kk] st =
      match lshlOf? w kk with
      | some sh => .ok (.op (.shiftOpAndAmt sh),st)
      | none => .fail := by
  change Stock.externCtor ctx T.lshl_from_imm64 _ st = _
  rw [stock_ctor_baseOnly ctx T.lshl_from_imm64 _ st (by decide),ctor_lshl_from_imm64 ctx st.base w kk]
  cases lshlOf? w kk <;> rfl
theorem stock_addsub_shift_match {p : Program} (hp : Data p) (ctx : Ctx) (subtract left : Bool)
    (side : subtract = true → left = false) {i x y z b w j1 j2 : Nat} {kk : Int} {info info1 info2 : IInfo}
    (source : ctx.insts[i]? = some info) (type : info.resTys.head? = some (.int w)) (width : w ≤ 64)
    (data : info.data = .data 152 2 [.data 151 (if subtract then 74 else 73) [],.values [x,y]])
    (defined : ctx.defInst? (if left then x else y) = some j1) (found : ctx.insts[j1]? = some info1)
    (shiftData : info1.data = .data 152 2 [.data 151 103 [],.values [z,b]])
    (constantDef : ctx.defInst? b = some j2) (constantFound : ctx.insts[j2]? = some info2)
    (constantData : info2.data = .data 152 35 [.data 151 57 [],.int kk])
    (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+10) (shiftRule subtract left) [.inst i]).run (st,tr) =
      .ok ((lshlOf? w kk).map (shiftEnv left w (if left then y else x) z (if left then x else y) kk),st,tr) := by
  have extraction := ext_inst_data_value ctx st.base source
  rw [data,type,Option.getD_some] at extraction
  have shiftExtraction := ext_inst_data_value ctx st.base found
  rw [shiftData] at shiftExtraction
  have constant := ext_inst_data_value ctx st.base constantFound
  rw [constantData] at constant
  have definition := ext_def_inst_some ctx st.base defined
  have constantDefinition := ext_def_inst_some ctx st.base constantDef
  have construct := shift_ctor ctx st w kk
  cases choice : lshlOf? w kk <;> rw [choice] at construct
  all_goals cases hp
  all_goals cases subtract <;> cases left
  · simp only [shiftRule,shiftEnv,Bool.false_eq_true,ite_false,ite_true] at *
    isel_eval [*,rule_lower_116,sem_extract,sem_unData,ext_ty_int_ref_scalar_64_extract ctx st.base width,ext_value_array_2]
    all_goals rfl
  · simp only [shiftRule,shiftEnv,Bool.false_eq_true,ite_false,ite_true] at *
    isel_eval [*,rule_lower_120,sem_extract,sem_unData,ext_ty_int_ref_scalar_64_extract ctx st.base width,ext_value_array_2]
    all_goals rfl
  · simp only [shiftRule,shiftEnv,Bool.false_eq_true,ite_false,ite_true] at *
    isel_eval [*,rule_lower_821,sem_extract,sem_unData,ext_ty_int_ref_scalar_64_extract ctx st.base width,ext_value_array_2]
    all_goals rfl
  · cases side rfl
  · simp only [shiftRule,shiftEnv,Bool.false_eq_true,ite_false,ite_true] at *
    isel_eval [*,rule_lower_116,sem_extract,sem_unData,ext_ty_int_ref_scalar_64_extract ctx st.base width,ext_value_array_2]
    all_goals rfl
  · simp only [shiftRule,shiftEnv,Bool.false_eq_true,ite_false,ite_true] at *
    isel_eval [*,rule_lower_120,sem_extract,sem_unData,ext_ty_int_ref_scalar_64_extract ctx st.base width,ext_value_array_2]
    all_goals rfl
  · simp only [shiftRule,shiftEnv,Bool.false_eq_true,ite_false,ite_true] at *
    isel_eval [*,rule_lower_821,sem_extract,sem_unData,ext_ty_int_ref_scalar_64_extract ctx st.base width,ext_value_array_2]
    all_goals rfl
  · cases side rfl
theorem stock_addsub_shift_match_value {p : Program} (hp : Data p)
    {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx) (subtract left : Bool)
    (side : subtract = true → left = false) {i x y w n : Nat} {info : IInfo}
    (source : ctx.insts[i]? = some info) (type : info.resTys.head? = some (.int w))
    (data : info.data = .data 152 2 [.data 151 (if subtract then 74 else 73) [],.values [x,y]])
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {ty : Clif.Ty} {v : BitVec ty.width}
    (get : fr.getAs (if left then x else y) ty = .ok v)
    {st : State} {tr : Array RuleId} {env : Isle.Interp.Env V} {middle : State × Array RuleId}
    (matched : (matchRule p (Stock.sem ctx) {} (n+10) (shiftRule subtract left) [.inst i]).run (st,tr) =
      .ok (some env,middle)) :
    ∃ (z b j1 j2 : Nat) (info1 info2 : IInfo) (ty1 ty3 : Clif.Ty) (c : BitVec ty3.width) (u : BitVec ty.width),
      ctx.defInst? (if left then x else y) = some j1 ∧ ctx.insts[j1]? = some info1 ∧
      info1.clif = some (.binary .ishl ty1 z b) ∧ ctx.defInst? b = some j2 ∧ ctx.insts[j2]? = some info2 ∧
      info2.clif = some (.iconst ty3 c) ∧ eTy ty3 = true ∧ fr.getAs z ty = .ok u ∧ v = Clif.Sem.ishl u c := by
  obtain ⟨initial,args,_⟩ := matchRule_some_inv matched
  cases subtract <;> cases left
  · simp only [shiftRule,Bool.false_eq_true,ite_false,ite_true] at args data get ⊢
    obtain ⟨ex,ey,_,ez,pattern⟩ := binary_patterns hp source type data args
    exact LogicalSemantics.stock_shift_pattern_value hp inv dfg get pattern
  · simp only [shiftRule,Bool.false_eq_true,ite_false,ite_true] at args data get ⊢
    obtain ⟨ex,ey,pattern,_⟩ := binary_patterns hp source type data args
    exact LogicalSemantics.stock_shift_pattern_value hp inv dfg get pattern
  · simp only [shiftRule,Bool.false_eq_true,ite_false,ite_true] at args data get ⊢
    obtain ⟨ex,ey,_,ez,pattern⟩ := binary_patterns hp source type data args
    exact LogicalSemantics.stock_shift_pattern_value hp inv dfg get pattern
  · cases side rfl
theorem stock_addsub_shift_match_receipts {p : Program} (hp : Data p)
    {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx) (subtract left : Bool)
    (side : subtract = true → left = false) {i x y n : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (type : info.resTys.head? = some (.int ty.width)) (width : ty.width ≤ 64)
    (data : info.data = .data 152 2 [.data 151 (if subtract then 74 else 73) [],.values [x,y]])
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {v : BitVec ty.width}
    (get : fr.getAs (if left then x else y) ty = .ok v)
    {st : State} {tr : Array RuleId} {env : Isle.Interp.Env V} {middle : State × Array RuleId}
    (matched : (matchRule p (Stock.sem ctx) {} (n+10) (shiftRule subtract left) [.inst i]).run (st,tr) = .ok (some env,middle)) :
    ∃ (z : Nat) (kk : Int) (sh : ShiftOpAndAmt) (u : BitVec ty.width),
      env = shiftEnv left ty.width (if left then y else x) z (if left then x else y) kk sh ∧
      middle = (st,tr) ∧ fr.getAs z ty = .ok u ∧ sh.op = .lsl ∧ sh.amt < ty.width ∧ v = u <<< sh.amt := by
  obtain ⟨z,b,j1,j2,info1,info2,ty1,ty3,c,previous,defined,found,original,constantDef,constantFound,
    constantClif,supported,_,_⟩ := stock_addsub_shift_match_value hp inv subtract left side source type data dfg get matched
  have accepted := inv.instE j1 info1 _ found original
  have shiftSupported : eTy ty1 = true := by simpa [Compile.instE,Compile.binaryE,Compile.tyE,eTy] using accepted
  have raw := inv.data j1 info1 _ found original
  have rawConstant := inv.data j2 info2 _ constantFound constantClif
  have shape : info1.data = .data 152 2 [.data 151 103 [],.values [z,b]] :=
    Except.ok.inj (raw.symm.trans (ishl_data shiftSupported))
  have constantShape : info2.data = .data 152 35 [.data 151 57 [],.int (imm64OfIconst ty3 c)] :=
    Except.ok.inj (rawConstant.symm.trans (iconst_data supported))
  rw [stock_addsub_shift_match hp ctx subtract left side source type width data defined found shape constantDef constantFound constantShape st tr n] at matched
  cases choice : lshlOf? ty.width (imm64OfIconst ty3 c) with
  | none => rw [choice] at matched; cases matched
  | some sh =>
    rw [choice] at matched
    simp only [Option.map_some,Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at matched
    obtain ⟨envEq,stateEq⟩ := matched
    obtain ⟨u,getSource,lsl,bounded,value⟩ := ishl_const_value dfg width defined found original
      constantDef constantFound constantClif supported get choice
    exact ⟨z,imm64OfIconst ty3 c,sh,u,envEq.symm,stateEq.symm,getSource,lsl,bounded,value⟩
end Backend.Stock.Proof.ScalarAddSub
