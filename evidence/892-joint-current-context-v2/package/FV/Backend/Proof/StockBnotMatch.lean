import FV.Backend.Proof.IselCovForm
import FV.Backend.Proof.StockBnotRhs
import FV.Backend.Proof.StockLogicalLookthrough

namespace Backend.Stock.Proof.Bnot
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem sem_unData (ctx : Ctx) (ty t k : Nat) (fs : List V) :
    (Stock.sem ctx).unData ty (.data t k fs) = if t = ty then some (k,fs) else none :=
  Backend.Proof.sem_unData ctx ty t k fs

section Data
attribute [local semireducible] Isle.Aarch64.program
/-- Original mapped source facts derive the scalar NOT root data and width. -/
theorem stock_bnot_data {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i x : Nat} {ty : Clif.Ty} {info : IInfo}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.unary .bnot ty x)) :
    ty.width ≤ 64 ∧ info.data = .data 152 29 [.data 151 100 [],.value x] ∧
      info.resTys.head? = some (.int ty.width) := by
  have accepted := inv.instE i info _ source clif
  have supported : eTy ty = true := by simpa [Compile.instE,Compile.unaryE,Compile.unaryTyE,Compile.tyE,eTy] using accepted
  have raw := inv.data i info _ source clif
  have shape : instData f (.unary .bnot ty x) = .ok (.data 152 29 [.data 151 100 [],.value x]) := by
    simp only [instData,unaryOpcode,supported]
    rfl
  obtain ⟨types,result,typed,len⟩ := inv.resTys i info _ source clif
  simp only [Clif.Inst.resultTypes] at result
  cases result
  exact ⟨eTy_width supported,Except.ok.inj (raw.symm.trans shape),by rw [typed]; simp [ofClif_int_width (isInt_of_eTy supported)]⟩
end Data

/-- The base root matches without changing any scheduling field. -/
theorem stock_bnot_base_match {p : Program} (hp : Data p) (ctx : Ctx) {i x w : Nat} {info : IInfo}
    (source : ctx.insts[i]? = some info) (type : info.resTys.head? = some (.int w)) (width : w ≤ 64)
    (data : info.data = .data 152 29 [.data 151 100 [],.value x]) (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+2) rule_lower_1377 [.inst i]).run (st,tr) =
      .ok (some (env false w x 0 ⟨.lsl,0⟩),st,tr) := by
  have extraction := ext_inst_data_value ctx st.base source
  rw [data,type,Option.getD_some] at extraction
  have fits := ext_fits_in_64 ctx st.base w
  simp only [width,ite_true] at fits
  cases hp
  isel_eval [*,env,rule_lower_1377,sem_extract,sem_unData,ext_ty_int]

/-- Successful fused-NOT matching exposes the original shift and constant
source definitions, so their source value can be reused without materialization. -/
theorem stock_bnot_shift_match_value {p : Program} (hp : Data p)
    {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx) {fr : Clif.Frame} (dfg : DFGCons ctx fr)
    {i y m : Nat} {ty : Clif.Ty} {v : BitVec ty.width} {info : IInfo}
    (source : ctx.insts[i]? = some info) (type : info.resTys.head? = some (.int ty.width))
    (data : info.data = .data 152 29 [.data 151 100 [],.value y]) (get : fr.getAs y ty = .ok v)
    {st : State} {tr : Array RuleId} {environment : Isle.Interp.Env V} {middle : State × Array RuleId}
    (matched : (matchRule p (Stock.sem ctx) {} (m+10) rule_lower_1401 [.inst i]).run (st,tr) = .ok (some environment,middle)) :
    ∃ (z b j1 j2 : Nat) (info1 info2 : IInfo) (ty1 ty3 : Clif.Ty) (c : BitVec ty3.width) (u : BitVec ty.width),
      ctx.defInst? y = some j1 ∧ ctx.insts[j1]? = some info1 ∧ info1.clif = some (.binary .ishl ty1 z b) ∧
      ctx.defInst? b = some j2 ∧ ctx.insts[j2]? = some info2 ∧ info2.clif = some (.iconst ty3 c) ∧
      eTy ty3 = true ∧ fr.getAs z ty = .ok u ∧ v = Clif.Sem.ishl u c := by
  obtain ⟨env0,args,_⟩ := matchRule_some_inv matched
  obtain ⟨e1,pattern,_⟩ := matchArgs_cons_inv args
  rw [stock_matchPat] at pattern
  obtain ⟨fs,extracted,args⟩ := matchPat_extract_inv hp.t209 term_209_kind rfl pattern
  rw [Backend.Proof.sem_extract] at extracted
  have expected := ext_inst_data_value ctx st.base source
  rw [type,Option.getD_some,data] at expected
  rw [expected] at extracted
  cases extracted
  obtain ⟨e2,_,args⟩ := matchArgs_cons_inv args
  obtain ⟨e3,pattern,_⟩ := matchArgs_cons_inv args
  obtain ⟨fields,unData,args⟩ := matchPat_enum_inv hp.t2476 term_2476_kind pattern
  rw [Backend.Proof.sem_unData] at unData
  simp only [ite_true,Option.some.injEq,Prod.mk.injEq] at unData
  obtain ⟨_,rfl⟩ := unData
  obtain ⟨e4,_,args⟩ := matchArgs_cons_inv args
  obtain ⟨e5,shiftPattern,_⟩ := matchArgs_cons_inv args
  rw [← stock_matchPat] at shiftPattern
  exact LogicalSemantics.stock_shift_pattern_value hp inv dfg get shiftPattern

private theorem shift_ctor (ctx : Ctx) (st : State) (w : Nat) (k : Int) :
    (Stock.sem ctx).ctor T.lshl_from_imm64 [.ty (.int w),.int k] st =
      match lshlOf? w k with
      | some sh => .ok (.op (.shiftOpAndAmt sh),st)
      | none => .fail := by
  change Stock.externCtor ctx T.lshl_from_imm64 _ st = _
  rw [stock_ctor_baseOnly ctx T.lshl_from_imm64 _ st (by decide),ctor_lshl_from_imm64 ctx st.base w k]
  cases lshlOf? w k <;> rfl

private theorem shift_match_run {p : Program} (hp : Data p) (ctx : Ctx) {i y z b j1 j2 w : Nat}
    {info info1 info2 : IInfo} {k : Int} (width : w ≤ 64)
    (source : ctx.insts[i]? = some info) (type : info.resTys.head? = some (.int w))
    (data : info.data = .data 152 29 [.data 151 100 [],.value y])
    (defined : ctx.defInst? y = some j1) (found : ctx.insts[j1]? = some info1)
    (shape : info1.data = .data 152 2 [.data 151 103 [],.values [z,b]])
    (constantDef : ctx.defInst? b = some j2) (constantFound : ctx.insts[j2]? = some info2)
    (constantData : info2.data = .data 152 35 [.data 151 57 [],.int k])
    (st : State) (tr : Array RuleId) (m : Nat) :
    (matchRule p (Stock.sem ctx) {} (m+10) rule_lower_1401 [.inst i]).run (st,tr) =
      .ok ((lshlOf? w k).map (env true w z k),st,tr) := by
  have root := ext_inst_data_value ctx st.base source
  rw [data,type,Option.getD_some] at root
  have fits := ext_fits_in_64 ctx st.base w
  simp only [width,ite_true] at fits
  have extraction := ext_inst_data_value ctx st.base found
  rw [shape] at extraction
  have constant := ext_inst_data_value ctx st.base constantFound
  rw [constantData] at constant
  have definition := ext_def_inst_some ctx st.base defined
  have constantDefinition := ext_def_inst_some ctx st.base constantDef
  have construct := shift_ctor ctx st w k
  cases choice : lshlOf? w k <;> rw [choice] at construct
  all_goals
    cases hp
    isel_eval [*,env,rule_lower_1401,sem_extract,sem_unData,ext_value_array_2,ext_ty_int]

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

/-- Original source/DFG facts and actual fused-root matching derive the typed
RHS environment, unchanged complete state and valid shift operand/value. -/
theorem stock_bnot_shift_match_receipts {p : Program} (hp : Data p)
    {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx) {fr : Clif.Frame} (dfg : DFGCons ctx fr)
    {i y m : Nat} {ty : Clif.Ty} {v : BitVec ty.width} {info : IInfo} (width : ty.width ≤ 64)
    (source : ctx.insts[i]? = some info) (type : info.resTys.head? = some (.int ty.width))
    (data : info.data = .data 152 29 [.data 151 100 [],.value y]) (get : fr.getAs y ty = .ok v)
    {st : State} {tr : Array RuleId} {environment : Isle.Interp.Env V} {middle : State × Array RuleId}
    (matched : (matchRule p (Stock.sem ctx) {} (m+10) rule_lower_1401 [.inst i]).run (st,tr) = .ok (some environment,middle)) :
    ∃ (z : Nat) (k : Int) (sh : ShiftOpAndAmt) (u : BitVec ty.width),
      environment = env true ty.width z k sh ∧ middle = (st,tr) ∧ fr.getAs z ty = .ok u ∧
      sh.op = .lsl ∧ sh.amt < ty.width ∧ v = u <<< sh.amt := by
  obtain ⟨z,b,j1,j2,info1,info2,ty1,ty3,c,previous,defined,found,original,constantDef,constantFound,
    constantClif,supported,_,_⟩ := stock_bnot_shift_match_value hp inv dfg source type data get matched
  have accepted := inv.instE j1 info1 _ found original
  have shiftSupported : eTy ty1 = true := by simpa [Compile.instE,Compile.binaryE,Compile.tyE,eTy] using accepted
  have raw := inv.data j1 info1 _ found original
  have rawConstant := inv.data j2 info2 _ constantFound constantClif
  have shape : info1.data = .data 152 2 [.data 151 103 [],.values [z,b]] :=
    Except.ok.inj (raw.symm.trans (ishl_data shiftSupported))
  have constantShape : info2.data = .data 152 35 [.data 151 57 [],.int (imm64OfIconst ty3 c)] :=
    Except.ok.inj (rawConstant.symm.trans (iconst_data supported))
  rw [shift_match_run hp ctx width source type data defined found shape constantDef constantFound constantShape st tr m] at matched
  cases choice : lshlOf? ty.width (imm64OfIconst ty3 c) with
  | none => rw [choice] at matched; cases matched
  | some sh =>
    rw [choice] at matched
    simp only [Option.map_some,Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at matched
    obtain ⟨envEq,stateEq⟩ := matched
    obtain ⟨u,getSource,lsl,bounded,value⟩ := ishl_const_value dfg width defined found original
      constantDef constantFound constantClif supported get choice
    exact ⟨z,imm64OfIconst ty3 c,sh,u,envEq.symm,stateEq.symm,getSource,lsl,bounded,value⟩

end Backend.Stock.Proof.Bnot
