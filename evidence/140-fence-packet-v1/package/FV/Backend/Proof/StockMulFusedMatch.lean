import FV.Backend.Proof.StockMulValues
import FV.Backend.Proof.StockMulFusedRhs
namespace Backend.Stock.Proof.ScalarMul.Fused
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.ScalarMul
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
section Data
attribute [local semireducible] Isle.Aarch64.program
private theorem source_data {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i x y : Nat} {info : IInfo} {ty : Clif.Ty} (fusion : Fusion)
    (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.binary fusion.cop ty x y)) :
    ty.width ≤ 64 ∧ info.data = .data 152 2 [.data 151 (if fusion.subtract then 74 else 73) [], .values [x,y]] ∧
      info.resTys.head? = some (.int ty.width) := by
  have supported := inv.instE i info _ source clif
  have he : eTy ty = true := by
    cases fusion <;> simpa [Fusion.cop,Fusion.subtract,Compile.instE, Compile.binaryE, Compile.tyE, eTy] using supported
  have data := inv.data i info _ source clif
  obtain ⟨types, result, typed, len⟩ := inv.resTys i info _ source clif
  simp only [Clif.Inst.resultTypes] at result
  cases result
  refine ⟨eTy_width he, ?_, ?_⟩
  · have shape : instData f (.binary fusion.cop ty x y) =
        .ok (.data 152 2 [.data 151 (if fusion.subtract then 74 else 73) [], .values [x,y]]) := by
      cases fusion
      all_goals simp only [Fusion.cop,Fusion.subtract,Bool.false_eq_true,ite_false,ite_true] at *
      · simp only [instData,show binaryOpcode .iadd = some "Iadd" from rfl,he,ite_true]; rfl
      · simp only [instData,show binaryOpcode .iadd = some "Iadd" from rfl,he,ite_true]; rfl
      · simp only [instData,show binaryOpcode .isub = some "Isub" from rfl,he,ite_true]; rfl
    exact Except.ok.inj (data.symm.trans shape)
  · rw [typed]; simp [ofClif_int_width (isInt_of_eTy he)]

end Data
private theorem root_patterns {p : Program} (hp : Data p) (ctx : Ctx) {i a b k opT : Nat} {info : IInfo}
    {tyPat first second : Pattern} {st : State} {environment environment' : Isle.Interp.Env V}
    (source : ctx.insts[i]? = some info) (data : info.data = .data 152 2 [.data 151 k [],.values [a,b]])
    (matched : matchPat p (Backend.sem ctx) st.base
      (.term 18 209 [tyPat,.term 152 2449 [.term 151 opT [],.term 147 1614 [first,second]]])
      (.inst i) environment = .ok (some environment')) :
    ∃ e0 e1, matchPat p (Backend.sem ctx) st.base first (.value a) e0 = .ok (some e1) ∧
      matchPat p (Backend.sem ctx) st.base second (.value b) e1 = .ok (some environment') := by
  obtain ⟨fs,extracted,args⟩ := matchPat_extract_inv hp.t209 term_209_kind rfl matched
  rw [Backend.Proof.sem_extract,ext_inst_data_value ctx st.base source] at extracted
  cases extracted
  obtain ⟨e2,_,args⟩ := matchArgs_cons_inv args
  obtain ⟨e3,binary,ending⟩ := matchArgs_cons_inv args
  have same := matchArgs_nil_nil ctx ending
  subst same
  obtain ⟨fields,decode,args⟩ := matchPat_enum_inv hp.t2449 term_2449_kind binary
  rw [data,Backend.Proof.sem_unData] at decode
  simp only [ite_true,Option.some.injEq,Prod.mk.injEq] at decode
  obtain ⟨_,rfl⟩ := decode
  obtain ⟨e4,_,rest⟩ := matchArgs_cons_inv args
  obtain ⟨e5,firstMatch,secondMatch⟩ := values2_match_inv hp ctx rest
  exact ⟨e4,e5,firstMatch,secondMatch⟩

private theorem mul_pattern_value {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {fr : Clif.Frame} (dfg : DFGCons ctx fr)
    {z s1 s2 : Nat} {ty : Clif.Ty} {product : BitVec ty.width} (get : fr.getAs z ty = .ok product)
    {st : LState} {environment environment' : Isle.Interp.Env V}
    (matched : matchPat p (Backend.sem ctx) st
      (.term 15 1 [.term 18 209 [.wildcard 14,.term 152 2449 [.term 151 2361 [],
        .term 147 1614 [.bind 15 s1 (.wildcard 15),.bind 15 s2 (.wildcard 15)]]]])
      (.value z) environment = .ok (some environment')) :
    ∃ (j a b : Nat) (child : IInfo) (ty' : Clif.Ty) (u v : BitVec ty.width),
      ctx.defInst? z = some j ∧ ctx.insts[j]? = some child ∧ child.clif = some (.binary .imul ty' a b) ∧
      fr.getAs a ty = .ok u ∧ fr.getAs b ty = .ok v ∧ product = Clif.Sem.binary .imul u v := by
  obtain ⟨j,child,fields,env0,defined,found,data,rest⟩ :=
    defInst_match_inv hp ctx hp.t2449 term_2449_kind hp.t2361 term_2361_kind matched
  obtain ⟨cl,original,raw⟩ := ctxInv_clif inv.identityView defined found
  rw [data] at raw
  obtain ⟨ty',a,b,rfl,_,rfl⟩ := instData_binary_inv variantNames_Imul (cop := .imul) rfl raw
  obtain ⟨u,v,getA,getB,value⟩ := binary_value dfg defined found original rfl get
  exact ⟨j,a,b,child,ty',u,v,defined,found,original,getA,getB,value⟩

/-- The real fused root match derives the underlying multiplication source
operands and their original values; the product need not be materialized. -/
theorem stock_mul_fused_match_source {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) (fusion : Fusion) {i x z : Nat} {ty : Clif.Ty} {info : IInfo}
    (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.binary fusion.cop ty (if fusion.left then z else x) (if fusion.left then x else z)))
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {product : BitVec ty.width} (get : fr.getAs z ty = .ok product)
    {m : Nat} {st : State} {tr : Array RuleId} {environment : Isle.Interp.Env V} {middle : State × Array RuleId}
    (matched : (matchRule p (Stock.sem ctx) {} (m+10) fusion.rule [.inst i]).run (st,tr) = .ok (some environment,middle)) :
    ∃ (j a b : Nat) (child : IInfo) (ty' : Clif.Ty) (u v : BitVec ty.width),
      ctx.defInst? z = some j ∧ ctx.insts[j]? = some child ∧ child.clif = some (.binary .imul ty' a b) ∧
      fr.getAs a ty = .ok u ∧ fr.getAs b ty = .ok v ∧ product = Clif.Sem.binary .imul u v := by
  obtain ⟨width,data,type⟩ := source_data inv fusion source clif
  obtain ⟨env0,args,_⟩ := matchRule_some_inv matched
  cases fusion
  all_goals
    obtain ⟨e1,pattern,_⟩ := matchArgs_cons_inv args
    rw [stock_matchPat] at pattern
    obtain ⟨e0,e2,firstMatch,secondMatch⟩ := root_patterns hp ctx source data pattern
    first
    | exact mul_pattern_value hp inv dfg get firstMatch
    | exact mul_pattern_value hp inv dfg get secondMatch

private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem sem_unData (ctx : Ctx) (ty t k : Nat) (fs : List V) :
    (Stock.sem ctx).unData ty (.data t k fs) = if t = ty then some (k,fs) else none := Backend.Proof.sem_unData ctx ty t k fs

/-- Actual typed fused roots select their canonical helper environment and
retain the entire Stock scheduling state. -/
theorem stock_mul_fused_match {p : Program} (hp : Data p) (ctx : Ctx) (fusion : Fusion)
    {i x z a b j w : Nat} {info child : IInfo} (source : ctx.insts[i]? = some info)
    (type : info.resTys.head? = some (.int w)) (width : w ≤ 64)
    (data : info.data = .data 152 2 [.data 151 (if fusion.subtract then 74 else 73) [],
      .values [if fusion.left then z else x,if fusion.left then x else z]])
    (defined : ctx.defInst? z = some j) (found : ctx.insts[j]? = some child)
    (childData : child.data = .data 152 2 [.data 151 77 [],.values [a,b]])
    (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+2) fusion.rule [.inst i]).run (st,tr) =
      .ok (some (rootEnv fusion w x a b),st,tr) := by
  have root := ext_inst_data_value ctx st.base source
  rw [data,type,Option.getD_some] at root
  have scalar := ext_ty_int_ref_scalar_64_extract ctx st.base width
  have definition := ext_def_inst_some ctx st.base defined
  have childExtract := ext_inst_data_value ctx st.base found
  rw [childData] at childExtract
  cases hp
  cases fusion <;> simp only [Fusion.subtract,Fusion.left,ite_true,Bool.false_eq_true,ite_false] at root <;>
    isel_eval [*,Fusion.rule,rootEnv,Fusion.left,rule_lower_125,rule_lower_128,rule_lower_132,sem_extract,sem_unData,ext_value_array_2]

/-- Successful actual selection derives the typed environment, source values
and unchanged match state for every multiply-add/subtract fusion. -/
theorem stock_mul_fused_match_receipts {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) (fusion : Fusion) {i x z : Nat} {ty : Clif.Ty} {info : IInfo}
    (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.binary fusion.cop ty (if fusion.left then z else x) (if fusion.left then x else z)))
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {product : BitVec ty.width} (get : fr.getAs z ty = .ok product)
    {m : Nat} {st : State} {tr : Array RuleId} {environment : Isle.Interp.Env V} {middle : State × Array RuleId}
    (matched : (matchRule p (Stock.sem ctx) {} (m+10) fusion.rule [.inst i]).run (st,tr) = .ok (some environment,middle)) :
    ty.width ≤ 64 ∧ ∃ (a b : Nat) (u v : BitVec ty.width),
      environment = rootEnv fusion ty.width x a b ∧ middle = (st,tr) ∧
      fr.getAs a ty = .ok u ∧ fr.getAs b ty = .ok v ∧ product = Clif.Sem.binary .imul u v := by
  obtain ⟨width,data,type⟩ := source_data inv fusion source clif
  obtain ⟨j,a,b,child,ty',u,v,defined,found,original,getA,getB,value⟩ :=
    stock_mul_fused_match_source hp inv fusion source clif dfg get matched
  have childData := (stock_mul_data inv found original).2.1
  rw [stock_mul_fused_match hp ctx fusion source type width data defined found childData st tr (m+8)] at matched
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at matched
  obtain ⟨environmentEq,stateEq⟩ := matched
  exact ⟨width,a,b,u,v,environmentEq.symm,stateEq.symm,getA,getB,value⟩
end Backend.Stock.Proof.ScalarMul.Fused
