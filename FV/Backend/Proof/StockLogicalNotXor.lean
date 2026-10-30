import FV.Backend.Proof.IselFamALUAMul
import FV.Backend.Proof.StockLogicalNotRootValues
import FV.Backend.Proof.StockBnotMatch

namespace Backend.Stock.Proof.LogicalNot
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.LogicalSelected
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem sem_unData (ctx : Ctx) (ty t k : Nat) (fs : List V) :
    (Stock.sem ctx).unData ty (.data t k fs) = if t = ty then some (k,fs) else none :=
  Backend.Proof.sem_unData ctx ty t k fs

/-- Actual NOT-of-XOR matching exposes the underlying original XOR operands
without requiring the XOR result to be materialized in a machine register. -/
theorem stock_not_xor_match_source {p : Program} (hp : Data p)
    {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx) {fr : Clif.Frame} (dfg : DFGCons ctx fr)
    {i z m : Nat} {ty : Clif.Ty} {v : BitVec ty.width} {info : IInfo}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.unary .bnot ty z))
    (get : fr.getAs z ty = .ok v)
    {st : State} {tr : Array RuleId} {environment : Isle.Interp.Env V} {middle : State × Array RuleId}
    (matched : (matchRule p (Stock.sem ctx) {} (m+10) rule_lower_1406 [.inst i]).run (st,tr) = .ok (some environment,middle)) :
    ∃ (j x y : Nat) (child : IInfo) (ty' : Clif.Ty) (u w : BitVec ty.width),
      ctx.defInst? z = some j ∧ ctx.insts[j]? = some child ∧ child.clif = some (.binary .bxor ty' x y) ∧
      fr.getAs x ty = .ok u ∧ fr.getAs y ty = .ok w ∧ v = Clif.Sem.binary .bxor u w := by
  obtain ⟨width,data,type⟩ := Bnot.stock_bnot_data inv source clif
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
  obtain ⟨e5,xorPattern,_⟩ := matchArgs_cons_inv args
  obtain ⟨j,child,fields,env0,defined,found,childData,rest⟩ :=
    defInst_match_inv hp ctx hp.t2449 term_2449_kind hp.t2383 term_2383_kind xorPattern
  obtain ⟨cl,original,raw⟩ := ctxInv_clif inv.identityView defined found
  rw [childData] at raw
  obtain ⟨ty',x,y,rfl,_,rfl⟩ := instData_binary_inv variantNames_Bxor (cop := .bxor) rfl raw
  obtain ⟨u,w,getX,getY,value⟩ := binary_value dfg defined found original rfl get
  exact ⟨j,x,y,child,ty',u,w,defined,found,original,getX,getY,value⟩

private theorem match_run {p : Program} (hp : Data p) (ctx : Ctx) {i z j x y w : Nat} {info child : IInfo}
    (source : ctx.insts[i]? = some info) (type : info.resTys.head? = some (.int w)) (width : w ≤ 64)
    (data : info.data = .data 152 29 [.data 151 100 [],.value z])
    (defined : ctx.defInst? z = some j) (found : ctx.insts[j]? = some child)
    (childData : child.data = .data 152 2 [.data 151 99 [],.values [x,y]])
    (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+2) rule_lower_1406 [.inst i]).run (st,tr) =
      .ok (some (rootEnv false w x y),st,tr) := by
  have root := ext_inst_data_value ctx st.base source
  rw [data,type,Option.getD_some] at root
  have fits := ext_fits_in_64 ctx st.base w
  simp only [width,ite_true] at fits
  have definition := ext_def_inst_some ctx st.base defined
  have childExtract := ext_inst_data_value ctx st.base found
  rw [childData] at childExtract
  cases hp
  isel_eval [*,rule_lower_1406,rootEnv,sem_extract,sem_unData,ext_ty_int,ext_value_array_2]

section Data
attribute [local semireducible] Isle.Aarch64.program
private theorem xor_shape {f : Clif.Function} {ty : Clif.Ty} {x y : Nat} (supported : eTy ty = true) :
    instData f (.binary .bxor ty x y) = .ok (.data 152 2 [.data 151 99 [],.values [x,y]]) := by
  simp only [instData,binaryOpcode,supported,ite_true]
  rfl
end Data

/-- Successful selected NOT-of-XOR matching derives its typed environment and
original operand values, retaining the complete scheduling state. -/
theorem stock_not_xor_match_receipts {p : Program} (hp : Data p)
    {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx) {fr : Clif.Frame} (dfg : DFGCons ctx fr)
    {i z m : Nat} {ty : Clif.Ty} {v : BitVec ty.width} {info : IInfo}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.unary .bnot ty z))
    (get : fr.getAs z ty = .ok v)
    {st : State} {tr : Array RuleId} {environment : Isle.Interp.Env V} {middle : State × Array RuleId}
    (matched : (matchRule p (Stock.sem ctx) {} (m+10) rule_lower_1406 [.inst i]).run (st,tr) = .ok (some environment,middle)) :
    ty.width ≤ 64 ∧ ∃ (x y : Nat) (u w : BitVec ty.width),
      environment = rootEnv false ty.width x y ∧ middle = (st,tr) ∧
      fr.getAs x ty = .ok u ∧ fr.getAs y ty = .ok w ∧ v = Clif.Sem.binary .bxor u w := by
  obtain ⟨width,data,type⟩ := Bnot.stock_bnot_data inv source clif
  obtain ⟨j,x,y,child,ty',u,w,defined,found,original,getX,getY,value⟩ :=
    stock_not_xor_match_source hp inv dfg source clif get matched
  have accepted := inv.instE j child _ found original
  have supported : eTy ty' = true := by
    simpa [Compile.instE,Compile.binaryE,Compile.tyE,eTy] using accepted
  have raw := inv.data j child _ found original
  have childData : child.data = .data 152 2 [.data 151 99 [],.values [x,y]] :=
    Except.ok.inj (raw.symm.trans (xor_shape supported))
  rw [match_run hp ctx source type width data defined found childData st tr (m+8)] at matched
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at matched
  obtain ⟨environmentEq,stateEq⟩ := matched
  exact ⟨width,x,y,u,w,environmentEq.symm,stateEq.symm,getX,getY,value⟩

/-- The seventh fusion computes the original NOT-of-XOR value using the actual
selected rule and the shared NOT helper, with final aliases and fresh writes. -/
theorem stock_not_xor_selected_root_values {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {i z : Nat} {ty : Clif.Ty} {info : IInfo}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.unary .bnot ty z))
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {v : BitVec ty.width} (get : fr.getAs z ty = .ok v)
    {st next : State} {out : V} {trace : List RuleId} (selected : LowerSelection ctx i st out next trace)
    (chosen : selected.rule = rule_lower_1406) {aliases : Array (Option Nat)} {ρ : Nat → CV}
    (bounded : aliases.size ≤ st.base.nextVreg) (extent : ∀ x r,ctx.valueReg? x = some r → x < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun k => ρ (aliasNum aliases k))) :
    ∃ (mi : MInst) (ρ' : Nat → CV), out = .regsVec [[.vreg st.base.nextVreg .int]] ∧
      next.base = (st.base.fresh .int).2.emit mi ∧
      PRun F isem [mi.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))] ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.unary .bnot v⟩ (ρ' st.base.nextVreg) ∧
      ∀ n,n ≠ st.base.nextVreg → ρ' n = ρ n := by
  have fuelBound := selected.fuelBound
  have count : (program.rulesOf T.lower.id).length ≤ 999987 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
  have enough : 10 ≤ selected.matchFuel := by omega
  obtain ⟨m,fuelEq⟩ : ∃ m,selected.matchFuel = m+10 := ⟨selected.matchFuel-10,by omega⟩
  have matched := selected.matchedRun
  rw [chosen,fuelEq] at matched
  obtain ⟨width,x,y,u,w,envEq,stateEq,getX,getY,value⟩ :=
    stock_not_xor_match_receipts data_program inv dfg source clif get matched
  have rhs := selected.rhsRun
  rw [chosen,envEq,stateEq] at rhs
  have sameRhs : rule_lower_1406.rhs = (notRule .bxor false).rhs := rfl
  rw [sameRhs] at rhs
  obtain ⟨mi,ρ',output,base,execution,result,kept⟩ := stock_not_root_values inv refines .bxor false
    width dfg getX getY bounded extent held rhs
  have original : notOpVal (notALU .bxor) u w = Clif.Sem.unary .bnot v := by
    rw [value]
    simp only [notALU,notOpVal,Clif.Sem.binary,Clif.Sem.unary,Clif.Sem.bxor,Clif.Sem.bnot]
    exact BitVec.not_xor_right.symm
  rw [original] at result
  exact ⟨mi,ρ',output,base,execution,result,kept⟩

end Backend.Stock.Proof.LogicalNot
