import FV.Backend.Proof.StockLogicalNotLookthrough
import FV.Backend.Proof.StockLogicalNotRootValues

namespace Backend.Stock.Proof.LogicalNot
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.LogicalSelected
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private def opcode : Kind → Nat
  | .band => 97 | .bor => 98 | .bxor => 99
section Data
attribute [local semireducible] Isle.Aarch64.program
private theorem source_data {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    (kind : Kind) {i x z : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.binary kind.cop ty x z)) :
    ty.width ≤ 64 ∧ info.data = .data 152 2 [.data 151 (opcode kind) [],.values [x,z]] ∧
      info.resTys.head? = some (.int ty.width) := by
  have accepted := inv.instE i info _ source clif
  have supported : eTy ty = true := by cases kind <;> simpa [Kind.cop,Compile.instE,Compile.binaryE,Compile.tyE,eTy] using accepted
  have raw := inv.data i info _ source clif
  obtain ⟨types,result,typed,len⟩ := inv.resTys i info _ source clif
  simp only [Clif.Inst.resultTypes] at result
  cases result
  refine ⟨eTy_width supported,?_,by rw [typed]; simp [ofClif_int_width (isInt_of_eTy supported)]⟩
  have shape : instData f (.binary kind.cop ty x z) = .ok (.data 152 2 [.data 151 (opcode kind) [],.values [x,z]]) := by
    cases kind <;> simp only [Kind.cop,opcode,instData,binaryOpcode,supported,ite_true] <;> rfl
  exact Except.ok.inj (raw.symm.trans shape)
end Data
private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem sem_unData (ctx : Ctx) (ty t k : Nat) (fs : List V) :
    (Stock.sem ctx).unData ty (.data t k fs) = if t = ty then some (k,fs) else none := Backend.Proof.sem_unData ctx ty t k fs

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

/-- All six fused root matches retain the complete Stock state and expose the
actual hidden NOT source in the canonical helper environment. -/
theorem stock_not_root_match {p : Program} (hp : Data p) (ctx : Ctx) (kind : Kind) (left : Bool)
    {i x z y j w : Nat} {info child : IInfo} (source : ctx.insts[i]? = some info)
    (type : info.resTys.head? = some (.int w)) (width : w ≤ 64)
    (data : info.data = .data 152 2 [.data 151 (opcode kind) [],.values [if left then z else x,if left then x else z]])
    (defined : ctx.defInst? z = some j) (found : ctx.insts[j]? = some child)
    (childData : child.data = .data 152 29 [.data 151 100 [],.value y])
    (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+2) (notRule kind left) [.inst i]).run (st,tr) =
      .ok (some (rootEnv left w x y),st,tr) := by
  have root := ext_inst_data_value ctx st.base source
  rw [data,type,Option.getD_some] at root
  have fits := ext_fits_in_64 ctx st.base w
  simp only [width,ite_true] at fits
  have definition := ext_def_inst_some ctx st.base defined
  have childExtract := ext_inst_data_value ctx st.base found
  rw [childData] at childExtract
  cases hp
  cases kind <;> cases left <;> simp only [Bool.false_eq_true,ite_false,ite_true] at root <;>
    isel_eval [*,notRule,opcode,rootEnv,rule_lower_1429,rule_lower_1431,rule_lower_1466,rule_lower_1468,
      rule_lower_1534,rule_lower_1536,sem_extract,sem_unData,ext_ty_int,ext_value_array_2]

/-- A successful actual fused-root match exposes the real NOT definition and
its original source value; no producer or materialization certificate is needed. -/
theorem stock_not_root_match_source {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) (kind : Kind) (left : Bool) {i x z : Nat} {ty : Clif.Ty} {info : IInfo}
    (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.binary kind.cop ty (if left then z else x) (if left then x else z)))
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {v : BitVec ty.width} (get : fr.getAs z ty = .ok v)
    {m : Nat} {st : State} {tr : Array RuleId} {environment : Isle.Interp.Env V} {middle : State × Array RuleId}
    (matched : (matchRule p (Stock.sem ctx) {} (m+10) (notRule kind left) [.inst i]).run (st,tr) = .ok (some environment,middle)) :
    ∃ (j y : Nat) (child : IInfo) (ty' : Clif.Ty) (u : BitVec ty.width),
      ctx.defInst? z = some j ∧ ctx.insts[j]? = some child ∧ child.clif = some (.unary .bnot ty' y) ∧
      fr.getAs y ty = .ok u ∧ v = ~~~u := by
  obtain ⟨width,data,type⟩ := source_data inv kind source clif
  obtain ⟨env0,args,_⟩ := matchRule_some_inv matched
  cases kind <;> cases left
  all_goals
    obtain ⟨e1,pattern,_⟩ := matchArgs_cons_inv args
    rw [stock_matchPat] at pattern
    obtain ⟨e0,e2,firstMatch,secondMatch⟩ := root_patterns hp ctx source data pattern
    first
    | (rw [← stock_matchPat] at firstMatch
       exact stock_not_pattern_value hp inv dfg get firstMatch)
    | (rw [← stock_matchPat] at secondMatch
       exact stock_not_pattern_value hp inv dfg get secondMatch)

section ChildData
attribute [local semireducible] Isle.Aarch64.program
private theorem child_shape {f : Clif.Function} {ty : Clif.Ty} {y : Nat} (supported : eTy ty = true) :
    instData f (.unary .bnot ty y) = .ok (.data 152 29 [.data 151 100 [],.value y]) := by
  simp only [instData,unaryOpcode,supported]
  rfl
end ChildData

/-- Actual source facts and a successful fused root match derive its typed
canonical environment, unchanged state, and the complemented source operand. -/
theorem stock_not_root_match_receipts {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) (kind : Kind) (left : Bool) {i x z : Nat} {ty : Clif.Ty} {info : IInfo}
    (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.binary kind.cop ty (if left then z else x) (if left then x else z)))
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {v : BitVec ty.width} (get : fr.getAs z ty = .ok v)
    {m : Nat} {st : State} {tr : Array RuleId} {environment : Isle.Interp.Env V} {middle : State × Array RuleId}
    (matched : (matchRule p (Stock.sem ctx) {} (m+10) (notRule kind left) [.inst i]).run (st,tr) = .ok (some environment,middle)) :
    ty.width ≤ 64 ∧ ∃ (y : Nat) (u : BitVec ty.width), environment = rootEnv left ty.width x y ∧
      middle = (st,tr) ∧ fr.getAs y ty = .ok u ∧ v = ~~~u := by
  obtain ⟨width,data,type⟩ := source_data inv kind source clif
  obtain ⟨j,y,child,ty',u,defined,found,original,getY,value⟩ := stock_not_root_match_source hp inv kind left source clif dfg get matched
  have accepted := inv.instE j child _ found original
  have supported : eTy ty' = true := by
    simpa [Compile.instE,Compile.unaryE,Compile.unaryTyE,Compile.tyE,eTy] using accepted
  have raw := inv.data j child _ found original
  have childData : child.data = .data 152 29 [.data 151 100 [],.value y] :=
    Except.ok.inj (raw.symm.trans (child_shape supported))
  rw [stock_not_root_match hp ctx kind left source type width data defined found childData st tr (m+8)] at matched
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at matched
  obtain ⟨environmentEq,stateEq⟩ := matched
  exact ⟨width,y,u,environmentEq.symm,stateEq.symm,getY,value⟩

/-- Actual root selection and original source operands establish the original
binary source value for all six mirrored NOT fusions. The canonical helper
match/RHS/environment certificates are derived internally. -/
theorem stock_not_selected_root_values {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (kind : Kind) (left : Bool) {i x z : Nat} {ty : Clif.Ty} {info : IInfo}
    (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.binary kind.cop ty (if left then z else x) (if left then x else z)))
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {u v : BitVec ty.width}
    (sourceX : fr.getAs x ty = .ok u) (sourceZ : fr.getAs z ty = .ok v)
    {st next : State} {out : V} {trace : List RuleId} (selected : LowerSelection ctx i st out next trace)
    (chosen : selected.rule = notRule kind left) {aliases : Array (Option Nat)} {ρ : Nat → CV}
    (bounded : aliases.size ≤ st.base.nextVreg) (extent : ∀ x r,ctx.valueReg? x = some r → x < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun z => ρ (aliasNum aliases z))) :
    ∃ (mi : MInst) (ρ' : Nat → CV), out = .regsVec [[.vreg st.base.nextVreg .int]] ∧
      next.base = (st.base.fresh .int).2.emit mi ∧
      PRun F isem [mi.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))] ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.binary kind.cop (if left then v else u) (if left then u else v)⟩ (ρ' st.base.nextVreg) ∧
      ∀ n,n ≠ st.base.nextVreg → ρ' n = ρ n := by
  have fuelBound := selected.fuelBound
  have count : (program.rulesOf T.lower.id).length ≤ 999987 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
  have enough : 10 ≤ selected.matchFuel := by omega
  obtain ⟨m,fuelEq⟩ : ∃ m,selected.matchFuel = m+10 := ⟨selected.matchFuel-10,by omega⟩
  have matched := selected.matchedRun
  rw [chosen,fuelEq] at matched
  obtain ⟨width,y,previous,envEq,stateEq,getY,value⟩ := stock_not_root_match_receipts
    data_program inv kind left source clif dfg sourceZ matched
  have rhs := selected.rhsRun
  rw [chosen,envEq,stateEq] at rhs
  obtain ⟨mi,ρ',output,base,execution,result,kept⟩ := stock_not_root_values inv refines kind left width
    dfg sourceX getY bounded extent held rhs
  have original : notOpVal (notALU kind) u previous =
      Clif.Sem.binary kind.cop (if left then v else u) (if left then u else v) := by
    rw [value]
    cases kind <;> cases left <;> simp [notOpVal,notALU,Kind.cop,Clif.Sem.binary,Clif.Sem.band,Clif.Sem.bor,Clif.Sem.bxor,
      BitVec.and_comm,BitVec.or_comm,BitVec.xor_comm]
  rw [original] at result
  exact ⟨mi,ρ',output,base,execution,result,kept⟩

end Backend.Stock.Proof.LogicalNot
