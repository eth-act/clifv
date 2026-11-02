import FV.Backend.Proof.IselFamALUALogic
import FV.Backend.Proof.IselFamAluBBfm
import FV.Backend.Proof.StockShiftRootValues
namespace Backend.Stock.Proof.ShiftBitfield
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.ScalarShift
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

def fusedRule (signed : Bool) : Rule := if signed then rule_lower_1704 else rule_lower_1707
def fusedKind (signed : Bool) : Kind := if signed then .asr else .lsr
def fusedEnv (w x : Nat) (a b : Int) : Isle.Interp.Env V :=
  env4 (.ty (.int w)) (.value x) (.int a) (.int b)
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


/-- Both fused right-shift patterns expose the original nested shift and its two
constant definitions; no materialized intermediate register is assumed. -/
theorem stock_bitfield_match_sources {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) (signed : Bool) {i z y : Nat} {info : IInfo}
    (source : ctx.insts[i]? = some info)
    (data : info.data = .data 152 2 [.data 151 (if signed then 105 else 104) [],.values [z,y]])
    {m : Nat} {st : State} {tr : Array RuleId} {environment : Isle.Interp.Env V} {middle : State × Array RuleId}
    (matched : (matchRule p (Stock.sem ctx) {} (m+10) (fusedRule signed) [.inst i]).run (st,tr) =
      .ok (some environment,middle)) :
    ∃ (x a jz ja jb : Nat) (iz ia ib : IInfo) (tz ta tb : Clif.Ty)
      (ca : BitVec ta.width) (cb : BitVec tb.width),
      ctx.defInst? z = some jz ∧ ctx.insts[jz]? = some iz ∧ iz.clif = some (.binary .ishl tz x a) ∧
      ctx.defInst? a = some ja ∧ ctx.insts[ja]? = some ia ∧ ia.clif = some (.iconst ta ca) ∧
      ctx.defInst? y = some jb ∧ ctx.insts[jb]? = some ib ∧ ib.clif = some (.iconst tb cb) := by
  obtain ⟨env0,args,_⟩ := matchRule_some_inv matched
  cases signed <;> simp only [fusedRule,Bool.false_eq_true,ite_false,ite_true] at args data
  all_goals
    obtain ⟨e1,pattern,_⟩ := matchArgs_cons_inv args
    rw [stock_matchPat] at pattern
    obtain ⟨e0,e2,left,right⟩ := root_patterns hp ctx source data pattern
    obtain ⟨jz,iz,fsz,ez,dz,sz,rawz,restz⟩ :=
      defInst_match_inv hp ctx hp.t2449 term_2449_kind hp.t2387 term_2387_kind left
    obtain ⟨clz,cz,rz⟩ := ctxInv_clif inv.identityView dz sz
    rw [rawz] at rz
    obtain ⟨tz,x,a,rfl,_,rfl⟩ := instData_binary_inv variantNames_Ishl (cop := .ishl) rfl rz
    obtain ⟨ea,_,patA⟩ := values2_match_inv hp ctx restz
    obtain ⟨ja,ia,fsa,ea',da,sa,rawa,_⟩ :=
      defInst_match_inv hp ctx hp.t2482 term_2482_kind hp.t2341 term_2341_kind patA
    obtain ⟨cla,ca,ra⟩ := ctxInv_clif inv.identityView da sa
    rw [rawa] at ra
    obtain ⟨ta,va,rfl,rfl⟩ := instData_iconst_inv ra
    obtain ⟨jb,ib,fsb,eb,db,sb,rawb,_⟩ :=
      defInst_match_inv hp ctx hp.t2482 term_2482_kind hp.t2341 term_2341_kind right
    obtain ⟨clb,cb,rb⟩ := ctxInv_clif inv.identityView db sb
    rw [rawb] at rb
    obtain ⟨tb,vb,rfl,rfl⟩ := instData_iconst_inv rb
    exact ⟨x,a,jz,ja,jb,iz,ia,ib,tz,ta,tb,va,vb,dz,sz,cz,da,sa,ca,db,sb,cb⟩

private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem sem_unData (ctx : Ctx) (ty t k : Nat) (fs : List V) :
    (Stock.sem ctx).unData ty (.data t k fs) = if t = ty then some (k,fs) else none :=
  Backend.Proof.sem_unData ctx ty t k fs

private theorem match_run {p : Program} (hp : Data p) (ctx : Ctx) (signed : Bool)
    {i z y x a jz ja jb w : Nat} {info iz ia ib : IInfo} {ca cb : Int}
    (source : ctx.insts[i]? = some info) (type : info.resTys.head? = some (.int w))
    (data : info.data = .data 152 2 [.data 151 (if signed then 105 else 104) [],.values [z,y]])
    (dz : ctx.defInst? z = some jz) (sz : ctx.insts[jz]? = some iz)
    (rz : iz.data = .data 152 2 [.data 151 103 [],.values [x,a]])
    (da : ctx.defInst? a = some ja) (sa : ctx.insts[ja]? = some ia)
    (ra : ia.data = .data 152 35 [.data 151 57 [],.int ca])
    (db : ctx.defInst? y = some jb) (sb : ctx.insts[jb]? = some ib)
    (rb : ib.data = .data 152 35 [.data 151 57 [],.int cb])
    (st : State) (tr : Array RuleId) (m : Nat) :
    (matchRule p (Stock.sem ctx) {} (m+10) (fusedRule signed) [.inst i]).run (st,tr) =
      .ok ((if w = 32 ∨ w = 64 then some (fusedEnv w x (u64 ca) (u64 cb)) else none),st,tr) := by
  have root := ext_inst_data_value ctx st.base source
  rw [data,type,Option.getD_some] at root
  have defz := ext_def_inst_some ctx st.base dz
  have defa := ext_def_inst_some ctx st.base da
  have defb := ext_def_inst_some ctx st.base db
  have getz := ext_inst_data_value ctx st.base sz
  have geta := ext_inst_data_value ctx st.base sa
  have getb := ext_inst_data_value ctx st.base sb
  rw [rz] at getz
  rw [ra] at geta
  rw [rb] at getb
  have gate := ext_ty_32_or_64 ctx st.base w
  by_cases width : w = 32 ∨ w = 64
  all_goals simp only [width,ite_true,ite_false] at gate ⊢
  all_goals cases hp
  all_goals cases signed <;> simp only [Bool.false_eq_true,ite_false,ite_true] at root <;>
    isel_eval [*,fusedRule,fusedEnv,rule_lower_1704,rule_lower_1707,sem_extract,sem_unData,ext_value_array_2,ext_u64_from_imm64]

section Data
attribute [local semireducible] Isle.Aarch64.program
private theorem source_data {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    (kind : Kind) {i x y : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.binary kind.cop ty x y)) :
    IW ty.width ∧ info.data = .data 152 2 [.data 151 kind.opcode [],.values [x,y]] ∧
      info.resTys.head? = some (.int ty.width) := by
  have accepted := inv.instE i info _ source clif
  have supported : eTy ty = true := by
    cases kind <;> simpa [Kind.cop,Compile.instE,Compile.binaryE,Compile.tyE,eTy] using accepted
  have raw := inv.data i info _ source clif
  obtain ⟨types,result,typed,len⟩ := inv.resTys i info _ source clif
  simp only [Clif.Inst.resultTypes] at result
  cases result
  refine ⟨?_,?_,by rw [typed]; simp [ofClif_int_width (isInt_of_eTy supported)]⟩
  · cases ty <;> simp [eTy,Clif.Ty.width,IW] at supported ⊢
  · have expected : instData f (.binary kind.cop ty x y) = .ok (.data 152 2 [.data 151 kind.opcode [],.values [x,y]]) := by
      cases kind <;> simp only [Kind.cop,Kind.opcode,instData,binaryOpcode,supported,ite_true] <;> rfl
    exact Except.ok.inj (raw.symm.trans expected)
end Data

section ConstantData
attribute [local semireducible] Isle.Aarch64.program
private theorem iconst_data {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {j : Nat} {info : IInfo} {ty : Clif.Ty} {c : BitVec ty.width}
    (found : ctx.insts[j]? = some info) (clif : info.clif = some (.iconst ty c)) :
    eTy ty = true ∧ info.data = .data 152 35 [.data 151 57 [],.int (imm64OfIconst ty c)] := by
  have accepted := inv.instE j info _ found clif
  have supported : eTy ty = true := by simpa [Compile.instE,Compile.tyE,eTy] using accepted
  have raw := inv.data j info _ found clif
  have shape : instData f (.iconst ty c) =
      .ok (.data 152 35 [.data 151 57 [],.int (imm64OfIconst ty c)]) := by
    simp only [instData,supported,ite_true]; rfl
  exact ⟨supported,Except.ok.inj (raw.symm.trans shape)⟩
end ConstantData

/-- Real fused matching derives both counts, the hidden source operand, the
canonical environment and unchanged scheduling state from original DFG facts. -/
theorem stock_bitfield_match_receipts {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) (signed : Bool) {i z y : Nat} {ty : Clif.Ty} {info : IInfo}
    (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.binary (fusedKind signed).cop ty z y))
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {v : BitVec ty.width} {amount : Clif.Val}
    (getZ : fr.getAs z ty = .ok v) (getY : fr.regs y = some amount)
    {m : Nat} {st : State} {tr : Array RuleId} {environment : Isle.Interp.Env V} {middle : State × Array RuleId}
    (matched : (matchRule p (Stock.sem ctx) {} (m+10) (fusedRule signed) [.inst i]).run (st,tr) =
      .ok (some environment,middle)) :
    (ty.width = 32 ∨ ty.width = 64) ∧ ∃ (x a b : Nat) (u : BitVec ty.width),
      environment = fusedEnv ty.width x a b ∧ middle = (st,tr) ∧ u64 (a : Int) = a ∧ u64 (b : Int) = b ∧
      fr.getAs x ty = .ok u ∧
      (fusedKind signed).value v amount =
        (if signed then (u <<< (a % ty.width)).sshiftRight (b % ty.width)
         else (u <<< (a % ty.width)) >>> (b % ty.width)) := by
  obtain ⟨width,data,type⟩ := source_data inv (fusedKind signed) source clif
  have data' : info.data = .data 152 2 [.data 151 (if signed then 105 else 104) [],.values [z,y]] := by
    cases signed <;> exact data
  obtain ⟨x,a,jz,ja,jb,iz,ia,ib,tz,ta,tb,ca,cb,dz,sz,cz,da,sa,cla,db,sb,clb⟩ :=
    stock_bitfield_match_sources hp inv signed source data' matched
  obtain ⟨supportedA,rawA⟩ := iconst_data inv sa cla
  obtain ⟨supportedB,rawB⟩ := iconst_data inv sb clb
  have rawZ := (source_data inv .lsl sz cz).2.1
  rw [match_run hp ctx signed source type data' dz sz rawZ da sa rawA db sb rawB st tr m] at matched
  by_cases wide : ty.width = 32 ∨ ty.width = 64
  · rw [if_pos wide] at matched
    simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at matched
    obtain ⟨envEq,stateEq⟩ := matched
    rw [u64_imm64OfIconst_fb (eTy_width supportedA),u64_imm64OfIconst_fb (eTy_width supportedB)] at envEq
    obtain ⟨vals,execution,lookup⟩ := dfg.1 z jz iz _ _ dz sz cz rfl (getAs_ok getZ)
    obtain ⟨u,ya,r,getX,getA,shift,rfl,_⟩ :=
      evalInst_shift_ok (rfl : Clif.BinaryOp.ishl.isShift = true) (execution default)
    have same := lookup_zip_single_fb lookup
    cases same
    have countA := dfg_iconst_fb dfg da sa cla getA
    have countB := dfg_iconst_fb dfg db sb clb getY
    subst countA
    subst countB
    simp only [Clif.Sem.shift,Option.some.injEq] at shift
    subst shift
    refine ⟨wide,x,ca.toNat,cb.toNat,u,envEq.symm,stateEq.symm,
      u64_toNat_fb (eTy_width supportedA) ca,u64_toNat_fb (eTy_width supportedB) cb,getX,?_⟩
    cases signed <;> rfl
  · rw [if_neg wide] at matched
    cases matched
end Backend.Stock.Proof.ShiftBitfield
