import FV.Backend.Proof.RegallocCSem
import FV.Backend.Proof.StockSourceView
import FV.Backend.Proof.LowerDecide

namespace Backend.Stock.Proof.LogicalSemantics
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

private theorem literal_of_pattern {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {fr : Clif.Frame} (dfg : DFGCons ctx fr)
    {y slot : Nat} {ty : Clif.Ty} {u : BitVec ty.width} (source : fr.getAs y ty = .ok u)
    {st : State} {env env' : Isle.Interp.Env V}
    (pattern : matchPat p (Stock.sem ctx) st
      (.term 15 1 [.term 18 209 [.wildcard 14,
        .term 152 2482 [.term 151 2341 [],.bind 134 slot (.wildcard 134)]]]) (.value y) env = .ok (some env')) :
    ∃ (j : Nat) (info : IInfo) (ty' : Clif.Ty) (c : BitVec ty'.width),
      ctx.defInst? y = some j ∧ ctx.insts[j]? = some info ∧ info.clif = some (.iconst ty' c) ∧
      (⟨ty,u⟩ : Clif.Val) = ⟨ty',c⟩ := by
  rw [stock_matchPat] at pattern
  obtain ⟨j,info,fs,e0,hj,hij,hdj,_⟩ :=
    defInst_match_inv hp ctx hp.t2482 term_2482_kind hp.t2341 term_2341_kind pattern
  obtain ⟨cl,hcl,hdat⟩ := ctxInv_clif inv.identityView hj hij
  rw [hdj] at hdat
  obtain ⟨ty',c,rfl,rfl⟩ := instData_iconst_inv hdat
  have value := dfg_single dfg hj hij hcl rfl (getAs_ok source) (a := ⟨ty',c⟩)
    (fun vals cm cm' run => by rw [evalInst_iconst] at run; cases run; rfl)
  exact ⟨j,info,ty',c,hj,hij,hcl,value⟩

/-- A successful logical immediate match gets the source constant value from
original DFG semantics, independently of Stock register numbering. -/
theorem stock_logical_constant_match_value {p : Program} (hp : Data p)
    {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) (left : Bool)
    {k x y m : Nat} {ty : Clif.Ty} {u : BitVec ty.width}
    (source : fr.getAs (if left then x else y) ty = .ok u)
    {st : State} {tr : Array RuleId} {env : Isle.Interp.Env V} {middle : State × Array RuleId}
    (matched : (matchRule p (Stock.sem ctx) {} (m + 10)
      (if left then rule_inst_3923 else rule_inst_3920)
      [.data 59 k [],.ty (.int ty.width),.value x,.value y]).run (st,tr) = .ok (some env,middle)) :
    ∃ (j : Nat) (info : IInfo) (ty' : Clif.Ty) (c : BitVec ty'.width),
      ctx.defInst? (if left then x else y) = some j ∧ ctx.insts[j]? = some info ∧
      info.clif = some (.iconst ty' c) ∧ (⟨ty,u⟩ : Clif.Val) = ⟨ty',c⟩ := by
  cases left
  · obtain ⟨env0,args,_⟩ := matchRule_some_inv matched
    obtain ⟨e1,_,args⟩ := matchArgs_cons_inv args
    obtain ⟨e2,_,args⟩ := matchArgs_cons_inv args
    obtain ⟨e3,_,args⟩ := matchArgs_cons_inv args
    obtain ⟨e4,pattern,_⟩ := matchArgs_cons_inv args
    exact literal_of_pattern hp inv dfg source pattern
  · obtain ⟨env0,args,_⟩ := matchRule_some_inv matched
    obtain ⟨e1,_,args⟩ := matchArgs_cons_inv args
    obtain ⟨e2,_,args⟩ := matchArgs_cons_inv args
    obtain ⟨e3,pattern,_⟩ := matchArgs_cons_inv args
    exact literal_of_pattern hp inv dfg source pattern

private theorem shift_of_pattern {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {fr : Clif.Frame} (dfg : DFGCons ctx fr)
    {y zSlot cSlot : Nat} {ty : Clif.Ty} {v : BitVec ty.width} (source : fr.getAs y ty = .ok v)
    {st : State} {env env' : Isle.Interp.Env V}
    (pattern : matchPat p (Stock.sem ctx) st
      (.term 15 1 [.term 18 209 [.wildcard 14,.term 152 2449 [.term 151 2387 [],
        .term 147 1614 [.bind 15 zSlot (.wildcard 15),.term 15 1 [.term 18 209 [.wildcard 14,
          .term 152 2482 [.term 151 2341 [],.bind 134 cSlot (.wildcard 134)]]]]]]])
        (.value y) env = .ok (some env')) :
    ∃ (z b j1 j2 : Nat) (info1 info2 : IInfo) (ty1 ty3 : Clif.Ty) (c : BitVec ty3.width) (u : BitVec ty.width),
      ctx.defInst? y = some j1 ∧ ctx.insts[j1]? = some info1 ∧ info1.clif = some (.binary .ishl ty1 z b) ∧
      ctx.defInst? b = some j2 ∧ ctx.insts[j2]? = some info2 ∧ info2.clif = some (.iconst ty3 c) ∧
      eTy ty3 = true ∧ fr.getAs z ty = .ok u ∧ v = Clif.Sem.ishl u c := by
  rw [stock_matchPat] at pattern
  obtain ⟨j1,info1,fs1,e5,hj1,hij1,hd1,rest⟩ :=
    defInst_match_inv hp ctx hp.t2449 term_2449_kind hp.t2387 term_2387_kind pattern
  obtain ⟨cl1,hcl1,hdat1⟩ := ctxInv_clif inv.identityView hj1 hij1
  rw [hd1] at hdat1
  obtain ⟨ty1,z,b,rfl,_,rfl⟩ := instData_binary_inv variantNames_Ishl (cop := .ishl) rfl hdat1
  obtain ⟨e6,_,constant⟩ := values2_match_inv hp ctx rest
  obtain ⟨j2,info2,fs2,e7,hj2,hij2,hd2,_⟩ :=
    defInst_match_inv hp ctx hp.t2482 term_2482_kind hp.t2341 term_2341_kind constant
  obtain ⟨cl2,hcl2,hdat2⟩ := ctxInv_clif inv.identityView hj2 hij2
  rw [hd2] at hdat2
  obtain ⟨ty3,c,rfl,rfl⟩ := instData_iconst_inv hdat2
  have supported := instData_iconst_eTy hdat2
  obtain ⟨vals,execution,lookup⟩ := dfg.1 y j1 info1 _ _ hj1 hij1 hcl1 rfl (getAs_ok source)
  obtain ⟨u,bv,r',hz,hb,result,rfl⟩ := evalInst_shift_inv rfl (execution default)
  have same := lookup_zip_single lookup
  cases same
  have literal := dfg_single dfg hj2 hij2 hcl2 rfl (get_ok hb) (a := ⟨ty3,c⟩)
    (fun vals cm cm' run => by rw [evalInst_iconst] at run; cases run; rfl)
  subst literal
  simp only [Clif.Sem.shift,Option.some.injEq] at result
  subst result
  exact ⟨z,b,j1,j2,info1,info2,ty,ty3,c,u,hj1,hij1,hcl1,hj2,hij2,hcl2,supported,hz,rfl⟩

/-- Reusable source-definition/value receipt for an actual nested LSL pattern.
This is shared by logical binary and unary-NOT selected roots. -/
theorem stock_shift_pattern_value {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {fr : Clif.Frame} (dfg : DFGCons ctx fr)
    {y zSlot cSlot : Nat} {ty : Clif.Ty} {v : BitVec ty.width} (source : fr.getAs y ty = .ok v)
    {st : State} {env env' : Isle.Interp.Env V}
    (pattern : matchPat p (Stock.sem ctx) st
      (.term 15 1 [.term 18 209 [.wildcard 14,.term 152 2449 [.term 151 2387 [],
        .term 147 1614 [.bind 15 zSlot (.wildcard 15),.term 15 1 [.term 18 209 [.wildcard 14,
          .term 152 2482 [.term 151 2341 [],.bind 134 cSlot (.wildcard 134)]]]]]]])
        (.value y) env = .ok (some env')) :
    ∃ (z b j1 j2 : Nat) (info1 info2 : IInfo) (ty1 ty3 : Clif.Ty) (c : BitVec ty3.width) (u : BitVec ty.width),
      ctx.defInst? y = some j1 ∧ ctx.insts[j1]? = some info1 ∧ info1.clif = some (.binary .ishl ty1 z b) ∧
      ctx.defInst? b = some j2 ∧ ctx.insts[j2]? = some info2 ∧ info2.clif = some (.iconst ty3 c) ∧
      eTy ty3 = true ∧ fr.getAs z ty = .ok u ∧ v = Clif.Sem.ishl u c := by
  exact shift_of_pattern hp inv dfg source pattern

/-- Successful Stock shift-side matches expose both real source definitions;
original DFG consistency supplies the unshifted operand and shifted value. -/
theorem stock_logical_shift_match_value {p : Program} (hp : Data p)
    {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) (left : Bool)
    {k x y m : Nat} {ty : Clif.Ty} {v : BitVec ty.width}
    (source : fr.getAs (if left then x else y) ty = .ok v)
    {st : State} {tr : Array RuleId} {env : Isle.Interp.Env V} {middle : State × Array RuleId}
    (matched : (matchRule p (Stock.sem ctx) {} (m + 10)
      (if left then rule_inst_3931 else rule_inst_3928)
      [.data 59 k [],.ty (.int ty.width),.value x,.value y]).run (st,tr) = .ok (some env,middle)) :
    ∃ (z b j1 j2 : Nat) (info1 info2 : IInfo) (ty1 ty3 : Clif.Ty) (c : BitVec ty3.width) (u : BitVec ty.width),
      ctx.defInst? (if left then x else y) = some j1 ∧ ctx.insts[j1]? = some info1 ∧
      info1.clif = some (.binary .ishl ty1 z b) ∧ ctx.defInst? b = some j2 ∧ ctx.insts[j2]? = some info2 ∧
      info2.clif = some (.iconst ty3 c) ∧ eTy ty3 = true ∧ fr.getAs z ty = .ok u ∧ v = Clif.Sem.ishl u c := by
  cases left
  · obtain ⟨env0,args,_⟩ := matchRule_some_inv matched
    obtain ⟨e1,_,args⟩ := matchArgs_cons_inv args
    obtain ⟨e2,_,args⟩ := matchArgs_cons_inv args
    obtain ⟨e3,_,args⟩ := matchArgs_cons_inv args
    obtain ⟨e4,pattern,_⟩ := matchArgs_cons_inv args
    exact shift_of_pattern hp inv dfg source pattern
  · obtain ⟨env0,args,_⟩ := matchRule_some_inv matched
    obtain ⟨e1,_,args⟩ := matchArgs_cons_inv args
    obtain ⟨e2,_,args⟩ := matchArgs_cons_inv args
    obtain ⟨e3,pattern,_⟩ := matchArgs_cons_inv args
    exact shift_of_pattern hp inv dfg source pattern

private theorem stock_sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem stock_sem_unData (ctx : Ctx) (ty t k : Nat) (fs : List V) :
    (Stock.sem ctx).unData ty (.data t k fs) = if t = ty then some (k,fs) else none := sem_unData ctx ty t k fs
private theorem imm_ctor (ctx : Ctx) (st : State) (w : Nat) (kk : Int) :
    (Stock.sem ctx).ctor T.imm_logic_from_imm64 [.ty (.int w),.int kk] st =
      match immLogicOf? w kk with
      | some imm => .ok (.op (.immLogic imm),st)
      | none => .fail := by
  change Stock.externCtor ctx T.imm_logic_from_imm64 _ st = _
  rw [stock_ctor_baseOnly ctx T.imm_logic_from_imm64 _ st (by decide),ctor_imm_logic_eq ctx st.base w kk]
  cases immLogicOf? w kk <;> rfl

def logicalImmEnv (left : Bool) (k w x y : Nat) (kk : Int) (imm : ImmLogic) : Isle.Interp.Env V :=
  if left then env5 (.data 59 k []) (.ty (.int w)) (.int kk) (.value y) (.op (.immLogic imm))
  else env5 (.data 59 k []) (.ty (.int w)) (.value x) (.int kk) (.op (.immLogic imm))
private theorem imm_match_run {p : Program} (hp : Data p) (ctx : Ctx) (left : Bool)
    {k w x y j : Nat} {kk : Int} {info : IInfo}
    (defined : ctx.defInst? (if left then x else y) = some j) (found : ctx.insts[j]? = some info)
    (data : info.data = .data 152 35 [.data 151 57 [],.int kk])
    (st : State) (tr : Array RuleId) (m : Nat) :
    (matchRule p (Stock.sem ctx) {} (m + 10) (if left then rule_inst_3923 else rule_inst_3920)
      [.data 59 k [],.ty (.int w),.value x,.value y]).run (st,tr) =
      .ok ((immLogicOf? w kk).map (logicalImmEnv left k w x y kk),st,tr) := by
  have extraction := ext_inst_data_value ctx st.base found
  rw [data] at extraction
  have definition := ext_def_inst_some ctx st.base defined
  have construct := imm_ctor ctx st w kk
  cases choice : immLogicOf? w kk <;> rw [choice] at construct
  all_goals
    cases hp
    cases left <;> simp only [Bool.false_eq_true,ite_false,ite_true] at definition <;>
      isel_eval [*,logicalImmEnv,rule_inst_3920,rule_inst_3923,stock_sem_extract,stock_sem_unData]

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

/-- Successful actual immediate matching derives its valid operand, typed
variable environment and unchanged complete state, using original source values. -/
theorem stock_logical_imm_match_receipts {p : Program} (hp : Data p)
    {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx) {fr : Clif.Frame} (dfg : DFGCons ctx fr)
    (left : Bool) {k x y m : Nat} {ty : Clif.Ty} (width : ty.width ≤ 64) {u : BitVec ty.width}
    (source : fr.getAs (if left then x else y) ty = .ok u)
    {st : State} {tr : Array RuleId} {env : Isle.Interp.Env V} {middle : State × Array RuleId}
    (matched : (matchRule p (Stock.sem ctx) {} (m + 10) (if left then rule_inst_3923 else rule_inst_3920)
      [.data 59 k [],.ty (.int ty.width),.value x,.value y]).run (st,tr) = .ok (some env,middle)) :
    ∃ imm, env = logicalImmEnv left k ty.width x y (imm64OfIconst ty u) imm ∧ middle = (st,tr) ∧
      imm.value = u.toNat ∧ ImmLogic.ofNat? imm.value (szOf ty.width) = some imm := by
  obtain ⟨j,info,ty',c,defined,found,original,value⟩ := stock_logical_constant_match_value hp inv dfg left source matched
  cases value
  have accepted := inv.instE j info _ found original
  have supported : eTy ty = true := by simpa [Compile.instE,Compile.tyE,eTy] using accepted
  have raw := inv.data j info _ found original
  have shape : info.data = .data 152 35 [.data 151 57 [],.int (imm64OfIconst ty u)] := by
    have expected : instData f (.iconst ty u) = .ok (.data 152 35 [.data 151 57 [],.int (imm64OfIconst ty u)]) := iconst_data supported
    exact Except.ok.inj (raw.symm.trans expected)
  rw [imm_match_run hp ctx left defined found shape st tr m] at matched
  cases choice : immLogicOf? ty.width (imm64OfIconst ty u) with
  | none => rw [choice] at matched; cases matched
  | some imm =>
    rw [choice] at matched
    simp only [Option.map_some,Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at matched
    obtain ⟨envEq,stateEq⟩ := matched
    obtain ⟨value,valid⟩ := immLogicOf_spec width choice
    exact ⟨imm,envEq.symm,stateEq.symm,value,valid⟩

private theorem shift_ctor (ctx : Ctx) (st : State) (w : Nat) (kk : Int) :
    (Stock.sem ctx).ctor T.lshl_from_imm64 [.ty (.int w),.int kk] st =
      match lshlOf? w kk with
      | some sh => .ok (.op (.shiftOpAndAmt sh),st)
      | none => .fail := by
  change Stock.externCtor ctx T.lshl_from_imm64 _ st = _
  rw [stock_ctor_baseOnly ctx T.lshl_from_imm64 _ st (by decide),ctor_lshl_from_imm64 ctx st.base w kk]
  cases lshlOf? w kk <;> rfl
def logicalShiftEnv (left : Bool) (k w x y z : Nat) (kk : Int) (sh : ShiftOpAndAmt) : Isle.Interp.Env V :=
  if left then env6 (.data 59 k []) (.ty (.int w)) (.value z) (.int kk) (.value y) (.op (.shiftOpAndAmt sh))
  else env6 (.data 59 k []) (.ty (.int w)) (.value x) (.value z) (.int kk) (.op (.shiftOpAndAmt sh))
private theorem shift_match_run {p : Program} (hp : Data p) (ctx : Ctx) (left : Bool)
    {k w x y z b j1 j2 : Nat} {kk : Int} {info1 info2 : IInfo}
    (defined : ctx.defInst? (if left then x else y) = some j1) (found : ctx.insts[j1]? = some info1)
    (data : info1.data = .data 152 2 [.data 151 103 [],.values [z,b]])
    (constantDef : ctx.defInst? b = some j2) (constantFound : ctx.insts[j2]? = some info2)
    (constantData : info2.data = .data 152 35 [.data 151 57 [],.int kk])
    (st : State) (tr : Array RuleId) (m : Nat) :
    (matchRule p (Stock.sem ctx) {} (m + 10) (if left then rule_inst_3931 else rule_inst_3928)
      [.data 59 k [],.ty (.int w),.value x,.value y]).run (st,tr) =
      .ok ((lshlOf? w kk).map (logicalShiftEnv left k w x y z kk),st,tr) := by
  have extraction := ext_inst_data_value ctx st.base found
  rw [data] at extraction
  have constant := ext_inst_data_value ctx st.base constantFound
  rw [constantData] at constant
  have definition := ext_def_inst_some ctx st.base defined
  have constantDefinition := ext_def_inst_some ctx st.base constantDef
  have construct := shift_ctor ctx st w kk
  cases choice : lshlOf? w kk <;> rw [choice] at construct
  all_goals
    cases hp
    cases left <;> simp only [Bool.false_eq_true,ite_false,ite_true] at definition <;>
      isel_eval [*,logicalShiftEnv,rule_inst_3928,rule_inst_3931,stock_sem_extract,stock_sem_unData,ext_value_array_2]

/-- Successful shift matching supplies its typed environment and valid LSL
operand, whose bounded amount computes the held original source value. -/
theorem stock_logical_shift_match_receipts {p : Program} (hp : Data p)
    {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx) {fr : Clif.Frame} (dfg : DFGCons ctx fr)
    (left : Bool) {k x y m : Nat} {ty : Clif.Ty} (width : ty.width ≤ 64) {v : BitVec ty.width}
    (source : fr.getAs (if left then x else y) ty = .ok v)
    {st : State} {tr : Array RuleId} {env : Isle.Interp.Env V} {middle : State × Array RuleId}
    (matched : (matchRule p (Stock.sem ctx) {} (m + 10) (if left then rule_inst_3931 else rule_inst_3928)
      [.data 59 k [],.ty (.int ty.width),.value x,.value y]).run (st,tr) = .ok (some env,middle)) :
    ∃ (z : Nat) (kk : Int) (sh : ShiftOpAndAmt) (u : BitVec ty.width),
      env = logicalShiftEnv left k ty.width x y z kk sh ∧ middle = (st,tr) ∧ fr.getAs z ty = .ok u ∧
      sh.op = .lsl ∧ sh.amt < ty.width ∧ v = u <<< sh.amt := by
  obtain ⟨z,b,j1,j2,info1,info2,ty1,ty3,c,previous,defined,found,original,constantDef,constantFound,
    constantClif,supported,_,_⟩ := stock_logical_shift_match_value hp inv dfg left source matched
  have accepted := inv.instE j1 info1 _ found original
  have shiftSupported : eTy ty1 = true := by simpa [Compile.instE,Compile.binaryE,Compile.tyE,eTy] using accepted
  have raw := inv.data j1 info1 _ found original
  have rawConstant := inv.data j2 info2 _ constantFound constantClif
  have shape : info1.data = .data 152 2 [.data 151 103 [],.values [z,b]] :=
    Except.ok.inj (raw.symm.trans (ishl_data shiftSupported))
  have constantShape : info2.data = .data 152 35 [.data 151 57 [],.int (imm64OfIconst ty3 c)] :=
    Except.ok.inj (rawConstant.symm.trans (iconst_data supported))
  rw [shift_match_run hp ctx left defined found shape constantDef constantFound constantShape st tr m] at matched
  cases choice : lshlOf? ty.width (imm64OfIconst ty3 c) with
  | none => rw [choice] at matched; cases matched
  | some sh =>
    rw [choice] at matched
    simp only [Option.map_some,Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at matched
    obtain ⟨envEq,stateEq⟩ := matched
    obtain ⟨u,getSource,lsl,bounded,value⟩ := ishl_const_value dfg width defined found original
      constantDef constantFound constantClif supported source choice
    exact ⟨z,imm64OfIconst ty3 c,sh,u,envEq.symm,stateEq.symm,getSource,lsl,bounded,value⟩

private def constantFunction : Clif.Function := {
  name := "logical_constant_match"
  sig := {params := [⟨.i64,.none,.normal⟩],returns := [⟨.i64,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,.i64)],body := [⟨[31],.iconst .i64 255⟩,⟨[100],.binary .bor .i64 7 31⟩],term := .ret [100]}] }
private def constantBuilt : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx constantFunction).toOption.getD (sinkCtx,#[],sinkState)
private theorem constantScope : LowerScope constantFunction := lowerScope_of (by decide +kernel)
private theorem constantBuild : Stock.buildCtx constantFunction = .ok constantBuilt := by rfl
private theorem constantInv : MappedCtxInv constantFunction constantBuilt.1 :=
  buildCtx_mappedInv constantScope constantBuild
private def constantFrame : Clif.Frame := {
  func := constantFunction
  regs := fun x => if x = 31 then some (.ofInt .i64 255) else if x = 7 then some (.ofInt .i64 7) else none
  slots := [],body := [],term := .ret [100] }
private theorem constantDFG : DFGCons constantBuilt.1 constantFrame := by
  constructor
  · intro x j info cl v defined found original pure lookup
    by_cases hx : x = 31
    · subst x
      change some 0 = some j at defined
      cases defined
      have atZero : constantBuilt.1.insts[0]? = some constantBuilt.1.insts[0]! := rfl
      rw [atZero] at found
      cases found
      change some (.iconst .i64 255) = some cl at original
      cases original
      change some (.ofInt .i64 255) = some v at lookup
      cases lookup
      refine ⟨[.ofInt .i64 255], ?_, ?_⟩
      · intro cm; rfl
      · rfl
    · by_cases leaf : x = 7
      · subst x
        change none = some j at defined
        cases defined
      · simp [constantFrame,hx,leaf] at lookup
  · intro x t v typed lookup
    by_cases hx : x = 31
    · subst x
      change some (.int 64) = some t at typed
      cases typed
      change some (.ofInt .i64 255) = some v at lookup
      cases lookup
      rfl
    · by_cases leaf : x = 7
      · subst x
        change some (.int 64) = some t at typed
        cases typed
        change some (.ofInt .i64 7) = some v at lookup
        cases lookup
        rfl
      · simp [constantFrame,hx,leaf] at lookup

attribute [local semireducible] Isle.Aarch64.program
/-- Both immediate sides inhabit a real mapped source context and original DFG:
source31 is a held iconst255, mapped193; actual matches expose that definition. -/
theorem stock_logical_constant_match_witness (left : Bool) :
    ∃ (env : Isle.Interp.Env V) (middle : State × Array RuleId) (j : Nat) (info : IInfo)
      (ty' : Clif.Ty) (c : BitVec ty'.width),
      MappedCtxInv constantFunction constantBuilt.1 ∧ DFGCons constantBuilt.1 constantFrame ∧
      constantBuilt.1.valueReg? 31 = some (.vreg 193 .int) ∧
      (matchRule program (Stock.sem constantBuilt.1) {} 10
        (if left then rule_inst_3923 else rule_inst_3920)
        [.data 59 2 [],.ty (.int 64),.value (if left then 31 else 7),.value (if left then 7 else 31)]).run
          (constantBuilt.2.2,#[]) = .ok (some env,middle) ∧
      constantBuilt.1.defInst? 31 = some j ∧ constantBuilt.1.insts[j]? = some info ∧
      info.clif = some (.iconst ty' c) ∧ (Clif.Val.ofInt .i64 255) = ⟨ty',c⟩ := by
  have observed : ((matchRule program (Stock.sem constantBuilt.1) {} 10
      (if left then rule_inst_3923 else rule_inst_3920)
      [.data 59 2 [],.ty (.int 64),.value (if left then 31 else 7),.value (if left then 7 else 31)]).run
        (constantBuilt.2.2,#[])).toOption.any (fun result => result.1.isSome) = true := by
    cases left <;> decide +kernel
  cases run : (matchRule program (Stock.sem constantBuilt.1) {} 10
      (if left then rule_inst_3923 else rule_inst_3920)
      [.data 59 2 [],.ty (.int 64),.value (if left then 31 else 7),.value (if left then 7 else 31)]).run
        (constantBuilt.2.2,#[]) with
  | error err => simp [run,Except.toOption] at observed
  | ok result =>
    obtain ⟨out,middle⟩ := result
    cases out with
    | none => simp [run,Except.toOption] at observed
    | some env =>
      have source : constantFrame.getAs (if left then (if left then 31 else 7) else (if left then 7 else 31)) .i64 =
          .ok (BitVec.ofInt 64 255) := by cases left <;> rfl
      obtain ⟨j,info,ty',c,defined,found,original,value⟩ := stock_logical_constant_match_value
        data_program constantInv constantDFG left source (m := 0) run
      have same : (if left then (if left then 31 else 7) else (if left then 7 else 31)) = 31 := by cases left <;> rfl
      rw [same] at defined
      exact ⟨env,middle,j,info,ty',c,constantInv,constantDFG,rfl,rfl,defined,found,original,value⟩

/-- The typed immediate receipts are inhabited on both sides of the real
constant fixture, including its encoded operand and unchanged matching state. -/
theorem stock_logical_imm_receipts_witness (left : Bool) :
    ∃ (env : Isle.Interp.Env V) (middle : State × Array RuleId) (imm : ImmLogic),
      MappedCtxInv constantFunction constantBuilt.1 ∧ DFGCons constantBuilt.1 constantFrame ∧
      (matchRule program (Stock.sem constantBuilt.1) {} 10 (if left then rule_inst_3923 else rule_inst_3920)
        [.data 59 2 [],.ty (.int 64),.value (if left then 31 else 7),.value (if left then 7 else 31)]).run
          (constantBuilt.2.2,#[]) = .ok (some env,middle) ∧
      env = logicalImmEnv left 2 64 (if left then 31 else 7) (if left then 7 else 31) 255 imm ∧
      middle = (constantBuilt.2.2,#[]) ∧ imm.value = 255 ∧ ImmLogic.ofNat? imm.value .size64 = some imm := by
  obtain ⟨env,middle,j,info,ty',c,inv,dfg,mapped,matched,defined,found,original,value⟩ :=
    stock_logical_constant_match_witness left
  have source : constantFrame.getAs (if left then (if left then 31 else 7) else (if left then 7 else 31)) .i64 =
      .ok (BitVec.ofInt 64 255) := by cases left <;> rfl
  obtain ⟨imm,envEq,stateEq,immValue,valid⟩ := stock_logical_imm_match_receipts
    data_program inv dfg left (by decide) source (m := 0) matched
  exact ⟨env,middle,imm,inv,dfg,matched,envEq,stateEq,immValue,valid⟩

private def shiftFunction : Clif.Function := {
  name := "logical_shift_match"
  sig := {params := [⟨.i64,.none,.normal⟩,⟨.i64,.none,.normal⟩],returns := [⟨.i64,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,.i64),(32,.i64)],body := [⟨[31],.iconst .i64 3⟩,
    ⟨[63],.binary .ishl .i64 7 31⟩,⟨[100],.binary .bor .i64 32 63⟩],term := .ret [100]}] }
private def shiftBuilt : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx shiftFunction).toOption.getD (sinkCtx,#[],sinkState)
private theorem shiftScope : LowerScope shiftFunction := lowerScope_of (by decide +kernel)
private theorem shiftBuild : Stock.buildCtx shiftFunction = .ok shiftBuilt := by rfl
private theorem shiftInv : MappedCtxInv shiftFunction shiftBuilt.1 := buildCtx_mappedInv shiftScope shiftBuild
private def shiftFrame : Clif.Frame := {
  func := shiftFunction
  regs := fun x => if x = 31 then some (.ofInt .i64 3) else if x = 63 then some (.ofInt .i64 56)
    else if x = 7 then some (.ofInt .i64 7) else if x = 32 then some (.ofInt .i64 5) else none
  slots := [],body := [],term := .ret [100] }
private theorem shiftDFG : DFGCons shiftBuilt.1 shiftFrame := by
  constructor
  · intro x j info cl v defined found original pure lookup
    by_cases hx : x = 31
    · subst x
      change some 0 = some j at defined
      cases defined
      have atZero : shiftBuilt.1.insts[0]? = some shiftBuilt.1.insts[0]! := rfl
      rw [atZero] at found
      cases found
      change some (.iconst .i64 3) = some cl at original
      cases original
      change some (.ofInt .i64 3) = some v at lookup
      cases lookup
      exact ⟨[.ofInt .i64 3],fun cm => rfl,rfl⟩
    · by_cases shifted : x = 63
      · subst x
        change some 1 = some j at defined
        cases defined
        have atOne : shiftBuilt.1.insts[1]? = some shiftBuilt.1.insts[1]! := rfl
        rw [atOne] at found
        cases found
        change some (.binary .ishl .i64 7 31) = some cl at original
        cases original
        change some (.ofInt .i64 56) = some v at lookup
        cases lookup
        exact ⟨[.ofInt .i64 56],fun cm => rfl,rfl⟩
      · by_cases leaf : x = 7 ∨ x = 32
        · rcases leaf with rfl | rfl
          all_goals change none = some j at defined; cases defined
        · simp only [not_or] at leaf
          simp [shiftFrame,hx,shifted,leaf.1,leaf.2] at lookup
  · intro x t v typed lookup
    by_cases present : x = 31 ∨ x = 63 ∨ x = 7 ∨ x = 32
    · rcases present with rfl | rfl | rfl | rfl
      all_goals
        change some (.int 64) = some t at typed
        cases typed
        cases lookup
        rfl
    · simp only [not_or] at present
      simp [shiftFrame,present.1,present.2.1,present.2.2.1,present.2.2.2] at lookup

/-- Actual shift-side matches inhabit both nested definitions and the held
source value56=7<<3 in a real sparse-ID mapped context and consistent frame. -/
theorem stock_logical_shift_match_witness (left : Bool) :
    ∃ (env : Isle.Interp.Env V) (middle : State × Array RuleId) (z b j1 j2 : Nat)
      (info1 info2 : IInfo) (ty1 ty3 : Clif.Ty) (c : BitVec ty3.width) (u : BitVec 64),
      MappedCtxInv shiftFunction shiftBuilt.1 ∧ DFGCons shiftBuilt.1 shiftFrame ∧
      shiftBuilt.1.valueReg? 63 = some (.vreg 195 .int) ∧
      (matchRule program (Stock.sem shiftBuilt.1) {} 10 (if left then rule_inst_3931 else rule_inst_3928)
        [.data 59 2 [],.ty (.int 64),.value (if left then 63 else 32),.value (if left then 32 else 63)]).run
          (shiftBuilt.2.2,#[]) = .ok (some env,middle) ∧
      shiftBuilt.1.defInst? 63 = some j1 ∧ shiftBuilt.1.insts[j1]? = some info1 ∧
      info1.clif = some (.binary .ishl ty1 z b) ∧ shiftBuilt.1.defInst? b = some j2 ∧
      shiftBuilt.1.insts[j2]? = some info2 ∧ info2.clif = some (.iconst ty3 c) ∧ eTy ty3 = true ∧
      shiftFrame.getAs z .i64 = .ok u ∧ (BitVec.ofNat 64 56) = Clif.Sem.ishl u c := by
  have observed : ((matchRule program (Stock.sem shiftBuilt.1) {} 10 (if left then rule_inst_3931 else rule_inst_3928)
      [.data 59 2 [],.ty (.int 64),.value (if left then 63 else 32),.value (if left then 32 else 63)]).run
        (shiftBuilt.2.2,#[])).toOption.any (fun result => result.1.isSome) = true := by cases left <;> decide +kernel
  cases run : (matchRule program (Stock.sem shiftBuilt.1) {} 10 (if left then rule_inst_3931 else rule_inst_3928)
      [.data 59 2 [],.ty (.int 64),.value (if left then 63 else 32),.value (if left then 32 else 63)]).run
        (shiftBuilt.2.2,#[]) with
  | error err => simp [run,Except.toOption] at observed
  | ok result =>
    obtain ⟨out,middle⟩ := result
    cases out with
    | none => simp [run,Except.toOption] at observed
    | some env =>
      have source : shiftFrame.getAs (if left then (if left then 63 else 32) else (if left then 32 else 63)) .i64 =
          .ok (BitVec.ofNat 64 56) := by cases left <;> rfl
      obtain ⟨z,b,j1,j2,info1,info2,ty1,ty3,c,u,defined,found,original,constantDef,constantFound,
        constantClif,supported,getSource,value⟩ := stock_logical_shift_match_value data_program shiftInv shiftDFG left
          source (m := 0) run
      have same : (if left then (if left then 63 else 32) else (if left then 32 else 63)) = 63 := by cases left <;> rfl
      rw [same] at defined
      exact ⟨env,middle,z,b,j1,j2,info1,info2,ty1,ty3,c,u,shiftInv,shiftDFG,rfl,rfl,
        defined,found,original,constantDef,constantFound,constantClif,supported,getSource,value⟩

/-- Both nested shift matches inhabit typed LSL3 receipts and source56=7<<3,
without caller-supplied shift operands, amounts or environments. -/
theorem stock_logical_shift_receipts_witness (left : Bool) :
    ∃ (env : Isle.Interp.Env V) (middle : State × Array RuleId) (z : Nat) (kk : Int)
      (sh : ShiftOpAndAmt) (u : BitVec 64),
      MappedCtxInv shiftFunction shiftBuilt.1 ∧ DFGCons shiftBuilt.1 shiftFrame ∧
      (matchRule program (Stock.sem shiftBuilt.1) {} 10 (if left then rule_inst_3931 else rule_inst_3928)
        [.data 59 2 [],.ty (.int 64),.value (if left then 63 else 32),.value (if left then 32 else 63)]).run
          (shiftBuilt.2.2,#[]) = .ok (some env,middle) ∧
      env = logicalShiftEnv left 2 64 (if left then 63 else 32) (if left then 32 else 63) z kk sh ∧
      middle = (shiftBuilt.2.2,#[]) ∧ shiftFrame.getAs z .i64 = .ok u ∧ sh.op = .lsl ∧ sh.amt < 64 ∧
      (BitVec.ofNat 64 56) = u <<< sh.amt := by
  obtain ⟨env,middle,z0,b,j1,j2,info1,info2,ty1,ty3,c,u0,inv,dfg,mapped,matched,
    defined,found,original,constantDef,constantFound,constantClif,supported,getSource,value⟩ :=
    stock_logical_shift_match_witness left
  have source : shiftFrame.getAs (if left then (if left then 63 else 32) else (if left then 32 else 63)) .i64 =
      .ok (BitVec.ofNat 64 56) := by cases left <;> rfl
  obtain ⟨z,kk,sh,u,envEq,stateEq,sourceEq,lsl,bounded,valueEq⟩ := stock_logical_shift_match_receipts
    data_program inv dfg left (by decide) source (m := 0) matched
  exact ⟨env,middle,z,kk,sh,u,inv,dfg,matched,envEq,stateEq,sourceEq,lsl,bounded,valueEq⟩

end Backend.Stock.Proof.LogicalSemantics
