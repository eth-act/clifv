import FV.Backend.Proof.IselFamALUA
import FV.Backend.Proof.StockSourceView
import FV.Backend.Proof.IselCovForm
import FV.Backend.Proof.StockRequestSuccess
import FV.Backend.Proof.StockRotateMatch
namespace Backend.Stock.Proof.ScalarRotate
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem sem_unData (ctx : Ctx) (t : Nat) (v : V) :
    (Stock.sem ctx).unData t v = (Backend.sem ctx).unData t v := rfl
private theorem sem_eq (ctx : Ctx) (a b : V) : (Stock.sem ctx).eq a b = (a == b) := rfl
private theorem sem_prim (ctx : Ctx) (name : String) :
    (Stock.sem ctx).prim 14 name = (CTy.ofName? name).map V.ty := rfl
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem shift_ctor (ctx : Ctx) (st : State) {w : Nat} (width : IW w) (c : Int) :
    Stock.externCtor ctx T.imm_shift_from_imm64 [.ty (.int w),.int c] st =
      .ok (.op (.immShift (Nat.land (u64 c) (w-1))),st) := by
  rw [stock_ctor_baseOnly ctx T.imm_shift_from_imm64 _ st (by decide),
    ctor_imm_shift_from_imm64 ctx st.base width.pos width.le c]
def rotateImmediateEnv (w x : Nat) (c : Int) (amount : Nat) : Isle.Interp.Env V :=
  if w = 8 ∨ w = 16 then env4 (.ty (.int w)) (.value x) (.int c) (.op (.immShift amount))
  else env3 (.value x) (.int c) (.op (.immShift amount))
/-- All six immediate root matches follow the actual original count definition
and normalize its width mask without requesting a machine count register. -/
theorem stock_rotate_immediate_match {p : Program} (hp : Data p) (ctx : Ctx) (left : Bool)
    {i x y j w : Nat} {info literal : IInfo} {c : Int} (width : IW w)
    (source : ctx.insts[i]? = some info) (type : info.resTys.head? = some (.int w))
    (data : info.data = .data 152 2 [.data 151 (rotateOpcode left) [],.values [x,y]])
    (defined : ctx.defInst? y = some j) (found : ctx.insts[j]? = some literal)
    (constant : literal.data = .data 152 35 [.data 151 57 [],.int c])
    (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+20) (rotateRule left true w) [.inst i]).run (st,tr) =
      .ok (some (rotateImmediateEnv w x c (Nat.land (u64 c) (w-1))),st,tr) := by
  have extraction := ext_inst_data_value ctx st.base source
  rw [data,type,Option.getD_some] at extraction
  have values := ext_value_array_2 ctx st.base x y
  have fits := ext_fits_in_16 ctx st.base w
  have definition := ext_def_inst_some ctx st.base defined
  have instruction := ext_inst_data_value ctx st.base found
  rw [constant] at instruction
  have constructor := shift_ctor ctx st width c
  cases hp
  cases left <;> rcases width with rfl | rfl | rfl | rfl
  all_goals simp only [rotateRule,rotateOpcode,rotateImmediateEnv,rotateNarrowRule,
    rotateWideImmRule,Bool.false_eq_true,Nat.reduceEqDiff,ite_true,ite_false,
    false_or,or_true,or_false] at extraction ⊢
  all_goals isel_eval [*,rule_lower_1778,rule_lower_1852,rule_lower_1803,rule_lower_1808,
    rule_lower_1857,rule_lower_1862,sem_extract,sem_unData,sem_eq,sem_prim,sem_ctor]
private def literalPattern (slot : Nat) : Pattern :=
  .term 15 1 [.term 18 209 [.wildcard 14,
    .term 152 2482 [.term 151 2341 [],.bind 134 slot (.wildcard 134)]]]
private theorem literal_pattern {p : Program} (hp : Data p) (ctx : Ctx)
    {r : Rule} {tp xp : Pattern} {op slot i x y : Nat} {info : IInfo}
    (argsShape : r.args = [.term 18 209 [tp,.term 152 2449
      [.term 151 op [],.term 147 1614 [xp,literalPattern slot]]]])
    (source : ctx.insts[i]? = some info)
    {code : Nat} (data : info.data = .data 152 2 [.data 151 code [],.values [x,y]])
    {n : Nat} {st : State} {tr : Array RuleId} {env : Isle.Interp.Env V} {middle : State × Array RuleId}
    (matched : (matchRule p (Stock.sem ctx) {} (n+20) r [.inst i]).run (st,tr) = .ok (some env,middle)) :
    ∃ e0 e1,matchPat p (Backend.sem ctx) st.base (literalPattern slot) (.value y) e0 = .ok (some e1) := by
  obtain ⟨initial,args,_⟩ := matchRule_some_inv matched
  rw [stock_matchArgs,argsShape] at args
  obtain ⟨e1,root,_⟩ := matchArgs_cons_inv args
  obtain ⟨fields,extracted,patterns⟩ := matchPat_extract_inv hp.t209 term_209_kind rfl root
  rw [Backend.Proof.sem_extract,ext_inst_data_value ctx st.base source,data] at extracted
  cases extracted
  obtain ⟨e2,_,tail⟩ := matchArgs_cons_inv patterns
  obtain ⟨e3,binary,_⟩ := matchArgs_cons_inv tail
  obtain ⟨fs,decoded,matchedFields⟩ := matchPat_enum_inv hp.t2449 term_2449_kind binary
  have decode : (Backend.sem ctx).unData 152 (.data 152 2 [.data 151 code [],.values [x,y]]) =
      some (2,[.data 151 code [],.values [x,y]]) := rfl
  rw [decode] at decoded
  cases decoded
  obtain ⟨e4,_,values⟩ := matchArgs_cons_inv matchedFields
  obtain ⟨e5,_,constant⟩ := values2_match_inv hp ctx values
  exact ⟨e5,e3,constant⟩
private def typePattern (w : Nat) : Pattern :=
  if w = 8 ∨ w = 16 then .term 14 110 [.bind 14 0 (.wildcard 14)]
  else .constPrim 14 (if w = 64 then "I64" else "I32")
private def valuePattern (w : Nat) : Pattern := .bind 15 (if w = 8 ∨ w = 16 then 1 else 0) (.wildcard 15)
private def constantSlot (w : Nat) : Nat := if w = 8 ∨ w = 16 then 2 else 1
/-- An actual successful rotation immediate match identifies an original
constant definition and its value via unchanged source-frame DFG semantics.
Its normalized count and canonical environment are derived internally. -/
theorem stock_rotate_immediate_receipts {p : Program} (hp : Data p)
    {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx) (left : Bool)
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {i x y w n : Nat} {info : IInfo}
    (width : IW w) (source : ctx.insts[i]? = some info) (type : info.resTys.head? = some (.int w))
    (data : info.data = .data 152 2 [.data 151 (rotateOpcode left) [],.values [x,y]])
    {amount : Clif.Val} (getY : fr.regs y = some amount)
    {st : State} {tr : Array RuleId} {env : Isle.Interp.Env V} {middle : State × Array RuleId}
    (matched : (matchRule p (Stock.sem ctx) {} (n+20) (rotateRule left true w) [.inst i]).run (st,tr) = .ok (some env,middle)) :
    ∃ (j : Nat) (literal : IInfo) (ty : Clif.Ty) (bits : BitVec ty.width) (c : Int) (count : Nat),
      ctx.defInst? y = some j ∧ ctx.insts[j]? = some literal ∧ literal.clif = some (.iconst ty bits) ∧
      amount = ⟨ty,bits⟩ ∧ env = rotateImmediateEnv w x c count ∧ middle = (st,tr) ∧
      count = amount.bits.toNat % w ∧ count < w := by
  have argsShape : (rotateRule left true w).args = [.term 18 209 [typePattern w,.term 152 2449
      [.term 151 (if left then 2385 else 2386) [],.term 147 1614 [valuePattern w,literalPattern (constantSlot w)]]]] := by
    cases left <;> rcases width with rfl | rfl | rfl | rfl <;>
      simp [rotateRule,rotateNarrowRule,rotateWideImmRule,typePattern,valuePattern,literalPattern,constantSlot] <;> rfl
  obtain ⟨e0,e1,pattern⟩ := literal_pattern hp ctx argsShape source data matched
  obtain ⟨j,literal,fs,defined,found,encoded⟩ := defInst_iconst_inv hp ctx pattern
  obtain ⟨original,clif,raw⟩ := ctxInv_clif inv.identityView defined found
  rw [encoded] at raw
  obtain ⟨ty,bits,rfl,rfl⟩ := instData_iconst_inv raw
  have supported := instData_iconst_eTy raw
  have value := dfg_iconst_fb dfg defined found clif getY
  have countEq : Nat.land (u64 (imm64OfIconst ty bits)) (w-1) = bits.toNat % w := by
    rw [u64_imm64OfIconst_fb (eTy_width supported) bits,land_mask_mod width]
  rw [stock_rotate_immediate_match hp ctx left width source type data defined found encoded st tr n] at matched
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at matched
  refine ⟨j,literal,ty,bits,imm64OfIconst ty bits,_,defined,found,clif,value,matched.1.symm,matched.2.symm,?_,?_⟩
  · rw [value]; exact countEq
  · rw [countEq]; exact Nat.mod_lt _ width.pos
/-- Successful wide immediate execution derives the guarded mapped data
request internally; it does not require the looked-through count register. -/
theorem stock_rotate_wide_immediate_requests {p : Program} (hp : Data p) (ctx : Ctx)
    (left wide : Bool) {x n amount : Nat} {constant : Int}
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+50) (rotateWideImmRule left wide).rhs
      (env3 (.value x) (.int constant) (.op (.immShift amount)))).run (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st x ∧ ∃ rx,ctx.valueReg? x = some rx := by
  cases request : Stock.externCtor ctx T.put_in_reg [.value x] st with
  | fail =>
    have denied : (evalExpr p (Stock.sem ctx) {} (n+50) (rotateWideImmRule left wide).rhs
        (env3 (.value x) (.int constant) (.op (.immShift amount)))).run (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      cases left <;> cases wide
      all_goals isel_eval [*,rotateWideImmRule,rule_lower_1803,rule_lower_1808,
        rule_lower_1857,rule_lower_1862,sem_ctor,sem_prim]
      all_goals intro impossible; cases impossible
    exact False.elim (denied run)
  | unmodeled err =>
    have denied : (evalExpr p (Stock.sem ctx) {} (n+50) (rotateWideImmRule left wide).rhs
        (env3 (.value x) (.int constant) (.op (.immShift amount)))).run (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      cases left <;> cases wide
      all_goals isel_eval [*,rotateWideImmRule,rule_lower_1803,rule_lower_1808,
        rule_lower_1857,rule_lower_1862,sem_ctor,sem_prim]
      all_goals intro impossible; cases impossible
    exact False.elim (denied run)
  | ok pair =>
    obtain ⟨v,q⟩ := pair
    obtain ⟨safe,rx,mapped,_,_⟩ := (stock_put_in_reg_iff ctx st x v q).mp request
    exact ⟨safe,rx,mapped⟩
end Backend.Stock.Proof.ScalarRotate
