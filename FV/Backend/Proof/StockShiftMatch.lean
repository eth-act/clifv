import FV.Backend.Proof.IselFamALUA
import FV.Backend.Proof.IselFamAluBShiftTerms
import FV.Backend.Proof.StockSourceView
import FV.Backend.Proof.StockShiftRhs
namespace Backend.Stock.Proof.ScalarShift
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem sem_unData (ctx : Ctx) (t : Nat) (v : V) :
    (Stock.sem ctx).unData t v = (Backend.sem ctx).unData t v := rfl
private theorem sem_eq (ctx : Ctx) (a b : V) : (Stock.sem ctx).eq a b = (a == b) := rfl
private theorem sem_prim_type (ctx : Ctx) (name : String) :
    (Stock.sem ctx).prim 14 name = (CTy.ofName? name).map V.ty := rfl
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem shift_ctor (ctx : Ctx) (st : State) {w : Nat}
    (pos : 0 < w) (width : w ≤ 64) (c : Int) :
    Stock.externCtor ctx T.imm_shift_from_imm64 [.ty (.int w),.int c] st =
      .ok (.op (.immShift (Nat.land (u64 c) (w-1))),st) := by
  rw [stock_ctor_baseOnly ctx T.imm_shift_from_imm64 _ st (by decide),
    ctor_imm_shift_from_imm64 ctx st.base pos width c]

/-- The actual immediate match preserves the full state and chooses the
original width mask without requesting the looked-through count register. -/
theorem stock_shift_imm_match {p : Program} (hp : Data p) (ctx : Ctx)
    {k w y j : Nat} {a : Reg} {info : IInfo} {c : Int} (width : IW w)
    (defined : ctx.defInst? y = some j) (found : ctx.insts[j]? = some info)
    (data : info.data = .data 152 35 [.data 151 57 [],.int c])
    (st : State) (tr : Array RuleId) (m : Nat) :
    (matchRule p (Stock.sem ctx) {} (m+10) rule_lower_1631 (shiftArgs k w a y)).run (st,tr) =
      .ok (some (env5 (.data 59 k []) (.ty (.int w)) (.reg a) (.int c)
        (.op (.immShift (Nat.land (u64 c) (w-1))))),st,tr) := by
  have definition := ext_def_inst_some ctx st.base defined
  have instruction := ext_inst_data_value ctx st.base found
  rw [data] at instruction
  have constructor := shift_ctor ctx st width.pos width.le c
  cases hp
  isel_eval [*,rule_lower_1631,sem_extract,sem_unData,sem_ctor]

/-- A successful actual immediate match exposes a real original count
constant and its DFG value, independently of its register materialization. -/
theorem stock_shift_imm_match_receipts {p : Program} (hp : Data p)
    {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {k w y m : Nat} {a : Reg}
    (width : IW w) {amount : Clif.Val} (source : fr.regs y = some amount)
    {st : State} {tr : Array RuleId} {env : Isle.Interp.Env V} {middle : State × Array RuleId}
    (matched : (matchRule p (Stock.sem ctx) {} (m+10) rule_lower_1631 (shiftArgs k w a y)).run
      (st,tr) = .ok (some env,middle)) :
    ∃ (c : Int) (shift : Nat),
      env = env5 (.data 59 k []) (.ty (.int w)) (.reg a) (.int c) (.op (.immShift shift)) ∧
      middle = (st,tr) ∧ shift = amount.bits.toNat % w ∧ shift < (szOf w).bits := by
  obtain ⟨env0,args,_⟩ := matchRule_some_inv matched
  obtain ⟨e1,_,args⟩ := matchArgs_cons_inv args
  obtain ⟨e2,_,args⟩ := matchArgs_cons_inv args
  obtain ⟨e3,_,args⟩ := matchArgs_cons_inv args
  obtain ⟨e4,pattern,_⟩ := matchArgs_cons_inv args
  rw [stock_matchPat] at pattern
  obtain ⟨j,info,fs,defined,found,data⟩ := defInst_iconst_inv hp ctx pattern
  obtain ⟨original,clif,raw⟩ := ctxInv_clif inv.identityView defined found
  rw [data] at raw
  obtain ⟨ty,c,rfl,rfl⟩ := instData_iconst_inv raw
  have supported := instData_iconst_eTy raw
  have value := dfg_iconst_fb dfg defined found clif source
  subst value
  rw [stock_shift_imm_match hp ctx width defined found data st tr m] at matched
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at matched
  have bits := u64_imm64OfIconst_fb (eTy_width supported) c
  have shiftEq : Nat.land (u64 (imm64OfIconst ty c)) (w-1) = c.toNat % w := by
    rw [bits,land_mask_mod width]
  refine ⟨imm64OfIconst ty c,_,matched.1.symm,matched.2.symm,shiftEq,?_⟩
  rw [shiftEq]
  exact Nat.lt_of_lt_of_le (Nat.mod_lt _ width.pos) (szOf_bits width.le)

/-- Successful register-count matching determines its real width, canonical
mapped-request environment and unchanged complete state. -/
theorem stock_shift_rrr_match_receipts {p : Program} (hp : Data p) (ctx : Ctx) (wide : Bool)
    {k w y m : Nat} {a : Reg} {st : State} {tr : Array RuleId}
    {env : Isle.Interp.Env V} {middle : State × Array RuleId}
    (matched : (matchRule p (Stock.sem ctx) {} (m+10) (shiftRegisterRule wide) (shiftArgs k w a y)).run
      (st,tr) = .ok (some env,middle)) :
    w = shiftWidth wide ∧ env = env3 (.data 59 k []) (.reg a) (.value y) ∧ middle = (st,tr) := by
  cases hp
  cases wide
  · isel_inv [*,shiftArgs,shiftRegisterRule,rule_lower_1622,sem_eq,sem_prim_type] at matched
    all_goals isel_destruct <;> subst_vars
    exact CTy.int.inj (show CTy.int w = CTy.int 32 from ‹_›)
  · isel_inv [*,shiftArgs,shiftRegisterRule,rule_lower_1623,sem_eq,sem_prim_type] at matched
    all_goals isel_destruct <;> subst_vars
    exact CTy.int.inj (show CTy.int w = CTy.int 64 from ‹_›)

/-- Successful narrow matching determines the8/16-bit case and reserves both
empty local slots in the actual interpreter environment. -/
theorem stock_shift_mask_match_receipts {p : Program} (hp : Data p) (ctx : Ctx)
    {k w y m : Nat} {a : Reg} (width : IW w) {st : State} {tr : Array RuleId}
    {env : Isle.Interp.Env V} {middle : State × Array RuleId}
    (matched : (matchRule p (Stock.sem ctx) {} (m+10) rule_lower_1612 (shiftArgs k w a y)).run
      (st,tr) = .ok (some env,middle)) :
    (w = 8 ∨ w = 16) ∧ env = shiftMaskEnv k w a y ∧ middle = (st,tr) := by
  cases hp
  isel_inv [*,shiftArgs,rule_lower_1612,sem_extract,ext_fits_in_16] at matched
  all_goals isel_destruct <;> subst_vars
  rcases width with rfl | rfl | rfl | rfl <;> simp_all [CTy.bits]
end Backend.Stock.Proof.ScalarShift
