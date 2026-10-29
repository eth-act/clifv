module

public import FV.Backend.Proof.StockShiftBitfieldHelper
public import FV.Backend.Proof.StockRequestSuccess
public import FV.Backend.Proof.StockShiftBitfieldMatch

@[expose] public section

namespace Backend.Stock.Proof.ShiftBitfield
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

private theorem bitfield_run {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) (st : LState) (tr : Array RuleId) (n : Nat)
    {ks w : Nat} {sz : OperandSize} {rid : RuleId}
    (hsz : ∀ st tr n, (applyTerm p (Backend.sem ctx) cfg (n+8) 93 305 [.ty (.int w)]).run (st,tr) =
      .ok (some (.data 93 ks []),st,tr.push rid))
    (width : w ≤ 64) (hs : OperandSize.ofIdx? ks = some sz) (op : BfmOp) (rn : Reg) (r s : Nat) :
    (applyTerm p (Backend.sem ctx) cfg (n+20) 27 418
      [.ty (.int w),.data 62 (bitfieldOpCode op) [],.reg rn,.op (.uimm6 r),.op (.uimm6 s)]).run (st,tr) =
      .ok (some (.reg (st.fresh .int).1),
        (st.fresh .int).2.emit (.bitfieldMove sz op (st.fresh .int).1 rn r s),
        (tr.push rid).push rule_inst_2999.id) := by
  have fresh := (ctor_temp_writable_reg_int_iff ctx st w _ _).mpr ⟨width,rfl,rfl⟩
  have decoded : (V.data 62 (bitfieldOpCode op) []).bfmOp? = some op := by cases op <;> rfl
  have emission := fun st rd => ctor_emit ctx st (ofV_bitfieldMove_fb hs decoded rd rn r s)
  cases hp
  isel_eval [*,rule_inst_2999,ctor_temp_writable_reg_i64,ctor_writable_reg_to_reg]

/-- The actual bitfield helper succeeds with a single fresh output while
preserving every Stock scheduling field. -/
theorem stock_bitfield_helper_run {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {w : Nat} (width : w ≤ 64)
    (op : BfmOp) (rn : Reg) (r s : Nat) (st : State) (tr : Array RuleId) (n : Nat) :
    (applyTerm p (Stock.sem ctx) cfg (n+20) 27 418
      [.ty (.int w),.data 62 (bitfieldOpCode op) [],.reg rn,.op (.uimm6 r),.op (.uimm6 s)]).run (st,tr) =
      .ok (some (.reg (st.base.fresh .int).1),
        {st with base := (st.base.fresh .int).2.emit (.bitfieldMove (szOf w) op (st.base.fresh .int).1 rn r s)},
        (tr.push (if w ≤ 32 then rule_inst_1592.id else rule_inst_1593.id)).push rule_inst_2999.id) := by
  by_cases small : w ≤ 32
  · have legacy := bitfield_run hp ctx hc st.base tr n
      (fun base trace fuel => operand_size_32 hp ctx hc base trace fuel small) (sz := .size32) width rfl op rn r s
    simpa only [szOf,small,ite_true] using stock_bitfield_pure_helper hp ctx hc (by decide) legacy
  · have legacy := bitfield_run hp ctx hc st.base tr n
      (fun base trace fuel => operand_size_64 hp ctx hc base trace fuel (by omega) width) (sz := .size64) width rfl op rn r s
    simpa only [szOf,small,ite_false] using stock_bitfield_pure_helper hp ctx hc (by decide) legacy

def fusedOp (signed : Bool) : BfmOp := if signed then .sBfm else .uBfm
def fusedCode (signed : Bool) (w : Nat) (d r : Reg) (a b : Int) : MInst :=
  .bitfieldMove (szOf w) (fusedOp signed) d r (bfmImmr w (u64 a) (u64 b))
    (w-1-Nat.land (u64 a % 256) (w-1))
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_mkData (ctx : Ctx) (t k : Nat) (vs : List V) :
    (Stock.sem ctx).mkData t k vs = .data t k vs := rfl
private theorem immr_run (ctx : Ctx) (st : State) (w : Nat) (a b : Int) :
    Stock.externCtor ctx T.bfm_immr [.ty (.int w),.int a,.int b] st =
      .ok (.op (.uimm6 (bfmImmr w (u64 a) (u64 b))),st) := by
  rw [stock_ctor_baseOnly ctx T.bfm_immr _ st (by decide)]
  rfl
private theorem imms_run (ctx : Ctx) (st : State) (w : Nat) (a b : Int) :
    Stock.externCtor ctx T.bfm_imms [.ty (.int w),.int a,.int b] st =
      .ok (.op (.uimm6 (w-1-Nat.land (u64 a % 256) (w-1))),st) := by
  rw [stock_ctor_baseOnly ctx T.bfm_imms _ st (by decide)]
  rfl
private theorem output_run {p : Program} (hp : Data p) (ctx : Ctx) (st : State) (tr : Array RuleId)
    (n : Nat) (r : Reg) :
    (applyTerm p (Stock.sem ctx) {} (n+10) 25 172 [.reg r]).run (st,tr) =
      .ok (some (.regsVec [[r]]),st,tr.push rule_prelude_lower_105.id) := by
  have value : ∀ q,Stock.externCtor ctx T.value_reg [.reg r] q = .ok (.regs [r],q) := by
    intro q; rw [stock_ctor_baseOnly ctx T.value_reg _ q (by decide)]; rfl
  have output : ∀ q,Stock.externCtor ctx T.output [.regs [r]] q = .ok (.regsVec [[r]],q) := by
    intro q; rw [stock_ctor_baseOnly ctx T.output _ q (by decide)]; rfl
  cases hp
  isel_eval [*,rule_prelude_lower_105,sem_ctor]

/-- Both fused RHSs request only the underlying source operand; counts and the
intermediate shift remain unmaterialized. The exact complete state is retained. -/
theorem stock_bitfield_rhs_run {p : Program} (hp : Data p) (ctx : Ctx) (signed : Bool)
    {w x : Nat} {r : Reg} (width : w ≤ 64) (mapped : ctx.valueReg? x = some r)
    (st : State) (safe : DemandAllowed ctx st x) (tr : Array RuleId) (n : Nat) (a b : Int) :
    ∃ trace,(evalExpr p (Stock.sem ctx) {} (n+40) (fusedRule signed).rhs (fusedEnv w x a b)).run (st,tr) =
      .ok (some (.regsVec [[(st.base.fresh .int).1]]),
        {st.mark x with base := (st.base.fresh .int).2.emit (fusedCode signed w (st.base.fresh .int).1 r a b)},trace) := by
  have request := stock_put_in_reg ctx st x r mapped safe
  have rotate := fun q => immr_run ctx q w a b
  have mask := fun q => imms_run ctx q w a b
  have helper := fun q trace fuel => stock_bitfield_helper_run hp ctx (cfg := {}) rfl width (fusedOp signed) r
    (bfmImmr w (u64 a) (u64 b)) (w-1-Nat.land (u64 a % 256) (w-1)) q trace fuel
  have output := fun q trace fuel rr => output_run hp ctx q trace fuel rr
  cases signed
  · simp only [fusedOp,bitfieldOpCode,Bool.false_eq_true,ite_false] at helper
    cases hp
    refine Exists.intro ?traceU ?proofU
    case proofU =>
      isel_eval [*,fusedRule,fusedEnv,fusedCode,fusedOp,bitfieldOpCode,rule_lower_1707,sem_ctor,sem_mkData]
      rfl
  · simp only [fusedOp,bitfieldOpCode,ite_true] at helper
    cases hp
    refine Exists.intro ?traceS ?proofS
    case proofS =>
      isel_eval [*,fusedRule,fusedEnv,fusedCode,fusedOp,bitfieldOpCode,rule_lower_1704,sem_ctor,sem_mkData]
      rfl

/-- Successful fused execution supplies its guarded request internally. -/
theorem stock_bitfield_rhs_observed {p : Program} (hp : Data p) (ctx : Ctx) (signed : Bool)
    {w x n : Nat} {a b : Int} (width : w ≤ 64)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+40) (fusedRule signed).rhs (fusedEnv w x a b)).run
      (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st x ∧ ∃ r,ctx.valueReg? x = some r ∧
      out = .regsVec [[(st.base.fresh .int).1]] ∧
      next = {st.mark x with base := (st.base.fresh .int).2.emit (fusedCode signed w (st.base.fresh .int).1 r a b)} := by
  cases called : Stock.externCtor ctx T.put_in_reg [.value x] st with
  | fail =>
    have denied : (evalExpr p (Stock.sem ctx) {} (n+40) (fusedRule signed).rhs (fusedEnv w x a b)).run
        (st,tr) ≠ .ok (some out,next,trace) := by
      cases signed <;> cases hp <;> isel_eval [*,fusedRule,fusedEnv,rule_lower_1704,rule_lower_1707,sem_ctor,sem_mkData]
      all_goals intro impossible; cases impossible
    exact False.elim (denied run)
  | unmodeled err =>
    have denied : (evalExpr p (Stock.sem ctx) {} (n+40) (fusedRule signed).rhs (fusedEnv w x a b)).run
        (st,tr) ≠ .ok (some out,next,trace) := by
      cases signed <;> cases hp <;> isel_eval [*,fusedRule,fusedEnv,rule_lower_1704,rule_lower_1707,sem_ctor,sem_mkData]
      all_goals intro impossible; cases impossible
    exact False.elim (denied run)
  | ok pair =>
    obtain ⟨value,after⟩ := pair
    obtain ⟨safe,r,mapped,_,_⟩ := (stock_put_in_reg_iff ctx st x value after).mp called
    obtain ⟨trace',expected⟩ := stock_bitfield_rhs_run hp ctx signed width mapped st safe tr n a b
    have same := Except.ok.inj (run.symm.trans expected)
    exact ⟨safe,r,mapped,Option.some.inj (congrArg Prod.fst same),congrArg (fun q => q.2.1) same⟩
end Backend.Stock.Proof.ShiftBitfield
