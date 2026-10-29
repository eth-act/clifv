module

public import FV.Backend.Proof.StockBmaskNarrow
public import FV.Backend.Proof.StockShiftRequests

@[expose] public section

namespace Backend.Stock.Proof.ScalarMask
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

def bmaskResult (st : LState) (wi : Nat) (r : Reg) : Reg :=
  if wi ≤ 16 then ((bmaskMaskedBase st wi r).fresh .int).1 else (st.fresh .int).1

def bmaskBase (st : LState) (wi : Nat) (r : Reg) : LState :=
  if wi ≤ 16 then bmaskNarrowBase st wi r else
    ((st.fresh .int).2.emit (.aluRRImm12 .subS (szOf wi) .xzr r ⟨0,false⟩)).emit
      (.csetm (st.fresh .int).1 .ne)

def bmaskTrace (wi : Nat) (tr : Array RuleId) : Array RuleId :=
  if wi ≤ 16 then bmaskNarrowTrace tr else bmaskWideTrace (szOf wi) tr

/-- The actual helper runs for all original independent input/output widths.
No result register, emission receipt or successful-run premise is supplied. -/
theorem stock_bmask_run {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {wo wi : Nat} (output : wo ≤ 64)
    (input : wi = 8 ∨ wi = 16 ∨ wi = 32 ∨ wi = 64)
    (r : Reg) (st : State) (tr : Array RuleId) (n : Nat) :
    (applyTerm p (Stock.sem ctx) cfg (n+400) 22 658
      [.ty (.int wo),.ty (.int wi),.regs [r]]).run (st,tr) =
      .ok (some (.regs [bmaskResult st.base wi r]),
        {st with base := bmaskBase st.base wi r},bmaskTrace wi tr) := by
  rcases input with rfl | rfl | rfl | rfl
  · simpa only [bmaskResult,bmaskBase,bmaskTrace,show 8 ≤ 16 by decide,ite_true] using
      stock_bmask_narrow hp ctx hc output (.inl rfl) r st tr n
  · simpa only [bmaskResult,bmaskBase,bmaskTrace,show 16 ≤ 16 by decide,ite_true] using
      stock_bmask_narrow hp ctx hc output (.inr rfl) r st tr n
  · simpa only [bmaskResult,bmaskBase,bmaskTrace,show ¬32 ≤ 16 by decide,ite_false,
      szOf,show 32 ≤ 32 by decide,ite_true,
      OperandSize.bits,Nat.add_assoc] using
      stock_bmask_wide hp ctx hc output .size32 r st tr (n+220)
  · simpa only [bmaskResult,bmaskBase,bmaskTrace,show ¬64 ≤ 16 by decide,ite_false,
      szOf,show ¬64 ≤ 32 by decide,OperandSize.bits,Nat.add_assoc] using
      stock_bmask_wide hp ctx hc output .size64 r st tr (n+220)

private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl

/-- The real root RHS requests its original operand through Stock's demand
guard, executes `lower_bmask`, and returns its actual output register. -/
theorem stock_bmask_rhs {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {wo wi x : Nat} (output : wo ≤ 64)
    (input : wi = 8 ∨ wi = 16 ∨ wi = 32 ∨ wi = 64) {r : Reg}
    (mapped : ctx.valueReg? x = some r) (st : State) (safe : DemandAllowed ctx st x)
    (tr : Array RuleId) (n : Nat) :
    (evalExpr p (Stock.sem ctx) cfg (n+420) rule_lower_2052.rhs
      (env3 (.ty (.int wo)) (.ty (.int wi)) (.value x))).run (st,tr) =
      .ok (some (.regsVec [[bmaskResult st.base wi r]]),
        {st.mark x with base := bmaskBase st.base wi r},bmaskTrace wi tr) := by
  have request := stock_put_in_regs ctx st x r mapped safe
  have lower := fun q trace fuel => stock_bmask_run hp ctx hc output input r q trace fuel
  have outputValue : ∀ (q : State) (rd : Reg),Stock.externCtor ctx T.output [.regs [rd]] q =
      .ok (.regsVec [[rd]],q) := by
    intro q rd; rw [stock_ctor_baseOnly ctx T.output _ q (by decide)]; rfl
  cases hp
  isel_eval [*,rule_lower_2052,sem_ctor]
  rfl

/-- Successful RHS execution derives its own original demand guard, register
mapping, result and full state; safety is not a separate caller certificate. -/
theorem stock_bmask_rhs_observed {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {wo wi x n : Nat} (output : wo ≤ 64)
    (input : wi = 8 ∨ wi = 16 ∨ wi = 32 ∨ wi = 64)
    {st next : State} {before trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) cfg (n+420) rule_lower_2052.rhs
      (env3 (.ty (.int wo)) (.ty (.int wi)) (.value x))).run (st,before) =
        .ok (some out,next,trace)) :
    DemandAllowed ctx st x ∧ ∃ r,ctx.valueReg? x = some r ∧
      out = .regsVec [[bmaskResult st.base wi r]] ∧
      next = {st.mark x with base := bmaskBase st.base wi r} := by
  cases call : Stock.externCtor ctx T.put_in_regs [.value x] st with
  | fail =>
    have denied : (evalExpr p (Stock.sem ctx) cfg (n+420) rule_lower_2052.rhs
        (env3 (.ty (.int wo)) (.ty (.int wi)) (.value x))).run (st,before) ≠
          .ok (some out,next,trace) := by
      cases hp
      isel_eval [*,rule_lower_2052,sem_ctor]
      intro impossible; cases impossible
    exact False.elim (denied run)
  | unmodeled err =>
    have denied : (evalExpr p (Stock.sem ctx) cfg (n+420) rule_lower_2052.rhs
        (env3 (.ty (.int wo)) (.ty (.int wi)) (.value x))).run (st,before) ≠
          .ok (some out,next,trace) := by
      cases hp
      isel_eval [*,rule_lower_2052,sem_ctor]
      intro impossible; cases impossible
    exact False.elim (denied run)
  | ok pair =>
    obtain ⟨value,middle⟩ := pair
    obtain ⟨safe,r,mapped,rfl,rfl⟩ :=
      (ScalarShift.stock_shift_put_in_regs_iff ctx st x value middle).mp call
    have expected := stock_bmask_rhs hp ctx hc output input mapped st safe before n
    have same := Except.ok.inj (run.symm.trans expected)
    exact ⟨safe,r,mapped,Option.some.inj (congrArg Prod.fst same),congrArg (fun q => q.2.1) same⟩

/-- All sixteen independent original width pairs inhabit the guarded RHS and
its observed contract, using the real source request and output consumer. -/
theorem stock_bmask_rhs_witness :
    ∀ wo ∈ ([8,16,32,64] : List Nat),∀ wi ∈ ([8,16,32,64] : List Nat),
      ∃ (out : V) (next : State) (trace : Array RuleId),
        (evalExpr program (Stock.sem sinkCtx) {} 1000 rule_lower_2052.rhs
          (env3 (.ty (.int wo)) (.ty (.int wi)) (.value 0))).run (sinkState,#[]) =
            .ok (some out,next,trace) ∧
        DemandAllowed sinkCtx sinkState 0 ∧
        out = .regsVec [[bmaskResult sinkState.base wi (.vreg 192 .int)]] ∧
        next = {sinkState.mark 0 with base := bmaskBase sinkState.base wi (.vreg 192 .int)} := by
  intro wo outMember wi inMember
  have output : wo ≤ 64 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at outMember; omega
  have input : wi = 8 ∨ wi = 16 ∨ wi = 32 ∨ wi = 64 := by simpa using inMember
  have safe := stock_put_in_regs_witness.1
  have run := stock_bmask_rhs data_program sinkCtx (cfg := {}) rfl output input
    (r := .vreg 192 .int) rfl sinkState safe #[] 580
  have observed := stock_bmask_rhs_observed data_program sinkCtx rfl output input run
  exact ⟨_,_,_,run,observed.1,rfl,rfl⟩

end Backend.Stock.Proof.ScalarMask
