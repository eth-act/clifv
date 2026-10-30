import FV.Backend.Proof.StockNoOpportunityCtor
import FV.Backend.Proof.IselCovClean
import FV.Backend.Proof.StockCoverageSound
import FV.Backend.Proof.LogicImmComplete
import FV.Backend.Proof.StockCoverageCtor
import FV.Backend.Proof.StockCoverageOracle
import FV.Backend.Proof.LowerDecide

/-! An inhabited model for actual Stock evaluation with the reused checked
summaries. Remembered-state preservation is derived from helper contracts;
no caller-supplied semantic model or accepted-program certificate is needed. -/
namespace Backend.Stock.Proof.Coverage
open Backend.Proof Backend.Proof.Cov Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- The real Stock helper contracts instantiate the state-aware analysis. -/
def model {f : Clif.Function} {ctx : Ctx} (mapped : MappedCtxInv f ctx)
    (clean : Clean (sourceIdentityCtx ctx)) (remembered : Array (Option Opportunistic)) :
    Model program f ctx where
  Is := fun st => st.opportunistic = remembered
  source := covModel logicImmComplete mapped.identityView clean sinkState.base
  ctor := by
    intro t term lookup as vs value st next held invariant pre run
    have both : (term.id != TId.opportunistic_def) = true ∧ apre term.id as = true := by
      simpa only [noOpportunityPre, Bool.and_eq_true] using pre
    have allowed : term.id ≠ TId.opportunistic_def := bne_iff_ne.mp both.1
    refine ⟨ctor_value_sound mapped logicImmComplete held both.2 run, ?_⟩
    exact (stock_ctor_noOpportunity allowed run).trans invariant
  oracle := oracle_sound _

private theorem clean_of_stock_build {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial)) : Clean (sourceIdentityCtx ctx) := by
  obtain ⟨original, before, legacy, spec, view⟩ := buildCtx_source build
  have clean := Cov.clean_of_build legacy
  intro i info lookup
  change ctx.insts[i]? = some info at lookup
  rw [view.insts] at lookup
  exact clean i info lookup

/-- Successful actual Stock evaluation accepted by the fixed abstract summary
preserves its remembered-definition table and has the described output. The
model is instantiated internally from the existing source context invariant. -/
theorem apply_coverage {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) (clean : Clean (sourceIdentityCtx ctx))
    {cfg : Config} (overlap : cfg.checkOverlap = false)
    {fuel ty term : Nat} {as : List AW} {a : AW} {vs : List V}
    {before after : State} {trace finalTrace : Array RuleId} {out : Option V}
    (checked : aApply program covTab actor noOpportunityPre aOracle ty term as = some a)
    (held : Holds2 f (sourceIdentityCtx ctx) as vs)
    (run : (applyTerm program (Stock.sem ctx) cfg fuel ty term vs).run (before, trace) =
      .ok (out, after, finalTrace)) :
    after.opportunistic = before.opportunistic ∧
      ∀ value, out = some value → γ f (sourceIdentityCtx ctx) a value := by
  let md := model mapped clean before.opportunistic
  exact (soundAt mapped md cfg covTab overlap stock_noOpportunity_table_checked fuel).apply
    ty term as a vs before trace out after finalTrace checked held rfl run

/-- Successful context construction derives both mapped-source and clean-data
premises. The only remaining admission is the fixed helper summary on its
actual argument values; this is an internal analysis fact, not a source check. -/
theorem built_apply_coverage {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State} (scope : LowerScope f)
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial))
    {cfg : Config} (overlap : cfg.checkOverlap = false)
    {fuel ty term : Nat} {as : List AW} {a : AW} {vs : List V}
    {before after : State} {trace finalTrace : Array RuleId} {out : Option V}
    (checked : aApply program covTab actor noOpportunityPre aOracle ty term as = some a)
    (held : Holds2 f (sourceIdentityCtx ctx) as vs)
    (run : (applyTerm program (Stock.sem ctx) cfg fuel ty term vs).run (before, trace) =
      .ok (out, after, finalTrace)) :
    after.opportunistic = before.opportunistic ∧
      ∀ value, out = some value → γ f (sourceIdentityCtx ctx) a value :=
  apply_coverage (buildCtx_mappedInv scope build) (clean_of_stock_build build) overlap checked held run

private def witnessFunction : Clif.Function := {
  name := "stock_coverage_model"
  sig := { returns := [⟨.i8, .none, .normal⟩], callConv := some .systemV }
  blocks := [{ id := 0, params := [], body := [⟨[0], .iconst .i8 7⟩], term := .ret [0] }] }
private def witnessBuilt : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx witnessFunction).toOption.getD (sinkCtx, #[], sinkState)
private theorem witness_build : Stock.buildCtx witnessFunction = .ok witnessBuilt := rfl
private theorem witness_scope : LowerScope witnessFunction := lowerScope_of (by decide +kernel)
private def witnessAs : List AW := [.ty [.int 64]]
private def witnessVs : List V := [.ty (.int 64)]
private def witnessAfter : State :=
  { witnessBuilt.2.2 with base := (witnessBuilt.2.2.base.fresh .int).2 }
private def witnessOut : V := .reg (witnessBuilt.2.2.base.fresh .int).1
private def witnessAbstract : AW :=
  (aApply program covTab actor noOpportunityPre aOracle
    T.temp_writable_reg.ret TId.temp_writable_reg witnessAs).getD .top
private theorem witness_held : Holds2 witnessFunction (sourceIdentityCtx witnessBuilt.1)
    witnessAs witnessVs := ⟨⟨_, by simp, rfl⟩, trivial⟩
private theorem witness_checked :
    aApply program covTab actor noOpportunityPre aOracle
      T.temp_writable_reg.ret TId.temp_writable_reg witnessAs = some witnessAbstract := by
  simp (config := {decide := true}) [aApply, witnessAs, witnessAbstract, data_program.t175,
    T.temp_writable_reg, noOpportunityPre, AW.isBot, apre]
private theorem witness_run :
    (applyTerm program (Stock.sem witnessBuilt.1) {} 1 T.temp_writable_reg.ret
      TId.temp_writable_reg witnessVs).run (witnessBuilt.2.2, #[]) =
      .ok (some witnessOut, witnessAfter, #[]) := by
  have ctor : Stock.externCtor witnessBuilt.1 T.temp_writable_reg witnessVs witnessBuilt.2.2 =
      .ok (witnessOut, witnessAfter) := by
    rw [stock_ctor_baseOnly _ _ _ _ (by decide)]
    rfl
  simp only [applyTerm.eq_2, data_program.t175, T.temp_writable_reg, witnessVs,
    isel_monad, Stock.sem]
  simp only [T.temp_writable_reg, witnessVs] at ctor
  rw [ctor]
  rfl

/-- A real nonempty function/context, nonempty typed helper arguments and a
successful allocating interpreter run inhabit the analysis/model premises. -/
theorem apply_coverage_witness :
    ∃ (f : Clif.Function) (ctx : Ctx) (ranges : Array (Nat × Nat)) (initial after : State)
      (as : List AW) (vs : List V) (a : AW) (value : V),
      LowerScope f ∧ Stock.buildCtx f = .ok (ctx, ranges, initial) ∧ f.blocks.length ≠ 0 ∧
      ctx.valueReg? 0 = some (.vreg 192 .int) ∧ vs ≠ [] ∧
      aApply program covTab actor noOpportunityPre aOracle
        T.temp_writable_reg.ret TId.temp_writable_reg as = some a ∧
      Holds2 f (sourceIdentityCtx ctx) as vs ∧
      (applyTerm program (Stock.sem ctx) {} 1 T.temp_writable_reg.ret
        TId.temp_writable_reg vs).run (initial, #[]) = .ok (some value, after, #[]) ∧
      after.base.nextVreg = initial.base.nextVreg + 1 ∧
      after.opportunistic = initial.opportunistic ∧ γ f (sourceIdentityCtx ctx) a value := by
  have result := built_apply_coverage witness_scope witness_build (by rfl)
    witness_checked witness_held witness_run
  exact ⟨witnessFunction, witnessBuilt.1, witnessBuilt.2.1, witnessBuilt.2.2, witnessAfter,
    witnessAs, witnessVs, witnessAbstract, witnessOut, witness_scope, witness_build,
    by decide, by decide +kernel, by decide, witness_checked, witness_held,
    witness_run, by rfl, result.1, result.2 _ rfl⟩

/-- The general state-aware induction is inhabited by the actual full-program
model and an allocating run on a nonempty successfully built context. -/
theorem soundAt_witness :
    ∃ (f : Clif.Function) (ctx : Ctx) (ranges : Array (Nat × Nat)) (initial after : State)
      (md : Model program f ctx) (value : V),
      LowerScope f ∧ Stock.buildCtx f = .ok (ctx, ranges, initial) ∧
      MappedCtxInv f ctx ∧ Clean (sourceIdentityCtx ctx) ∧ md.Is initial ∧
      SoundAt md {} covTab 1 ∧
      (applyTerm program (Stock.sem ctx) {} 1 T.temp_writable_reg.ret
        TId.temp_writable_reg witnessVs).run (initial, #[]) = .ok (some value, after, #[]) ∧
      after.base.nextVreg = initial.base.nextVreg + 1 := by
  have mapped := buildCtx_mappedInv witness_scope witness_build
  have clean := clean_of_stock_build witness_build
  let md := model mapped clean witnessBuilt.2.2.opportunistic
  exact ⟨witnessFunction, witnessBuilt.1, witnessBuilt.2.1, witnessBuilt.2.2,
    witnessAfter, md, witnessOut, witness_scope, witness_build, mapped, clean, rfl,
    soundAt mapped md {} covTab rfl stock_noOpportunity_table_checked 1, witness_run, rfl⟩

/-- Constructor premises have real typed arguments and successful allocation,
with the fixed logical-immediate fact supplied by its existing proof. -/
theorem ctor_value_sound_witness :
    ∃ (f : Clif.Function) (ctx : Ctx) (initial after : State) (value : V),
      MappedCtxInv f ctx ∧ LogicImmComplete ∧
      Holds2 f (sourceIdentityCtx ctx) witnessAs witnessVs ∧
      apre T.temp_writable_reg.id witnessAs = true ∧
      (Stock.sem ctx).ctor T.temp_writable_reg witnessVs initial = .ok (value, after) ∧
      after.base.nextVreg = initial.base.nextVreg + 1 ∧
      γ f (sourceIdentityCtx ctx) (actor T.temp_writable_reg.id witnessAs) value := by
  have mapped := buildCtx_mappedInv witness_scope witness_build
  have pre : apre T.temp_writable_reg.id witnessAs = true := by decide +kernel
  have ctor : (Stock.sem witnessBuilt.1).ctor T.temp_writable_reg witnessVs witnessBuilt.2.2 =
      .ok (witnessOut, witnessAfter) := by
    change Stock.externCtor witnessBuilt.1 T.temp_writable_reg witnessVs witnessBuilt.2.2 =
      .ok (witnessOut, witnessAfter)
    rw [stock_ctor_baseOnly _ _ _ _ (by decide)]
    rfl
  exact ⟨witnessFunction, witnessBuilt.1, witnessBuilt.2.2, witnessAfter, witnessOut,
    mapped, logicImmComplete, witness_held, pre, ctor, rfl,
    ctor_value_sound mapped logicImmComplete witness_held pre ctor⟩

private def witnessCallSig : Clif.Signature := { returns := [⟨.i64, .none, .normal⟩] }
private def witnessCallOut : V := .regsVec [[(witnessBuilt.2.2.base.fresh .int).1]]
private def witnessCallAfter : State :=
  { witnessBuilt.2.2 with base := (witnessBuilt.2.2.base.fresh .int).2 }

/-- `ctor_value_sound_int` is inhabited by Stock's `gen_call_output` on a signature with one
`i64` return: one fresh int vreg, which `Cov.actorI` describes (`.flat 1 true`). -/
theorem ctor_value_sound_int_witness :
    ∃ (f : Clif.Function) (ctx : Ctx) (initial after : State) (value : V),
      MappedCtxInv f ctx ∧ LogicImmComplete ∧
      Holds2 f (sourceIdentityCtx ctx) [AW.top] [.op (.sig witnessCallSig)] ∧
      apre T.gen_call_output.id [AW.top] = true ∧
      (Stock.sem ctx).ctor T.gen_call_output [.op (.sig witnessCallSig)] initial =
        .ok (value, after) ∧
      (∃ n, value = .regsVec [[.vreg n .int]]) ∧
      γ f (sourceIdentityCtx ctx) (Cov.actorI T.gen_call_output.id [AW.top]) value := by
  have mapped := buildCtx_mappedInv witness_scope witness_build
  have held : Holds2 witnessFunction (sourceIdentityCtx witnessBuilt.1) [AW.top]
      [.op (.sig witnessCallSig)] := ⟨γ_top _, trivial⟩
  have pre : apre T.gen_call_output.id [AW.top] = true := by decide +kernel
  have ctor : (Stock.sem witnessBuilt.1).ctor T.gen_call_output [.op (.sig witnessCallSig)]
      witnessBuilt.2.2 = .ok (witnessCallOut, witnessCallAfter) := rfl
  exact ⟨witnessFunction, witnessBuilt.1, witnessBuilt.2.2, witnessCallAfter, witnessCallOut,
    mapped, logicImmComplete, held, pre, ctor, ⟨_, rfl⟩,
    ctor_value_sound_int mapped logicImmComplete held pre ctor⟩

private def witnessOracleAbstract : AW :=
  (aOracle TId.operand_size witnessAs).getD .top
private theorem witness_oracle_run :
    (applyTerm program (Stock.sem witnessBuilt.1) {} 20 T.operand_size.ret
      TId.operand_size witnessVs).run (witnessBuilt.2.2, #[]) =
      .ok (some (.data 93 1 []), witnessBuilt.2.2, #[79]) := by
  rfl

/-- The operand-size oracle's admission, input, run and state-invariant premises
are inhabited by the actual full program returning Size64. -/
theorem oracle_sound_witness :
    ∃ (f : Clif.Function) (ctx : Ctx) (initial : State) (I : State → Prop),
      MappedCtxInv f ctx ∧ I initial ∧
      aOracle TId.operand_size witnessAs = some witnessOracleAbstract ∧
      Holds2 f (sourceIdentityCtx ctx) witnessAs witnessVs ∧
      (applyTerm program (Stock.sem ctx) {} 20 T.operand_size.ret
        TId.operand_size witnessVs).run (initial, #[]) =
        .ok (some (.data 93 1 []), initial, #[79]) ∧
      I initial ∧ γ f (sourceIdentityCtx ctx) witnessOracleAbstract (.data 93 1 []) := by
  have mapped := buildCtx_mappedInv witness_scope witness_build
  let I : State → Prop := fun st => st.opportunistic = witnessBuilt.2.2.opportunistic
  have admitted : aOracle TId.operand_size witnessAs = some witnessOracleAbstract := by
    simp (config := {decide := true}) [witnessOracleAbstract, aOracle, witnessAs]
  have result := oracle_sound I {} rfl 20 _ _ _ _ _ witnessBuilt.2.2 #[]
    _ witnessBuilt.2.2 #[79] admitted witness_held rfl witness_oracle_run
  exact ⟨witnessFunction, witnessBuilt.1, witnessBuilt.2.2, I, mapped, rfl, admitted,
    witness_held, witness_oracle_run, result.1, result.2 _ rfl⟩

end Backend.Stock.Proof.Coverage
