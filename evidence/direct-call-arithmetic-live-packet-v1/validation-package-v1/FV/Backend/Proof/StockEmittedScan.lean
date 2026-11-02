import FV.Backend.Proof.StockEmissionSemantics
import FV.Backend.Proof.StockDriverBounds

/-! Actual emitted-scan inversion and constant-rule transfer at real backward
scan boundaries. These discharge local semantic obligations from constructor
and selector proofs; final aliases still come from the whole-driver invariant. -/

namespace Backend.Stock.Proof

open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 4096

attribute [local irreducible] emitInstruction Stock.runTerm Isle.Aarch64.program

/-- An actual emitted decision identifies its real emitter transition and
complete output scan, including code, results, rule trace and after-state. -/
theorem stock_emitted_scan {ctx : Ctx} {block i ti : Nat} {isBranch : Bool}
    {input : State} {output : Scan} {step : Step}
    (hscan : scanInstruction ctx block i ti isBranch input = .ok output)
    (hstep : output.step = some step) (hd : step.decision = .emitted) :
    ∃ emission, emitInstruction ctx i (scanState input i) = .ok emission ∧
      output = emission.scan block i (scanState input i) := by
  have emit (he : (emitInstruction ctx i (scanState input i) >>= fun e =>
      pure (e.scan block i (scanState input i))) = .ok output) :
      ∃ emission, emitInstruction ctx i (scanState input i) = .ok emission ∧
        output = emission.scan block i (scanState input i) := by
    cases hr : emitInstruction ctx i (scanState input i) with
    | error e => simp only [hr, bind, Except.bind] at he; cases he
    | ok emission =>
      simp only [hr, bind, Except.bind, pure, Except.pure] at he
      cases he
      exact ⟨emission, rfl, rfl⟩
  unfold scanInstruction at hscan
  dsimp only at hscan
  generalize hm : (if i == ti then true else ctx.insts[i]!.clif.any mustLower) = mandatory at hscan
  split at hscan
  · cases hscan; cases hstep; cases hd
  · split at hscan
    · cases hscan; cases hstep
    · split at hscan
      · cases hscan; cases hstep; cases hd
      · split at hscan
        · cases ho : commitOpportunistic ctx block i (scanState input i) with
          | error e => simp only [ho, bind, Except.bind] at hscan; cases hscan
          | ok result =>
            simp only [ho, bind, Except.bind] at hscan
            cases result with
            | none => exact emit hscan
            | some next => cases hscan; cases hstep; cases hd
        · exact emit hscan

private theorem scan_empty (st : State) (i : Nat) :
    (scanState st i).base.emitted = #[] := by
  unfold scanState
  dsimp only
  split <;> rfl

/-- The selected constant rule discharges an actual emitted scan's semantic
obligation, including the normalization from its input to its before-state. -/
theorem stock_iconstScan_fall_refines {p : Program} (hp : Data p)
    {f : Clif.Function} {ctx : Ctx} (hctx : MappedCtxInv f ctx)
    {ii block ti : Nat} {isBranch : Bool} {info : IInfo} {inst : Clif.Inst}
    (hi : ctx.insts[ii]? = some info) (hic : info.clif = some inst)
    {input : State} {output : Scan} {step : Step}
    (hscan : scanInstruction ctx block ii ti isBranch input = .ok output)
    (hstep : output.step = some step) (hd : step.decision = .emitted)
    {cfg : Config} (hc : cfg.checkOverlap = false)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (hR : Refines F isem)
    (hsem : ∀ aliases i, isem (i.mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size + 1))) = isem i)
    {m n : Nat} (hm : 2 ≤ m) (hn : 50 ≤ n)
    {s1 st' : State} {tr tr1 tr' : Array RuleId} {env' : Isle.Interp.Env V} {out : V}
    (hmatch : (matchRule p (Stock.sem ctx) cfg m rule_lower_53 [.inst ii]).run
      (scanState input ii, tr) = .ok (some env', s1, tr1))
    (heval : (evalExpr p (Stock.sem ctx) cfg n rule_lower_53.rhs env').run (s1, tr1) =
      .ok (some out, st', tr'))
    {trace : List RuleId}
    (hroot : Stock.runTerm ctx "lower" [.inst ii] (scanState input ii) =
      .ok (some out, st', trace)) {x a : Nat}
    (hres : info.results = [x]) (hmap : ctx.valueReg? x = some (.vreg a .int)) :
    ∃ (ty : Clif.Ty) (imm : BitVec ty.width) (d : Nat),
      inst = .iconst ty imm ∧ out = .regsVec [[.vreg d .int]] ∧
      ∀ aliases, aliases.size ≤ (scanState input ii).base.nextVreg →
        aliasNum aliases a = d →
        (∀ y b, Demanded input y → y ≠ x → ctx.valueReg? y = some (.vreg b .int) →
          aliasNum aliases b < (scanState input ii).base.nextVreg ∨
            output.state.base.nextVreg ≤ aliasNum aliases b) →
        ∀ (env : Clif.Env) (cp : Clif.Program) (MR : Clif.Mem → Arm.ArmState → Prop),
        (∀ cm w w', SameWorld F w' w → MR cm w → MR cm w') →
        ScanFallRefines (SourceInstResult env cp ctx) isem aliases
          (fun q s ρ w => MR s.2 w ∧ ValuesHeld (Demanded q) ctx s.1
            (fun k => ρ (aliasNum aliases k))) ⟨ii, input, output⟩ := by
  obtain ⟨actual, hemit, houtput⟩ := stock_emitted_scan hscan hstep hd
  obtain ⟨ty, imm, d, emission, hinst, hout, hresults, hemit', hmono, hlocal⟩ :=
    stock_iconst_emission_fall_refines hp hctx (block := block) hi hic hc hR hsem hm hn
      hmatch heval hroot (scan_empty input ii) hres hmap
  have heq : actual = emission := Except.ok.inj (hemit.symm.trans hemit')
  subst actual
  subst output
  refine ⟨ty, imm, d, hinst, hout, ?_⟩
  intro aliases ha hresult houtside env cp MR hMR
  have hlocal' := hlocal aliases ha hresult (fun y b hy hne hm =>
    houtside y b (by simpa only [Demanded, scanState_demands] using hy) hne hm) env cp MR hMR
  simpa only [ScanFallRefines, ValuesHeld, Demanded, scanState_demands] using hlocal'

/-- Actual selection and alias-transfer facts for an emitted constant. The
allocation cap is supplied separately by the whole-driver proof. -/
structure ConstantScanFacts (ctx : Ctx) (aliases : Array (Option Nat)) (r : ScanRecord) where
  info : IInfo
  inst : Clif.Inst
  source : ctx.insts[r.inst]? = some info
  original : info.clif = some inst
  value : Nat
  mapped : Nat
  result : Nat
  results : info.results = [value]
  mapping : ctx.valueReg? value = some (.vreg mapped .int)
  m : Nat
  n : Nat
  matchFuel : 2 ≤ m
  evalFuel : 50 ≤ n
  env : Isle.Interp.Env V
  matched : State
  next : State
  matchTrace : Array RuleId
  evalTrace : Array RuleId
  trace : List RuleId
  out : V
  output : out = .regsVec [[.vreg result .int]]
  matchRun : (matchRule program (Stock.sem ctx) {} m rule_lower_53 [.inst r.inst]).run
    (scanState r.input r.inst, #[]) = .ok (some env, matched, matchTrace)
  evalRun : (evalExpr program (Stock.sem ctx) {} n rule_lower_53.rhs env).run
    (matched, matchTrace) = .ok (some out, next, evalTrace)
  rootRun : Stock.runTerm ctx "lower" [.inst r.inst] (scanState r.input r.inst) =
    .ok (some out, next, trace)
  resultAlias : aliasNum aliases mapped = result
  otherOutside : ∀ y b, Demanded r.input y → y ≠ value →
    ctx.valueReg? y = some (.vreg b .int) →
    aliasNum aliases b < (scanState r.input r.inst).base.nextVreg ∨
      r.output.state.base.nextVreg ≤ aliasNum aliases b
  step : Step
  stepRecorded : r.output.step = some step
  emitted : step.decision = .emitted

/-- The original local invariant remains available to existing callers. -/
structure ConstantScanInv (ctx : Ctx) (aliases : Array (Option Nat)) (r : ScanRecord)
    extends ConstantScanFacts ctx aliases r where
  aliasesBounded : aliases.size ≤ (scanState r.input r.inst).base.nextVreg

/-- For a record retained by the actual compiler, allocation boundedness is a
consequence of the run. Callers supply selection and alias transfer facts only. -/
def constantScanInvOfRun {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (recorded : event ∈ result.blockScans.toList) {record : ScanRecord}
    (member : record ∈ event.output.records)
    (facts : ConstantScanFacts event.ctx result.final.alias record) :
    ConstantScanInv event.ctx result.final.alias record := {
  toConstantScanFacts := facts
  aliasesBounded := stock_lower_blockScanAliasBounds run event recorded record member }

private theorem scans_execute {exec : Nat → State → Except String Scan}
    {indices : List Nat} {input : State} {output : BlockScan}
    (h : ScansSpec exec indices input output) :
    ∀ r ∈ output.records, exec r.inst r.input = .ok r.output := by
  induction h with
  | nil input => simp
  | cons head rest ih =>
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact head
    · exact ih r hr

/-- Constants and actual omitted instructions compose without a local semantic
oracle. Actual selection and final aliases discharge each emitted obligation;
omitted loads may still update source registers while producing no code. -/
theorem stock_constantOmittedBlock_fall_refines {f : Clif.Function} {ctx : Ctx}
    (hctx : MappedCtxInv f ctx) {block ti : Nat} {isBranch : Bool}
    {input : State} {output : BlockScan} {indices : List Nat}
    {aliases : Array (Option Nat)} {env : Clif.Env} {cp : Clif.Program}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (hR : Refines F isem)
    (hsem : ∀ a i, isem (i.mapRegs
      (Backend.lowerFunction.resolve a (a.size + 1))) = isem i)
    {MR : Clif.Mem → Arm.ArmState → Prop}
    (hMR : ∀ cm w w', SameWorld F w' w → MR cm w → MR cm w')
    (hscan : scanBlock ctx block ti isBranch indices input = .ok output)
    (hcases : ∀ r ∈ output.records,
      (∃ step, r.output.step = some step ∧ step.decision = .omitted) ∨
        Nonempty (ConstantScanInv ctx aliases r)) :
    ∀ s s', SourceSteps (SourceInstResult env cp ctx) indices.reverse s s' → ∀ ρ w,
      MR s.2 w → ValuesHeld (Demanded output.state) ctx s.1
        (fun k => ρ (aliasNum aliases k)) → ∃ ρ' w',
          seqRun isem (output.code.toList.map (·.mapRegs
            (Backend.lowerFunction.resolve aliases (aliases.size + 1)))) ρ w = some (.fall ρ' w') ∧
          MR s'.2 w' ∧ ValuesHeld (Demanded input) ctx s'.1
            (fun k => ρ' (aliasNum aliases k)) := by
  have cert := runScans_spec hscan
  have hlocal : ∀ r ∈ output.records,
      ScanFallRefines (SourceInstResult env cp ctx) isem aliases
        (fun q s ρ w => MR s.2 w ∧ ValuesHeld (Demanded q) ctx s.1
          (fun k => ρ (aliasNum aliases k))) r := by
    intro r hr
    have hs := scans_execute cert r hr
    rcases hcases r hr with omitted | selected
    · obtain ⟨step, hstep, hd⟩ := omitted
      exact stock_omitted_fall_refines hs hstep hd
    · rcases selected with ⟨selected⟩
      obtain ⟨ty, imm, d, hi, hout, htransfer⟩ := stock_iconstScan_fall_refines
        data_program hctx selected.source selected.original hs selected.stepRecorded selected.emitted
        rfl hR hsem selected.matchFuel selected.evalFuel selected.matchRun selected.evalRun
        selected.rootRun selected.results selected.mapping
      have heq : d = selected.result := by
        have h := hout.symm.trans selected.output
        cases h
        rfl
      subst d
      exact htransfer aliases selected.aliasesBounded selected.resultAlias
        selected.otherOutside env cp MR hMR
  intro s s' hs ρ w hmem hheld
  exact cert.fall_refines hlocal s s' hs ρ w ⟨hmem, hheld⟩

/-- A real constant scan makes the emitted inversion's premise satisfiable. -/
theorem stock_emitted_scan_witness :
    ∃ (ctx : Ctx) (input : State) (output : Scan) (step : Step) (emission : Emission),
      scanInstruction ctx 0 0 1 false input = .ok output ∧
      output.step = some step ∧ step.decision = .emitted ∧
      emitInstruction ctx 0 (scanState input 0) = .ok emission ∧
      output = emission.scan 0 0 (scanState input 0) := by
  obtain ⟨f, ctx, emission, fr, fr', ρ', w', hctx, hmap, hemit, hscan, hsource, hrun, hv, hfr⟩ :=
    stock_iconst_emission_fall_refines_witness
  let input := (fun {ctx : Ctx} {input : State} {output : Scan}
    (_ : scanInstruction ctx 0 0 1 false input = .ok output) => input) hscan
  let output := emission.scan 0 0 (scanState input 0)
  let step : Step := ⟨0, 0, .emitted, scanState input 0, emission.state,
    emission.results, emission.rules, emission.code⟩
  have hs : output.step = some step := rfl
  obtain ⟨actual, ha, ho⟩ := stock_emitted_scan hscan hs (show step.decision = .emitted from rfl)
  exact ⟨ctx, input, output, step, actual, hscan, hs, rfl, ha, ho⟩

private def constantInput : State := { sinkState with demand := #[0, 0, 1] }
private def constantAliases : Array (Option Nat) := aliasStep #[] (193, 194)

private theorem constant_demanded (y : Nat) : Demanded constantInput y ↔ y = 2 := by
  change (#[0, 0, 1] : Array Nat)[y]! ≠ 0 ↔ y = 2
  match y with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | y + 3 =>
    have ho : (#[0, 0, 1] : Array Nat)[y + 3]? = none :=
      Array.getElem?_eq_none (by change 3 ≤ y + 3; omega)
    simp only [getElem!_def, ho]
    simp

private theorem constant_aliases :
    constantAliases.size ≤ (scanState constantInput 0).base.nextVreg ∧
      aliasNum constantAliases 193 = 194 := by decide

private theorem self_refines : Refines (fun _ => True) ispec :=
  fun _ _ _ _ w' _ h => ⟨w', h, SameWorld.refl _ _⟩

private theorem resolver_sem : ∀ aliases i, ispec (i.mapRegs
    (Backend.lowerFunction.resolve aliases (aliases.size + 1))) = ispec i := by
  intro aliases i
  funext us w
  have hg : VRenaming (Backend.lowerFunction.resolve aliases (aliases.size + 1))
      (aliasNum aliases) := by
    refine ⟨fun n c => resolve_vreg aliases _ n c, ?_⟩
    intro r hr
    cases r with
    | vreg n c => exact False.elim (hr n c rfl)
    | _ => simp [Backend.lowerFunction.resolve]
  exact ispec_mapRegs hg us w i

set_option maxHeartbeats 500000 in
private theorem constant_fixture :
    ∃ (f : Clif.Function) (ctx : Ctx) (info : IInfo) (output : Scan),
      MappedCtxInv f ctx ∧ ctx.insts[0]? = some info ∧
      info.clif = some (.iconst .i8 9) ∧ info.results = [2] ∧
      ctx.valueReg? 2 = some (.vreg 193 .int) ∧
      scanInstruction ctx 0 0 1 false constantInput = .ok output ∧
      output.state.alias = constantAliases ∧
      Nonempty (ConstantScanInv ctx constantAliases ⟨0, constantInput, output⟩) := by
  obtain ⟨f, ctx, info, hc, hi, hic, hres, hmap, hselected⟩ := stock_statement_selectedConstant
  obtain ⟨next, trace, hroot, heval, hmatch⟩ := hselected (scanState constantInput 0)
  obtain ⟨ty, imm, d, emission, hinst, hout, hrs, hemit, hmono, hlocal⟩ :=
    stock_iconst_emission_fall_refines data_program hc (block := 0) hi hic rfl
      self_refines resolver_sem (by decide) (by decide) hmatch heval hroot
      (scan_empty constantInput 0) hres hmap
  cases hinst
  change V.regsVec [[.vreg 194 .int]] = .regsVec [[.vreg d .int]] at hout
  cases hout
  have hscan : scanInstruction ctx 0 0 1 false constantInput =
      .ok (emission.scan 0 0 (scanState constantInput 0)) := by
    have hinfo : ctx.insts[0]! = info := by simp only [getElem!_def, hi]
    unfold scanInstruction
    simp only [show constantInput.sunk[0]! = false from rfl, Bool.false_eq_true, ite_false,
      show (0 == 1) = false from rfl, Bool.false_and, hinfo, hic,
      hres, List.any_cons, List.any_nil,
      show (scanState constantInput 0).demand[2]! = 1 from rfl,
      show ((1 : Nat) != 0) = true from rfl, Bool.true_or, Bool.not_true, Bool.and_false,
      show ((scanState constantInput 0).entryColor[0]! == 0) = false from rfl,
      bind, Except.bind, pure, Except.pure]
    rw [hemit]
  obtain ⟨aliasEmission, haliasEmit, haliasFrame, _, _⟩ :=
    stock_iconst_emission_alias data_program hi hres hmap rfl hmatch heval hroot
  have heq : aliasEmission = emission := Except.ok.inj (haliasEmit.symm.trans hemit)
  have halias : emission.state.alias = constantAliases := by
    rw [← heq, haliasFrame]
    change aliasStep (scanState constantInput 0).alias
      (193, (scanState constantInput 0).base.nextVreg) = aliasStep #[] (193, 194)
    rw [show (scanState constantInput 0).alias = #[] from rfl,
      show (scanState constantInput 0).base.nextVreg = 194 from rfl]
  let output := emission.scan 0 0 (scanState constantInput 0)
  refine ⟨f, ctx, info, output, hc, hi, hic, hres, hmap, hscan, halias, ?_⟩
  refine ⟨{
    info := info
    inst := .iconst .i8 9
    source := hi
    original := hic
    value := 2
    mapped := 193
    result := 194
    results := hres
    mapping := hmap
    m := 999825
    n := 999999
    matchFuel := by decide
    evalFuel := by decide
    env := env2 (.ty (.int 8)) (.int 9)
    matched := scanState constantInput 0
    next := next
    matchTrace := #[]
    evalTrace := trace
    trace := (trace.push 582).toList
    out := .regsVec [[.vreg 194 .int]]
    output := rfl
    matchRun := hmatch
    evalRun := heval
    rootRun := hroot
    aliasesBounded := constant_aliases.1
    resultAlias := constant_aliases.2
    otherOutside := ?_
    step := ⟨0, 0, .emitted, scanState constantInput 0, emission.state,
      emission.results, emission.rules, emission.code⟩
    stepRecorded := rfl
    emitted := rfl }⟩
  intro y b hy hne _
  exact False.elim (hne ((constant_demanded y).mp hy))

private def constantRel (ctx : Ctx) (q : State) (s : Clif.Frame × Clif.Mem)
    (ρ : Nat → CV) (_ : Arm.ArmState) : Prop :=
  True ∧ ValuesHeld (Demanded q) ctx s.1 (fun k => ρ (aliasNum constantAliases k))

theorem stock_iconstScan_fall_refines_witness :
    ∃ (f : Clif.Function) (ctx : Ctx) (info : IInfo) (output : Scan),
      MappedCtxInv f ctx ∧ ctx.insts[0]? = some info ∧
      info.clif = some (.iconst .i8 9) ∧ info.results = [2] ∧
      scanInstruction ctx 0 0 1 false constantInput = .ok output ∧
      ScanFallRefines (SourceInstResult Clif.Env.empty { funcs := [] } ctx) ispec
        constantAliases (constantRel ctx) ⟨0, constantInput, output⟩ ∧
      Demanded constantInput 2 := by
  obtain ⟨f, ctx, info, output, hc, hi, hic, hres, hmap, hs, _halias, ⟨selected⟩⟩ := constant_fixture
  obtain ⟨ty, imm, d, hinst, hout, htransfer⟩ := stock_iconstScan_fall_refines data_program
    hc selected.source selected.original hs selected.stepRecorded selected.emitted rfl
    self_refines resolver_sem selected.matchFuel selected.evalFuel selected.matchRun
    selected.evalRun selected.rootRun selected.results selected.mapping
  have heq : d = selected.result := by
    have h := hout.symm.trans selected.output
    cases h; rfl
  subst d
  exact ⟨f, ctx, info, output, hc, hi, hic, hres, hs,
    htransfer constantAliases selected.aliasesBounded selected.resultAlias selected.otherOutside
      Clif.Env.empty { funcs := [] } (fun _ _ => True) (fun _ _ _ _ _ => trivial),
    (constant_demanded 2).mpr rfl⟩

/-- An actual emitted constant block discharges the block theorem's cases;
it evaluates a real source statement and runs machine code resolved through
the alias array returned by this actual block scan. -/
theorem stock_constantOmittedBlock_fall_refines_witness :
    ∃ (f : Clif.Function) (ctx : Ctx) (output : BlockScan) (fr fr' : Clif.Frame)
      (ρ' : Nat → CV) (w' : Arm.ArmState),
      MappedCtxInv f ctx ∧ scanBlock ctx 0 1 false [0] constantInput = .ok output ∧
      SourceSteps (SourceInstResult Clif.Env.empty { funcs := [] } ctx) [0]
        (fr, Clif.Mem.empty) (fr', Clif.Mem.empty) ∧
      seqRun ispec (output.code.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve output.state.alias (output.state.alias.size + 1))))
        (fun _ => 0) Arm.ArmState.default = some (.fall ρ' w') ∧
      ValuesHeld (Demanded constantInput) ctx fr'
        (fun k => ρ' (aliasNum output.state.alias k)) ∧
      VHolds (Clif.Val.ofInt .i8 9) (ρ' 194) ∧ fr'.body = [] := by
  obtain ⟨f, ctx, info, scan, hc, hi, hic, hres, hmap, hs, halias, selected⟩ := constant_fixture
  let record : ScanRecord := ⟨0, constantInput, scan⟩
  let output : BlockScan := ⟨scan.state, [record], scan.emitted⟩
  have hb : scanBlock ctx 0 1 false [0] constantInput = .ok output := by
    unfold scanBlock
    rw [runScans_ref]
    simp only [runScansRef, hs, bind, Except.bind, pure, Except.pure, Array.empty_append]
    rfl
  have hcases : ∀ r ∈ output.records,
      (∃ step, r.output.step = some step ∧ step.decision = .omitted) ∨
        Nonempty (ConstantScanInv ctx constantAliases r) := by
    intro r hr
    change r ∈ [record] at hr
    have he := List.mem_singleton.mp hr
    subst r
    exact Or.inr selected
  let fr : Clif.Frame := {
    func := f
    regs := fun _ => none
    slots := []
    body := [⟨[2], .iconst .i8 9⟩]
    term := .ret [2] }
  let fr' : Clif.Frame := { fr with regs := fr.regs.set 2 (.ofInt .i8 9), body := [] }
  have hsource : SourceInstResult Clif.Env.empty { funcs := [] } ctx 0
      (fr, Clif.Mem.empty) (fr', Clif.Mem.empty) :=
    ⟨info, .iconst .i8 9, [.ofInt .i8 9], fr.regs.set 2 (.ofInt .i8 9), [],
      hi, hic, by simp only [fr, hres], rfl, by rw [hres]; rfl, rfl⟩
  have hsteps : SourceSteps (SourceInstResult Clif.Env.empty { funcs := [] } ctx) [0]
      (fr, Clif.Mem.empty) (fr', Clif.Mem.empty) := .cons hsource (.nil _)
  have hstart : ValuesHeld (Demanded output.state) ctx fr (fun _ => (0 : CV)) := by
    intro x hx v hv
    cases hv
  obtain ⟨ρ', w', hrun, hmem, hheld⟩ := stock_constantOmittedBlock_fall_refines hc
    self_refines resolver_sem (fun _ _ _ _ _ => trivial) hb hcases
    (fr, Clif.Mem.empty) (fr', Clif.Mem.empty) hsteps (fun _ => 0)
    Arm.ArmState.default trivial hstart
  have hv := hheld.read ((constant_demanded 2).mpr rfl)
    (show fr'.regs 2 = some (.ofInt .i8 9) from rfl) hmap
  rw [constant_aliases.2] at hv
  have ha : output.state.alias = constantAliases := halias
  refine ⟨f, ctx, output, fr, fr', ρ', w', hc, hb, hsteps, ?_, ?_, hv, rfl⟩
  · simpa only [ha] using hrun
  · simpa only [ha] using hheld

end Backend.Stock.Proof
