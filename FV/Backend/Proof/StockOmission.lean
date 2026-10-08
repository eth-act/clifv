import FV.Backend.Proof.StockScan
import FV.Backend.Proof.StockDemand
import FV.Opt.Proof.SemFacts

/-!
Semantic omission obligations. The actual stock guard permits nontrapping loads
as well as memory-free arithmetic. Omitting their code preserves memory and
traps, while ignoring their source results preserves demanded mapped values.
This is a local simulation step, not yet the whole backward-schedule proof.
The Opt.SemFacts dependency intentionally shares existing source-semantics
lemmas; these facts do not depend on optimizing the input function.
-/

namespace Backend.Stock.Proof

open Backend.Proof Backend.Proof.Driver

private theorem load_noTrap (mem : Clif.Mem) (flags : Clif.MemFlags)
    (hflags : flags.trapCode = none) (addr n w : Nat) (c : Clif.TrapCode) :
    mem.load flags addr n w ≠ .trap c := by
  simp only [Clif.Mem.load]
  unfold Clif.Mem.checkAccess
  split
  · split <;> simp
  · simp [hflags]

/-- Every source operation eligible for omission preserves memory on successful
evaluation and cannot produce a trap. Undefined/nontrapping invalid inputs may
still be stuck, as in the existing source semantics. -/
theorem mustLower_quiet {fr : Clif.Frame} {mem : Clif.Mem} {inst : Clif.Inst}
    (hm : mustLower inst = false) :
    (∀ vals mem', Clif.evalInst fr mem inst = .ok (vals, mem') → mem' = mem) ∧
      ∀ c, Clif.evalInst fr mem inst ≠ .trap c := by
  cases inst <;> first
    | (simp [mustLower] at hm; done)
    | (apply Opt.evalInst_removable; rfl)
    | skip
  case load op ty flags p offset =>
    have hflags : flags.trapCode = none := by
      cases hf : flags.trapCode <;> simp [mustLower, Clif.MemFlags.notrap, hf] at hm ⊢
    refine ⟨fun vals mem' h => ?_, fun c h => ?_⟩
    · simp only [Clif.evalInst, Opt.Res.bind_eq_ok, Opt.Res.pure_eq_ok,
        Prod.mk.injEq] at h
      obtain ⟨_, _, _, _, _, _, _, rfl⟩ := h
      rfl
    · simp only [Clif.evalInst, Opt.Res.bind_eq_trap, Opt.Frame.get_ne_trap,
        Opt.Res.check_ne_trap, Opt.Res.pure_ne_trap,
        false_or, and_false, exists_false, or_false] at h
      obtain ⟨_, _, _, _, hload⟩ := h
      exact load_noTrap mem flags hflags _ _ _ c hload
  all_goals
    refine ⟨fun vals mem' h => ?_, fun c h => ?_⟩ <;>
      simp only [Clif.evalInst, Clif.Frame.getAs, Opt.Res.bind_eq_ok,
        Opt.Res.pure_eq_ok, Prod.mk.injEq, Opt.Res.bind_eq_trap,
        Opt.Res.ofOption_ne_trap, Opt.Res.pure_ne_trap,
        Opt.Frame.get_ne_trap, false_or, or_false, and_false, exists_false] at h
  all_goals
    repeat (first | (obtain ⟨_, _, h⟩ := h) | (split at h) |
      (simp only [Opt.Res.bind_eq_ok, Opt.Res.pure_eq_ok, Prod.mk.injEq,
        Opt.Res.ofOption_eq_ok, Opt.Res.bind_eq_trap, Opt.Res.ofOption_ne_trap,
        Opt.Res.pure_ne_trap, or_false, and_false, exists_false] at h))
  all_goals grind

/-- Calls are mandatory, so eligible omissions use the ordinary source
instruction semantics even when the surrounding simulation models callees. -/
theorem mustLower_outcome_quiet {env : Clif.Env} {p : Clif.Program}
    {fr : Clif.Frame} {mem : Clif.Mem} {inst : Clif.Inst} (hm : mustLower inst = false) :
    (∀ vals mem', instOutcome env p fr mem inst = .ok (vals, mem') → mem' = mem) ∧
      ∀ c, instOutcome env p fr mem inst ≠ .trap c := by
  cases inst <;> first
    | (simp [mustLower] at hm; done)
    | simpa only [instOutcome] using (mustLower_quiet (fr := fr) (mem := mem) hm)

/-- Binding ignored source results leaves the availability relation unchanged
for the demanded set. No injectivity or source-ID/register-number equality is
needed: the source frame is equal at every demanded value. -/
theorem ValuesHeld.omittedResults {ctx : Ctx} {fr : Clif.Frame} {ρ : Nat → CV}
    {st : State} {results : List Nat} {vals : List Clif.Val} {regs : Clif.Regs}
    (hzero : ∀ x ∈ results, st.demand[x]! = 0)
    (hset : fr.regs.setMany results vals = some regs) :
    ValuesHeld (Demanded st) ctx { fr with regs := regs } ρ ↔
      ValuesHeld (Demanded st) ctx fr ρ := by
  have hkeep : ∀ x, Demanded st x → regs x = fr.regs x := by
    intro x hx
    apply setMany_other hset
    intro hin
    exact hx (hzero x hin)
  constructor <;> intro h x hx v hv
  · apply h x hx v
    change regs x = some v
    rw [hkeep x hx]
    exact hv
  · apply h x hx v
    change regs x = some v at hv
    rwa [hkeep x hx] at hv

/-- An actual accepted omission is a local semantic stutter: its source result
bindings preserve all demanded values, successful evaluation preserves memory,
traps cannot be lost, and no machine instruction is emitted. -/
theorem scan_omitted_semantic {ctx : Ctx} {block i ti : Nat} {isBranch : Bool}
    {input : State} {output : Scan} {step : Step} {info : IInfo} {inst : Clif.Inst}
    {fr : Clif.Frame} {cm : Clif.Mem} {vals : List Clif.Val} {regs : Clif.Regs}
    {env : Clif.Env} {p : Clif.Program} {ρ : Nat → CV}
    (hscan : scanInstruction ctx block i ti isBranch input = .ok output)
    (hstep : output.step = some step) (hd : step.decision = .omitted)
    (hi : ctx.insts[i]? = some info) (hcl : info.clif = some inst)
    (hset : fr.regs.setMany info.results vals = some regs) :
    output.state = scanState input i ∧
      (∀ vals mem', instOutcome env p fr cm inst = .ok (vals, mem') → mem' = cm) ∧
      (∀ c, instOutcome env p fr cm inst ≠ .trap c) ∧
      (ValuesHeld (Demanded input) ctx { fr with regs := regs } ρ ↔
        ValuesHeld (Demanded input) ctx fr ρ) ∧ output.emitted = #[] := by
  have facts := scan_omitted hscan hstep hd
  have hinfo : ctx.insts[i]! = info := by
    have ht := (Array.getElem?_eq_some_iff.mp hi).1
    rw [_root_.getElem!_pos _ i ht]
    exact (Array.getElem?_eq_some_iff.mp hi).2
  have hm : mustLower inst = false := by
    simpa only [hinfo, hcl, Option.any_some] using facts.2.1
  have hquiet := mustLower_outcome_quiet (env := env) (p := p) (fr := fr) (mem := cm) hm
  exact ⟨facts.2.2.2.2.2.2.2.2, hquiet.1, hquiet.2,
    ValuesHeld.omittedResults (by simpa only [hinfo] using facts.2.2.1) hset,
    facts.2.2.2.2.2.2.2.1⟩

/-! The source executes a real nontrapping load, yielding 9. Its result v0 is
ignored, while demanded pointer v1 remains held by vreg 193. The machine does
not have to materialize 9 into vreg 192. -/

private def omittedLoad : Clif.Inst := .load .load .i8 { trapCode := none } 1 0

private def omittedFrame : Clif.Frame := {
  func := unusedCtx.func
  regs := fun x => if x = 1 then some (.ofInt .i64 100) else none
  slots := []
  body := [⟨[0], omittedLoad⟩]
  term := .ret [1] }

private def omittedMem : Clif.Mem := {
  allocs := [⟨100, 1, false⟩]
  bytes := fun x => if x = 100 then some 9 else none }

private def omittedRegs : Clif.Regs := omittedFrame.regs.set 0 (.ofInt .i8 9)

private def omittedInput : State := { unusedInput with demand := #[0, 1] }

private def omittedOutput : Scan :=
  let st := scanState omittedInput 0
  ⟨st, some ⟨0, 0, .omitted, st, st, [], [], #[]⟩, #[]⟩

private def omittedStep : Step := omittedOutput.step.getD default

private def omittedRF (n : Nat) : CV := if n = 193 then 100 else 0

private theorem omitted_held : ValuesHeld (Demanded omittedInput) unusedCtx omittedFrame omittedRF := by
  intro x _ v hv
  by_cases hx : x = 1
  · subst x
    change some (Clif.Val.ofInt .i64 100) = some v at hv
    cases hv
    exact ⟨193, rfl, by unfold VHolds; decide⟩
  · simp [omittedFrame, hx] at hv

private theorem omitted_scan : scanInstruction unusedCtx 0 0 1 false omittedInput =
    .ok omittedOutput := rfl

private theorem omitted_eval : Clif.evalInst omittedFrame omittedMem omittedLoad =
    .ok ([Clif.Val.ofInt .i8 9], omittedMem) := rfl

theorem mustLower_quiet_witness :
    mustLower omittedLoad = false ∧
    Clif.evalInst omittedFrame omittedMem omittedLoad = .ok ([Clif.Val.ofInt .i8 9], omittedMem) ∧
    (∀ c, Clif.evalInst omittedFrame omittedMem omittedLoad ≠ .trap c) ∧
    (∀ c, Clif.evalInst omittedFrame Clif.Mem.empty omittedLoad ≠ .trap c) :=
  ⟨rfl, omitted_eval, (mustLower_quiet (fr := omittedFrame) (mem := omittedMem) rfl).2,
    (mustLower_quiet (fr := omittedFrame) (mem := Clif.Mem.empty) rfl).2⟩

theorem mustLower_outcome_quiet_witness :
    mustLower omittedLoad = false ∧
    instOutcome Clif.Env.empty { funcs := [] } omittedFrame omittedMem omittedLoad =
      .ok ([Clif.Val.ofInt .i8 9], omittedMem) ∧
    (∀ c, instOutcome Clif.Env.empty { funcs := [] } omittedFrame omittedMem omittedLoad ≠ .trap c) :=
  ⟨rfl, omitted_eval, (mustLower_outcome_quiet
    (env := Clif.Env.empty) (p := { funcs := [] }) (fr := omittedFrame) (mem := omittedMem) rfl).2⟩

theorem ValuesHeld.omittedResults_witness :
    omittedFrame.regs.setMany [0] [Clif.Val.ofInt .i8 9] = some omittedRegs ∧
    (ValuesHeld (Demanded omittedInput) unusedCtx { omittedFrame with regs := omittedRegs } omittedRF ↔
      ValuesHeld (Demanded omittedInput) unusedCtx omittedFrame omittedRF) ∧
    ValuesHeld (Demanded omittedInput) unusedCtx { omittedFrame with regs := omittedRegs } omittedRF ∧
    omittedRegs 0 = some (.ofInt .i8 9) ∧ ¬VHolds (.ofInt .i8 9) (omittedRF 192) := by
  have hi := ValuesHeld.omittedResults (ctx := unusedCtx) (fr := omittedFrame) (ρ := omittedRF)
    (st := omittedInput) (results := [0]) (vals := [.ofInt .i8 9]) (regs := omittedRegs)
    (by intro x hx; simp only [List.mem_singleton] at hx; subst x; rfl) rfl
  exact ⟨rfl, hi, hi.mpr omitted_held, rfl, by unfold VHolds; decide⟩

theorem scan_omitted_semantic_witness :
    scanInstruction unusedCtx 0 0 1 false omittedInput = .ok omittedOutput ∧
    instOutcome Clif.Env.empty { funcs := [] } omittedFrame omittedMem omittedLoad =
      .ok ([Clif.Val.ofInt .i8 9], omittedMem) ∧
    (∀ c, instOutcome Clif.Env.empty { funcs := [] } omittedFrame omittedMem omittedLoad ≠ .trap c) ∧
    ValuesHeld (Demanded omittedInput) unusedCtx { omittedFrame with regs := omittedRegs } omittedRF ∧
    omittedOutput.emitted = #[] := by
  have h := scan_omitted_semantic (step := omittedStep) (info := unusedCtx.insts[0]!)
    (ρ := omittedRF) (regs := omittedRegs) (env := Clif.Env.empty) (p := { funcs := [] })
    omitted_scan rfl rfl rfl rfl rfl
  exact ⟨omitted_scan, omitted_eval, h.2.2.1, h.2.2.2.1.mpr omitted_held, h.2.2.2.2⟩

end Backend.Stock.Proof
