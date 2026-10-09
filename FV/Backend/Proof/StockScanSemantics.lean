import FV.Backend.Proof.StockAliasSemantics
import FV.Backend.Proof.StockBlockScan
import FV.Backend.Proof.StockOmission
import FV.Backend.Proof.IselCmpRun

/-! Semantic composition of actual backward-scan records in source execution
order. Step obligations are internal proof obligations for selected rules and
omissions; they do not introduce a new compiler checker or source condition.
This module covers successful fall-through; trapping/sinking simulation still
requires its deferred-effect invariant. -/

namespace Backend.Stock.Proof

open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64

/-- Source steps indexed by the original context, in execution order. -/
inductive SourceSteps {S : Type} (step : Nat → S → S → Prop) : List Nat → S → S → Prop where
  | nil (s : S) : SourceSteps step [] s s
  | cons {i : Nat} {indices : List Nat} {s s1 s2 : S}
      (head : step i s s1) (tail : SourceSteps step indices s1 s2) :
      SourceSteps step (i :: indices) s s2

private theorem sourceSteps_append {S : Type} {step : Nat → S → S → Prop}
    {xs ys : List Nat} {s t : S} :
    SourceSteps step (xs ++ ys) s t ↔
      ∃ u, SourceSteps step xs s u ∧ SourceSteps step ys u t := by
  induction xs generalizing s with
  | nil =>
    constructor
    · intro h; exact ⟨s, .nil s, h⟩
    · rintro ⟨u, hu, h⟩; cases hu; exact h
  | cons i xs ih =>
    constructor
    · intro h
      cases h with
      | cons head tail =>
        obtain ⟨u, hx, hy⟩ := ih.mp tail
        exact ⟨u, .cons head hx, hy⟩
    · rintro ⟨u, hx, hy⟩
      cases hx with
      | cons head tail => exact .cons head (ih.mpr ⟨u, tail, hy⟩)

/-- Relate source states and machine states using the demand set at each scan
boundary. A forward step goes from the backward scan's output to its input. -/
def ScanFallRefines {S W : Type} (source : Nat → S → S → Prop)
    (sem : ISem CV W) (aliases : Array (Option Nat))
    (rel : State → S → (Nat → CV) → W → Prop) (record : ScanRecord) : Prop :=
  ∀ s s', source record.inst s s' → ∀ ρ w,
    rel record.output.state s ρ w → ∃ ρ' w',
      seqRun sem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size + 1)))) ρ w = some (.fall ρ' w') ∧
      rel record.input s' ρ' w'

/-- Compose the real recorded chunks in forward order, even though their states
and demands were constructed backward. Memory/world relations are carried by
`rel`, so this also permits effects rather than requiring a pure `PRun`. -/
theorem ScansSpec.fall_refines {S W : Type} {exec : Nat → State → Except String Scan}
    {source : Nat → S → S → Prop} {sem : ISem CV W} {aliases : Array (Option Nat)}
    {rel : State → S → (Nat → CV) → W → Prop}
    {indices : List Nat} {input : State} {output : BlockScan}
    (hscan : ScansSpec exec indices input output)
    (hlocal : ∀ r ∈ output.records, ScanFallRefines source sem aliases rel r) :
    ∀ s s', SourceSteps source indices.reverse s s' → ∀ ρ w,
      rel output.state s ρ w → ∃ ρ' w',
        seqRun sem (output.code.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve aliases (aliases.size + 1)))) ρ w = some (.fall ρ' w') ∧
        rel input s' ρ' w' := by
  induction hscan with
  | nil input =>
    intro s s' hs ρ w hrel
    cases hs
    exact ⟨ρ, w, rfl, hrel⟩
  | @cons i indices input scan tail hhead hrest ih =>
    intro s s' hs ρ w hrel
    have hsplit : SourceSteps source (indices.reverse ++ [i]) s s' := by
      simpa only [List.reverse_cons] using hs
    obtain ⟨mid, hfront, hlast⟩ := sourceSteps_append.mp hsplit
    obtain ⟨ρ1, w1, hr1, hrel1⟩ := ih
      (fun r hr => hlocal r (List.mem_cons_of_mem _ hr)) s mid hfront ρ w hrel
    cases hlast with
    | cons last done =>
      cases done
      obtain ⟨ρ', w', hr, hrel'⟩ := hlocal ⟨i, input, scan⟩ (List.mem_cons_self ..)
        mid s' last ρ1 w1 hrel1
      refine ⟨ρ', w', ?_, hrel'⟩
      simp only [Array.toList_append, List.map_append]
      exact seqRun_append_fall' sem hr1 hr

/-- Actual `scanBlock` satisfies the composition theorem without replay/checker
acceptance as a premise. Its per-record semantic obligations are discharged by
the selected-rule and omission proofs, not imposed on accepted programs. -/
theorem stock_scanBlock_fall_refines {S W : Type} {ctx : Ctx} {block ti : Nat}
    {isBranch : Bool} {source : Nat → S → S → Prop} {sem : ISem CV W}
    {aliases : Array (Option Nat)} {rel : State → S → (Nat → CV) → W → Prop}
    {indices : List Nat} {input : State} {output : BlockScan}
    (hscan : scanBlock ctx block ti isBranch indices input = .ok output)
    (hlocal : ∀ r ∈ output.records, ScanFallRefines source sem aliases rel r) :
    ∀ s s', SourceSteps source indices.reverse s s' → ∀ ρ w,
      rel output.state s ρ w → ∃ ρ' w',
        seqRun sem (output.code.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve aliases (aliases.size + 1)))) ρ w = some (.fall ρ' w') ∧
        rel input s' ρ' w' :=
  (runScans_spec hscan).fall_refines hlocal

/-- Successful ordinary source instruction evaluation with its actual result
bindings. Calls use the established `instOutcome` interpretation. -/
def SourceInstResult (env : Clif.Env) (p : Clif.Program) (ctx : Ctx) (i : Nat)
    (s s' : Clif.Frame × Clif.Mem) : Prop :=
  ∃ info inst vals regs rest, ctx.insts[i]? = some info ∧ info.clif = some inst ∧
    s.1.body = ⟨info.results, inst⟩ :: rest ∧
    instOutcome env p s.1 s.2 inst = .ok (vals, s'.2) ∧
    s.1.regs.setMany info.results vals = some regs ∧
    s'.1 = { s.1 with regs := regs, body := rest }

/-- An actual omitted scan discharges the forward transfer obligation through
an arbitrary final alias resolver and source/machine memory relation. -/
theorem stock_omitted_fall_refines {W : Type} {ctx : Ctx} {block i ti : Nat}
    {isBranch : Bool} {input : State} {output : Scan} {step : Step}
    {env : Clif.Env} {p : Clif.Program} {sem : ISem CV W}
    {aliases : Array (Option Nat)} {MR : Clif.Mem → W → Prop}
    (hscan : scanInstruction ctx block i ti isBranch input = .ok output)
    (hstep : output.step = some step) (hd : step.decision = .omitted) :
    ScanFallRefines (SourceInstResult env p ctx) sem aliases
      (fun st s ρ w => MR s.2 w ∧ ValuesHeld (Demanded st) ctx s.1
        (fun k => ρ (aliasNum aliases k))) ⟨i, input, output⟩ := by
  intro s s' hsource ρ w hrel
  obtain ⟨info, inst, vals, regs, rest, hi, hic, _, heval, hset, hfr⟩ := hsource
  have facts := scan_omitted_semantic (ρ := fun k => ρ (aliasNum aliases k)) (env := env) (p := p) (cm := s.2)
    hscan hstep hd hi hic hset
  have hmem : s'.2 = s.2 := facts.2.1 _ _ heval
  have hheld : ValuesHeld (Demanded input) ctx s.1
      (fun k => ρ (aliasNum aliases k)) := by
    simpa only [facts.1, ValuesHeld, Demanded, scanState_demands] using hrel.2
  refine ⟨ρ, w, ?_, ?_, ?_⟩
  · simp only [facts.2.2.2.2, Array.toList_empty, List.map_nil, seqRun]
  · rw [hmem]; exact hrel.1
  · rw [hfr]
    exact facts.2.2.2.1.mpr hheld

private theorem quiet_source_step {env : Clif.Env} {p : Clif.Program}
    {fr : Clif.Frame} {cm cm' : Clif.Mem} {inst : Clif.Inst} {results : List Nat}
    {vals : List Clif.Val} {regs : Clif.Regs} {rest : List Clif.Stmt}
    (hm : mustLower inst = false) (hbody : fr.body = ⟨results, inst⟩ :: rest)
    (heval : instOutcome env p fr cm inst = .ok (vals, cm'))
    (hset : fr.regs.setMany results vals = some regs)
    (callers : List (Clif.Frame × List Nat)) :
    Clif.step env p { frame := fr, callers, mem := cm } =
      .next { frame := { fr with regs := regs, body := rest }, callers, mem := cm' } := by
  cases inst <;> first
    | (simp only [mustLower, Bool.true_eq_false] at hm; done)
    | (simp only [Clif.step, hbody, instOutcome] at heval ⊢
       rw [heval]
       simp only [Clif.StepResult.ofRes_ok, Clif.continueWith, hset])

/-- The source transition used for an actual omission is the original CLIF
small step, including consumption of the source body and unchanged callers. -/
theorem stock_omitted_source_step {ctx : Ctx} {block i ti : Nat} {isBranch : Bool}
    {input : State} {output : Scan} {step : Step} {env : Clif.Env} {p : Clif.Program}
    {s s' : Clif.Frame × Clif.Mem}
    (hscan : scanInstruction ctx block i ti isBranch input = .ok output)
    (hstep : output.step = some step) (hd : step.decision = .omitted)
    (hsource : SourceInstResult env p ctx i s s')
    (callers : List (Clif.Frame × List Nat)) :
    Clif.step env p { frame := s.1, callers, mem := s.2 } =
      .next { frame := s'.1, callers, mem := s'.2 } := by
  obtain ⟨info, inst, vals, regs, rest, hi, hic, hbody, heval, hset, hfr⟩ := hsource
  have facts := scan_omitted hscan hstep hd
  have hinfo : ctx.insts[i]! = info := by
    have ht := (Array.getElem?_eq_some_iff.mp hi).1
    rw [_root_.getElem!_pos _ i ht]
    exact (Array.getElem?_eq_some_iff.mp hi).2
  have hm : mustLower inst = false := by
    simpa only [hinfo, hic, Option.any_some] using facts.2.1
  rw [hfr]
  exact quiet_source_step hm hbody heval hset callers

private theorem scans_executions {exec : Nat → State → Except String Scan}
    {indices : List Nat} {input : State} {output : BlockScan}
    (h : ScansSpec exec indices input output) :
    ∀ r ∈ output.records, exec r.inst r.input = .ok r.output := by
  induction h with
  | nil input => simp
  | cons head rest ih =>
    intro r hr
    simp only [List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact head
    · exact ih r hr

/-- All-omitted actual blocks need no semantic rule oracle: local replay-free
scan facts discharge every step of the forward source/machine composition. -/
theorem stock_omittedBlock_fall_refines {W : Type} {ctx : Ctx} {block ti : Nat}
    {isBranch : Bool} {env : Clif.Env} {p : Clif.Program} {sem : ISem CV W}
    {aliases : Array (Option Nat)} {MR : Clif.Mem → W → Prop}
    {indices : List Nat} {input : State} {output : BlockScan}
    (hscan : scanBlock ctx block ti isBranch indices input = .ok output)
    (homitted : ∀ r ∈ output.records, ∃ step, r.output.step = some step ∧
      step.decision = .omitted) :
    ∀ s s', SourceSteps (SourceInstResult env p ctx) indices.reverse s s' → ∀ ρ w,
      MR s.2 w → ValuesHeld (Demanded output.state) ctx s.1
        (fun k => ρ (aliasNum aliases k)) → ∃ ρ' w',
          seqRun sem (output.code.toList.map (·.mapRegs
            (Backend.lowerFunction.resolve aliases (aliases.size + 1)))) ρ w = some (.fall ρ' w') ∧
          MR s'.2 w' ∧ ValuesHeld (Demanded input) ctx s'.1
            (fun k => ρ' (aliasNum aliases k)) := by
  have cert := runScans_spec hscan
  have hlocal : ∀ r ∈ output.records,
      ScanFallRefines (SourceInstResult env p ctx) sem aliases
        (fun st s ρ w => MR s.2 w ∧ ValuesHeld (Demanded st) ctx s.1
          (fun k => ρ (aliasNum aliases k))) r := by
    intro r hr
    obtain ⟨step, hs, hd⟩ := homitted r hr
    exact stock_omitted_fall_refines (scans_executions cert r hr) hs hd
  intro s s' hsource ρ w hmem hheld
  exact cert.fall_refines hlocal s s' hsource ρ w ⟨hmem, hheld⟩

/-! A producer allocated after its consumer executes first. The actual final
resolver redirects source vreg 193 to the producer's later vreg 195. -/

private def scanAliases : Array (Option Nat) := aliasStep #[] (193, 195)

set_option maxRecDepth 2048 in
private theorem scan_alias_facts :
    aliasNum scanAliases 192 = 192 ∧ aliasNum scanAliases 193 = 195 ∧
      aliasNum scanAliases 194 = 194 ∧ aliasNum scanAliases 195 = 195 := by decide

private def producerCode : MInst :=
  .aluRRImm12 .add .size64 (.vreg 195 .int) (.vreg 192 .int) ⟨1, false⟩

private def consumerCode : MInst :=
  .aluRRImm12 .add .size64 (.vreg 194 .int) (.vreg 193 .int) ⟨1, false⟩

private theorem producer_resolved :
    producerCode.mapRegs (Backend.lowerFunction.resolve scanAliases (scanAliases.size + 1)) =
      producerCode := by
  change MInst.aluRRImm12 .add .size64
    (Backend.lowerFunction.resolve scanAliases (scanAliases.size + 1) (.vreg 195 .int))
    (Backend.lowerFunction.resolve scanAliases (scanAliases.size + 1) (.vreg 192 .int)) _ = _
  rw [resolve_vreg, resolve_vreg]
  change MInst.aluRRImm12 .add .size64 (.vreg (aliasNum scanAliases 195) .int)
    (.vreg (aliasNum scanAliases 192) .int) _ = _
  rw [scan_alias_facts.2.2.2, scan_alias_facts.1]
  rfl

private theorem consumer_resolved :
    consumerCode.mapRegs (Backend.lowerFunction.resolve scanAliases (scanAliases.size + 1)) =
      .aluRRImm12 .add .size64 (.vreg 194 .int) (.vreg 195 .int) ⟨1, false⟩ := by
  change MInst.aluRRImm12 .add .size64
    (Backend.lowerFunction.resolve scanAliases (scanAliases.size + 1) (.vreg 194 .int))
    (Backend.lowerFunction.resolve scanAliases (scanAliases.size + 1) (.vreg 193 .int)) _ = _
  rw [resolve_vreg, resolve_vreg]
  change MInst.aluRRImm12 .add .size64 (.vreg (aliasNum scanAliases 194) .int)
    (.vreg (aliasNum scanAliases 193) .int) _ = _
  rw [scan_alias_facts.2.2.1, scan_alias_facts.2.1]

private def scanEnd : State := { sinkState with current := some 1 }
private def scanMiddle : State := { sinkState with current := some 0 }
private def scanStart : State := { sinkState with current := none }

private def consumerScan : Scan := ⟨scanMiddle, none, #[consumerCode]⟩
private def producerScan : Scan := ⟨scanStart, none, #[producerCode]⟩

private def exampleExec (i : Nat) (_ : State) : Except String Scan :=
  .ok (if i = 1 then consumerScan else producerScan)

private def exampleBlock : BlockScan :=
  ⟨scanStart, [⟨1, scanEnd, consumerScan⟩, ⟨0, scanMiddle, producerScan⟩],
    #[producerCode, consumerCode]⟩

private theorem example_spec : ScansSpec exampleExec [1, 0] scanEnd exampleBlock := by
  have hc : exampleExec 1 scanEnd = .ok consumerScan := rfl
  have hp : exampleExec 0 scanMiddle = .ok producerScan := rfl
  exact .cons hc (.cons hp (.nil scanStart))

private def addOne (x : CV) : CV :=
  resX .size64 (opnd .size64 x + BitVec.ofNat _ 1)

private theorem add_one_run (d a : Nat) (ρ : Nat → CV) (w : Arm.ArmState) :
    seqRun ispec [.aluRRImm12 .add .size64 (.vreg d .int) (.vreg a .int) ⟨1, false⟩] ρ w =
      some (.fall (upd ρ d (addOne (ρ a))) w) := rfl

private def exampleSource (_ : Nat) (s t : CV) : Prop := t = addOne s

private def exampleRel (st : State) (s : CV) (ρ : Nat → CV) (_ : Arm.ArmState) : Prop :=
  if st.current = some 1 then ρ 194 = s
  else if st.current = some 0 then ρ 195 = s else ρ 192 = s

private theorem example_local :
    ∀ r ∈ exampleBlock.records, ScanFallRefines exampleSource ispec scanAliases exampleRel r := by
  intro r hr
  change r ∈ [⟨1, scanEnd, consumerScan⟩, ⟨0, scanMiddle, producerScan⟩] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · intro s t hsource ρ w hrel
    change t = addOne s at hsource
    change ρ 195 = s at hrel
    refine ⟨upd ρ 194 (addOne (ρ 195)), w, ?_, ?_⟩
    · change seqRun ispec [consumerCode.mapRegs
        (Backend.lowerFunction.resolve scanAliases (scanAliases.size + 1))] ρ w = _
      rw [consumer_resolved]
      exact add_one_run _ _ _ _
    · change upd ρ 194 (addOne (ρ 195)) 194 = t
      simp only [upd, ite_true, hrel, hsource]
  · intro s t hsource ρ w hrel
    change t = addOne s at hsource
    change ρ 192 = s at hrel
    refine ⟨upd ρ 195 (addOne (ρ 192)), w, ?_, ?_⟩
    · change seqRun ispec [producerCode.mapRegs
        (Backend.lowerFunction.resolve scanAliases (scanAliases.size + 1))] ρ w = _
      rw [producer_resolved]
      exact add_one_run _ _ _ _
    · change upd ρ 195 (addOne (ρ 192)) 195 = t
      simp only [upd, ite_true, hrel, hsource]

private def exampleRF (n : Nat) : CV := if n = 192 then 11 else 0

private theorem example_source_steps : SourceSteps exampleSource [0, 1] 11 13 :=
  .cons (by rfl) (.cons (by rfl) (.nil 13))

theorem ScansSpec.fall_refines_witness :
    ScansSpec exampleExec [1, 0] scanEnd exampleBlock ∧
      SourceSteps exampleSource [0, 1] 11 13 ∧
      exampleBlock.code = #[producerCode, consumerCode] ∧
      aliasNum scanAliases 193 = 195 ∧
      ∃ ρ' w', seqRun ispec (exampleBlock.code.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve scanAliases (scanAliases.size + 1))))
          exampleRF Arm.ArmState.default = some (.fall ρ' w') ∧ ρ' 194 = 13 := by
  obtain ⟨ρ', w', hr, hrel⟩ := example_spec.fall_refines example_local
    11 13 example_source_steps exampleRF Arm.ArmState.default (by rfl)
  exact ⟨example_spec, example_source_steps, rfl, scan_alias_facts.2.1, ρ', w', hr, hrel⟩

/-! A real omitted nontrapping load executes in the source while the demanded
pointer is retained and the selected machine code stays empty. -/

private def loadInput : State := { unusedInput with demand := #[0, 1] }
private def loadOutput : Scan :=
  let before := scanState loadInput 0
  ⟨before, some ⟨0, 0, .omitted, before, before, [], [], #[]⟩, #[]⟩
private def loadStep : Step := loadOutput.step.getD default

private theorem load_scan : scanInstruction unusedCtx 0 0 1 false loadInput = .ok loadOutput := rfl

private def loadFrame : Clif.Frame := {
  func := unusedCtx.func, regs := fun x => if x = 1 then some (.ofInt .i64 100) else none,
  slots := [], body := [⟨[0], .load .load .i8 { trapCode := none } 1 0⟩], term := .ret [1] }

private def loadMem : Clif.Mem := {
  allocs := [⟨100, 1, false⟩], bytes := fun x => if x = 100 then some 9 else none }

private def loadedFrame : Clif.Frame :=
  { loadFrame with regs := loadFrame.regs.set 0 (.ofInt .i8 9), body := [] }
private def loadRF (n : Nat) : CV := if n = 193 then 100 else 0

private def loadRel (st : State) (s : Clif.Frame × Clif.Mem) (ρ : Nat → CV) (_ : Unit) : Prop :=
  s.2 = loadMem ∧ ValuesHeld (Demanded st) unusedCtx s.1 (fun k => ρ (aliasNum #[] k))

private theorem load_source :
    SourceInstResult Clif.Env.empty { funcs := [] } unusedCtx 0
      (loadFrame, loadMem) (loadedFrame, loadMem) :=
  ⟨unusedCtx.insts[0]!, .load .load .i8 { trapCode := none } 1 0, [.ofInt .i8 9],
    loadedFrame.regs, [], rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem load_start_held : loadRel loadOutput.state (loadFrame, loadMem) loadRF () := by
  refine ⟨rfl, ?_⟩
  intro x hx v hv
  by_cases he : x = 1
  · subst x
    change some (Clif.Val.ofInt .i64 100) = some v at hv
    cases hv
    exact ⟨193, rfl, by unfold VHolds aliasNum chaseF loadRF; decide⟩
  · simp [loadFrame, he] at hv

private theorem load_local {sem : ISem CV Unit} :
    ScanFallRefines (SourceInstResult Clif.Env.empty { funcs := [] } unusedCtx)
      sem #[] loadRel ⟨0, loadInput, loadOutput⟩ :=
  stock_omitted_fall_refines (MR := fun cm _ => cm = loadMem) (step := loadStep)
    load_scan rfl rfl

theorem stock_omitted_fall_refines_witness :
    scanInstruction unusedCtx 0 0 1 false loadInput = .ok loadOutput ∧
      SourceInstResult Clif.Env.empty { funcs := [] } unusedCtx 0
        (loadFrame, loadMem) (loadedFrame, loadMem) ∧
      loadedFrame.regs 0 = some (.ofInt .i8 9) ∧
      ∃ ρ', seqRun (fun (_ : MInst) (_ : List CV) (w : Unit) => some ([], w, .next))
          loadOutput.emitted.toList loadRF () = some (.fall ρ' ()) ∧
        loadRel loadInput (loadedFrame, loadMem) ρ' () ∧
        ¬VHolds (Clif.Val.ofInt .i8 9) (ρ' 192) := by
  obtain ⟨ρ', w', hr, hrel⟩ := load_local
    (sem := fun _ _ w => some ([], w, .next))
    (loadFrame, loadMem) (loadedFrame, loadMem) load_source loadRF () load_start_held
  have he : ρ' = loadRF := by
    change some (SeqEnd.fall loadRF ()) = some (.fall ρ' w') at hr
    exact (SeqEnd.fall.inj (Option.some.inj hr)).1.symm
  subst ρ'
  exact ⟨load_scan, load_source, rfl, loadRF, hr, hrel, by unfold VHolds loadRF; decide⟩

private def loadBlock : BlockScan :=
  ⟨loadOutput.state, [⟨0, loadInput, loadOutput⟩], #[]⟩

private theorem load_block_scan : scanBlock unusedCtx 0 1 false [0] loadInput = .ok loadBlock := by
  unfold scanBlock
  rw [runScans_ref]
  simp only [runScansRef, load_scan, bind, Except.bind, pure, Except.pure]
  rfl

theorem stock_scanBlock_fall_refines_witness :
    scanBlock unusedCtx 0 1 false [0] loadInput = .ok loadBlock ∧
      SourceSteps (SourceInstResult Clif.Env.empty { funcs := [] } unusedCtx) [0]
        (loadFrame, loadMem) (loadedFrame, loadMem) ∧
      ∃ ρ', seqRun (fun (_ : MInst) (_ : List CV) (w : Unit) => some ([], w, .next))
          loadBlock.code.toList loadRF () = some (.fall ρ' ()) ∧
        loadRel loadInput (loadedFrame, loadMem) ρ' () := by
  have hsource : SourceSteps (SourceInstResult Clif.Env.empty { funcs := [] } unusedCtx)
      [0] (loadFrame, loadMem) (loadedFrame, loadMem) := .cons load_source (.nil _)
  have hlocal : ∀ r ∈ loadBlock.records,
      ScanFallRefines (SourceInstResult Clif.Env.empty { funcs := [] } unusedCtx)
        (fun _ _ w => some ([], w, .next)) #[] loadRel r := by
    intro r hr
    change r ∈ [⟨0, loadInput, loadOutput⟩] at hr
    simp only [List.mem_singleton] at hr
    subst r
    exact load_local
  obtain ⟨ρ', w', hr, hrel⟩ := stock_scanBlock_fall_refines load_block_scan hlocal
    (loadFrame, loadMem) (loadedFrame, loadMem) hsource loadRF () load_start_held
  exact ⟨load_block_scan, hsource, ρ', hr, hrel⟩

theorem stock_omitted_source_step_witness :
    SourceInstResult Clif.Env.empty { funcs := [] } unusedCtx 0
      (loadFrame, loadMem) (loadedFrame, loadMem) ∧
      Clif.step Clif.Env.empty { funcs := [] }
        { frame := loadFrame, callers := [], mem := loadMem } =
        .next { frame := loadedFrame, callers := [], mem := loadMem } ∧
      loadFrame.body.length = 1 ∧ loadedFrame.body = [] ∧
      loadedFrame.regs 0 = some (.ofInt .i8 9) :=
  ⟨load_source, stock_omitted_source_step (step := loadStep) load_scan rfl rfl load_source [],
    rfl, rfl, rfl⟩

theorem stock_omittedBlock_fall_refines_witness :
    scanBlock unusedCtx 0 1 false [0] loadInput = .ok loadBlock ∧
      SourceSteps (SourceInstResult Clif.Env.empty { funcs := [] } unusedCtx) [0]
        (loadFrame, loadMem) (loadedFrame, loadMem) ∧
      ∃ ρ', seqRun (fun (_ : MInst) (_ : List CV) (w : Unit) => some ([], w, .next))
          loadBlock.code.toList loadRF () = some (.fall ρ' ()) ∧
        loadRel loadInput (loadedFrame, loadMem) ρ' () := by
  have hsource : SourceSteps (SourceInstResult Clif.Env.empty { funcs := [] } unusedCtx)
      [0] (loadFrame, loadMem) (loadedFrame, loadMem) := .cons load_source (.nil _)
  have homitted : ∀ r ∈ loadBlock.records, ∃ step, r.output.step = some step ∧
      step.decision = .omitted := by
    intro r hr
    change r ∈ [⟨0, loadInput, loadOutput⟩] at hr
    simp only [List.mem_singleton] at hr
    subst r
    exact ⟨loadStep, rfl, rfl⟩
  obtain ⟨ρ', w', hr, hmem, hheld⟩ := stock_omittedBlock_fall_refines
    (sem := fun _ _ (w : Unit) => some ([], w, .next))
    (MR := fun cm _ => cm = loadMem) (aliases := #[])
    load_block_scan homitted (loadFrame, loadMem) (loadedFrame, loadMem)
    hsource loadRF () load_start_held.1 load_start_held.2
  exact ⟨load_block_scan, hsource, ρ', hr, hmem, hheld⟩

end Backend.Stock.Proof
