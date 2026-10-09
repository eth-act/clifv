import FV.Backend.Proof.StockScanSemantics

/-! Source-side delayed-load obligations. These compare the complete result,
including traps and stuck outcomes. The driver must establish address and memory
stability from its scan invariants; these are not new accepted-input conditions.
-/
namespace Backend.Stock.Proof

/-- A load has the same result at two source boundaries when its address value
and memory are unchanged, regardless of other registers or remaining body. -/
theorem load_delay_outcome {before after : Clif.Frame} {mem nextMem : Clif.Mem}
    {op : Clif.LoadOp} {ty : Clif.Ty} {flags : Clif.MemFlags} {ptr : Nat} {offset : Int}
    (address : after.regs ptr = before.regs ptr) (memory : nextMem = mem) :
    Clif.evalInst after nextMem (.load op ty flags ptr offset) =
      Clif.evalInst before mem (.load op ty flags ptr offset) := by
  subst nextMem
  simp only [Clif.evalInst, Clif.Frame.get, address]

/-- Stable boundaries compose over an entire source execution window. Equality
of outcomes preserves successful values and traps without assuming success. -/
theorem load_delay_window {S : Type} {step : Nat → S → S → Prop}
    {frame : S → Clif.Frame} {memory : S → Clif.Mem}
    {op : Clif.LoadOp} {ty : Clif.Ty} {flags : Clif.MemFlags} {ptr : Nat} {offset : Int}
    {indices : List Nat} {before after : S}
    (run : SourceSteps step indices before after)
    (stable : ∀ i s t, step i s t →
      (frame t).regs ptr = (frame s).regs ptr ∧ memory t = memory s) :
    Clif.evalInst (frame after) (memory after) (.load op ty flags ptr offset) =
      Clif.evalInst (frame before) (memory before) (.load op ty flags ptr offset) := by
  induction run with
  | nil s => rfl
  | cons head tail ih =>
    obtain ⟨address, mem⟩ := stable _ _ _ head
    exact ih.trans (load_delay_outcome address mem)

/-- An actual quiet source step preserves memory and an address outside its
result list. Thus delay stability follows from evaluation and result binding,
rather than an extra memory-equality premise. -/
theorem load_delay_quiet_step {env : Clif.Env} {p : Clif.Program} {ctx : Ctx}
    {i : Nat} {info : IInfo} {inst : Clif.Inst} {s t : Clif.Frame × Clif.Mem}
    {op : Clif.LoadOp} {ty : Clif.Ty} {flags : Clif.MemFlags} {ptr : Nat} {offset : Int}
    (run : SourceInstResult env p ctx i s t)
    (source : ctx.insts[i]? = some info) (original : info.clif = some inst)
    (quiet : mustLower inst = false) (address : ptr ∉ info.results) :
    t.2 = s.2 ∧ t.1.regs ptr = s.1.regs ptr ∧
    Clif.evalInst t.1 t.2 (.load op ty flags ptr offset) =
      Clif.evalInst s.1 s.2 (.load op ty flags ptr offset) := by
  obtain ⟨info', inst', vals, regs, rest, hi, hic, _, he, hset, hframe⟩ := run
  have sameInfo : info' = info := Option.some.inj (hi.symm.trans source)
  subst info'
  have sameInst : inst' = inst := Option.some.inj (hic.symm.trans original)
  subst inst'
  have mem : t.2 = s.2 := (mustLower_outcome_quiet quiet).1 _ _ he
  have addr : t.1.regs ptr = s.1.regs ptr := by
    rw [hframe]
    exact Backend.Proof.Driver.setMany_other hset address
  exact ⟨mem, addr, load_delay_outcome addr mem⟩

private def delayFrame : Clif.Frame := {
  func := default
  regs := fun n => if n = 1 then some (.ofInt .i64 104) else none
  slots := []
  body := [⟨[2], .iconst .i64 7⟩]
  term := .ret [2] }

private def delayAfter : Clif.Frame := {
  delayFrame with regs := delayFrame.regs.set 2 (.ofInt .i64 7), body := [] }

private def delayMem : Clif.Mem := {
  allocs := [⟨100, 1, false⟩]
  bytes := fun n => if n = 100 then some 128 else none }

private def delayLoad : Clif.Inst := .load .sload8 .i64 {} 1 (-4)

/-- Negative offset and sign extension are retained. The source boundaries
differ in a register and body, and an invalid access retains its trap. -/
theorem load_delay_outcome_witness :
    delayAfter.regs 1 = delayFrame.regs 1 ∧
    delayAfter.regs 2 = some (.ofInt .i64 7) ∧ delayFrame.regs 2 = none ∧
    Clif.evalInst delayAfter delayMem delayLoad =
      Clif.evalInst delayFrame delayMem delayLoad ∧
    Clif.evalInst delayAfter delayMem delayLoad =
      .ok ([.ofInt .i64 (-128)], delayMem) ∧
    Clif.evalInst delayAfter Clif.Mem.empty delayLoad = .trap .heapOob := by
  refine ⟨rfl, rfl, rfl, load_delay_outcome rfl rfl, ?_, ?_⟩ <;> rfl

private def delayStep (_ : Nat) (s t : Clif.Frame × Clif.Mem) : Prop :=
  Clif.step Clif.Env.empty { funcs := [] } { frame := s.1, callers := [], mem := s.2 } =
    .next { frame := t.1, callers := [], mem := t.2 } ∧
  t.1.regs 1 = s.1.regs 1 ∧ t.2 = s.2

/-- An actual CLIF constant step inhabits the intervening execution window. -/
theorem load_delay_window_witness :
    SourceSteps delayStep [0] (delayFrame, delayMem) (delayAfter, delayMem) ∧
    Clif.evalInst delayAfter delayMem delayLoad =
      Clif.evalInst delayFrame delayMem delayLoad ∧
    Clif.evalInst delayAfter delayMem delayLoad =
      .ok ([.ofInt .i64 (-128)], delayMem) := by
  have run : SourceSteps delayStep [0] (delayFrame, delayMem) (delayAfter, delayMem) :=
    .cons (s1 := (delayAfter, delayMem)) ⟨rfl, rfl, rfl⟩ (.nil _)
  exact ⟨run, load_delay_window run (fun _ _ _ h => h.2), rfl⟩

private def quietCtx : Ctx := { unusedCtx with
  insts := #[⟨default, [2], [.int 64], some (.iconst .i64 7)⟩] }

/-- Original source evaluation/result binding, rather than a supplied stability
assertion, establishes the intervening step's memory and address preservation. -/
theorem load_delay_quiet_step_witness :
    SourceInstResult Clif.Env.empty { funcs := [] } quietCtx 0
      (delayFrame, delayMem) (delayAfter, delayMem) ∧
    delayAfter.regs 1 = delayFrame.regs 1 ∧
    Clif.evalInst delayAfter delayMem delayLoad =
      Clif.evalInst delayFrame delayMem delayLoad := by
  have run : SourceInstResult Clif.Env.empty { funcs := [] } quietCtx 0
      (delayFrame, delayMem) (delayAfter, delayMem) :=
    ⟨quietCtx.insts[0]!, .iconst .i64 7, [.ofInt .i64 7], delayAfter.regs, [],
      rfl, rfl, rfl, rfl, rfl, rfl⟩
  have facts := load_delay_quiet_step (op := .sload8) (ty := .i64) (flags := {})
    (ptr := 1) (offset := -4) run (info := quietCtx.insts[0]!) rfl
    (inst := .iconst .i64 7) rfl rfl (by decide)
  exact ⟨run, facts.2.1, facts.2.2⟩

/-- Stock's uncolored instructions are never mandatory, including the possible
traps and memory operations classified by its actual predicate. -/
theorem uncolored_quiet {inst : Clif.Inst} (h : colored inst = false) :
    mustLower inst = false := by
  unfold colored at h
  exact (Bool.or_eq_false_iff.mp h).1

/-- The color counter's source-body advance. Each colored operation increments
it once, just as the body loop in `sourceMetadata`. -/
def colorAdvance : List Clif.Inst → Nat → Nat
  | [], c => c
  | inst :: rest, c => colorAdvance rest (if colored inst then c + 1 else c)

/-- An unchanged counter cannot conceal an intervening ordering barrier. This
is the arithmetic component of the metadata invariant, not yet its derivation
from a successful buildCtx or sink call. -/
theorem colorAdvance_unchanged (insts : List Clif.Inst) (c : Nat) :
    colorAdvance insts c = c ↔ ∀ inst ∈ insts, colored inst = false := by
  have monotone (xs : List Clif.Inst) (n : Nat) : n ≤ colorAdvance xs n := by
    induction xs generalizing n with
    | nil => exact Nat.le_refl _
    | cons inst xs ih =>
      dsimp [colorAdvance]
      split
      · exact Nat.le_trans (by omega) (ih _)
      · exact ih _
  induction insts generalizing c with
  | nil => simp [colorAdvance]
  | cons inst rest ih =>
    cases hc : colored inst with
    | false => simp [colorAdvance, hc, ih]
    | true =>
      have bound := monotone rest (c + 1)
      simp only [colorAdvance, hc, ite_true]
      constructor
      · intro he; omega
      · intro all; have := all inst (List.mem_cons_self ..); simp [hc] at this

/-- Internal source window guard: unchanged colors rule out effects/traps;
address-definition exclusion rules out overwriting the deferred load pointer.
Both must eventually be derived from actual source metadata and SSA facts. -/
def LoadWindowGuard (ctx : Ctx) (ptr : Nat) (indices : List Nat) : Prop :=
  ∀ i ∈ indices, ∃ info inst, ctx.insts[i]? = some info ∧ info.clif = some inst ∧
    colored inst = false ∧ ptr ∉ info.results

/-- A complete actual source window preserves the entire deferred load outcome
using stock barrier classification and result-binding facts at every step. -/
theorem load_delay_guarded_window {env : Clif.Env} {p : Clif.Program} {ctx : Ctx}
    {indices : List Nat} {s t : Clif.Frame × Clif.Mem}
    {op : Clif.LoadOp} {ty : Clif.Ty} {flags : Clif.MemFlags} {ptr : Nat} {offset : Int}
    (run : SourceSteps (SourceInstResult env p ctx) indices s t)
    (guard : LoadWindowGuard ctx ptr indices) :
    Clif.evalInst t.1 t.2 (.load op ty flags ptr offset) =
      Clif.evalInst s.1 s.2 (.load op ty flags ptr offset) := by
  induction run with
  | nil s => rfl
  | cons head tail ih =>
    obtain ⟨info, inst, hi, hic, quiet, address⟩ := guard _ (List.mem_cons_self ..)
    have current := load_delay_quiet_step (op := op) (ty := ty) (flags := flags)
      (offset := offset) head hi hic (uncolored_quiet quiet) address
    have rest := ih (fun i hi => guard i (List.mem_cons_of_mem _ hi))
    exact rest.trans current.2.2

theorem uncolored_quiet_witness :
    colored (.iconst .i64 7) = false ∧ mustLower (.iconst .i64 7) = false :=
  ⟨rfl, uncolored_quiet rfl⟩

theorem colorAdvance_unchanged_witness :
    colorAdvance [.iconst .i64 7, .iconst .i8 9] 5 = 5 ∧
    (∀ inst ∈ [.iconst .i64 7, .iconst .i8 9], colored inst = false) ∧
    colorAdvance [.load .load .i8 { trapCode := none } 1 0] 5 = 6 ∧
    colorAdvance [.div .udiv .i64 1 2] 5 = 6 := by
  exact ⟨rfl, (colorAdvance_unchanged _ 5).mp rfl, rfl, rfl⟩

theorem load_delay_guarded_window_witness :
    SourceSteps (SourceInstResult Clif.Env.empty { funcs := [] } quietCtx) [0]
      (delayFrame, delayMem) (delayAfter, delayMem) ∧
    LoadWindowGuard quietCtx 1 [0] ∧
    Clif.evalInst delayAfter delayMem delayLoad =
      Clif.evalInst delayFrame delayMem delayLoad := by
  have run := load_delay_quiet_step_witness.1
  have guard : LoadWindowGuard quietCtx 1 [0] := by
    intro i hi
    simp only [List.mem_singleton] at hi
    subst i
    exact ⟨quietCtx.insts[0]!, .iconst .i64 7, rfl, rfl, rfl, by decide⟩
  have steps : SourceSteps (SourceInstResult Clif.Env.empty { funcs := [] } quietCtx) [0]
      (delayFrame, delayMem) (delayAfter, delayMem) := .cons run (.nil _)
  exact ⟨steps, guard, load_delay_guarded_window steps guard⟩

end Backend.Stock.Proof
