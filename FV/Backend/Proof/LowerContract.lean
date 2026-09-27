import FV.Backend.Isel
import FV.Clif.Run
import FV.Backend.Proof.LowerRename
import FV.Backend.Proof.RegallocOperands

/-!
# The per-lowering contracts the M7 driver consumes (M4 hypothesis, placeholder)

What one call of the ISLE root term does, at the VCode level, over an abstract per-`MInst`
semantics `sem : Sem` (M6's `csem` is the instance) and an abstract relation `MR` between the
CLIF memory (with the frame's slot bases) and the VCode world:

* `LowerInstOk`: `lower` on a CLIF instruction: the emitted code, run straight-line from any
  vreg file holding the CLIF frame's values (low bits, `VHolds`) and any related world, computes
  the instruction's results into the result registers (`ResultsHeld`), keeps `MR`, writes only
  fresh vregs, reads only fresh vregs or defined values; an explicit trap (`div`) stops at an
  instruction that halts with the CLIF trap code.
* `LowerTermOk`: `lower` on `return`/`trap`, `lower_branch` on `jump`/`brif`/`br_table`.
* `LowerRulesCorrect`: every `lower`/`lower_branch` call the driver makes satisfies them.

This is the content agreed with agent M4Foundation (`FV/Backend/Proof/IselContract.lean`,
`LowerRulesCorrect p` + `lowerInstOk_of_rules`, which gives it at the `runTerm` level); it is a
*definition*, swapped for M4's when that lands (docs/contracts/e2e.md).
-/

namespace Backend.Proof.Driver

open Backend

/-- The VCode-level instruction semantics. -/
abbrev Sem := ISem CV Arm.ArmState

/-- Width convention: a CLIF value of type `ty` is the low `ty.width` bits of a register value;
the upper bits are unspecified (PLAN.md §3.4). -/
def VHolds (v : Clif.Val) (x : CV) : Prop := x.setWidth v.ty.width = v.bits

/-- `vals` are held by `xs`, index by index. -/
def AllHold (vals : List Clif.Val) (xs : List CV) : Prop :=
  vals.length = xs.length ∧ ∀ (j : Nat) v x, vals[j]? = some v → xs[j]? = some x → VHolds v x

/-- Relation between the CLIF memory (and the activation's slot bases) and the VCode world. -/
abbrev MemRelT := List (Clif.SlotId × Nat) → Clif.Mem → Arm.ArmState → Prop

/-- Every defined CLIF value `x` is held by vreg `x` (`buildCtx`: value `x` has vreg `x`). -/
def ValsHeld (fr : Clif.Frame) (ρ : Nat → CV) : Prop :=
  ∀ x v, fr.regs x = some v → VHolds v (ρ x)

/-- Instructions the rules may look through (`def_inst`): their value is a function of their
operands (and the frame's slot bases). -/
def pureInst : Clif.Inst → Bool
  | .iconst .. | .unary .. | .binary .. | .icmp .. | .extend .. | .ireduce .. | .select ..
  | .stackAddr .. => true
  | _ => false

/-- DFG consistency: a defined value whose definition is a pure instruction equals that
instruction re-evaluated in the current frame (what `def_inst` look-through relies on). -/
def DFGCons (ctx : Ctx) (fr : Clif.Frame) : Prop :=
  ∀ x j info cl v, ctx.defInst? x = some j → ctx.insts[j]? = some info → info.clif = some cl →
    pureInst cl = true → fr.regs x = some v →
    ∃ vals, (∀ cm, Clif.evalInst fr cm cl = .ok (vals, cm)) ∧ (info.results.zip vals).lookup x = some v

/-- The CLIF outcome of a statement's instruction: `evalInst`, and for a `call` the extern's
semantics (as `Clif.stepCall`; a call of a function of `p` is outside the theorem). -/
def instOutcome (env : Clif.Env) (p : Clif.Program) (fr : Clif.Frame) (cm : Clif.Mem) :
    Clif.Inst → Clif.Res (List Clif.Val × Clif.Mem)
  | .call fn args =>
    Clif.Res.bind (do
      let ext ← Clif.Res.ofOption s!"unknown function reference fn{fn}" (fr.func.extern? fn)
      let vals ← fr.getMany args
      Clif.checkTys s!"arguments of call to %{ext.name}" vals (Clif.AbiParam.tys ext.sig.params)
      pure (ext, vals)) fun (ext, vals) =>
    match p.func? ext.name with
    | some _ => .stuck "call of a function of the program"
    | none =>
      match env.extern ext.name with
      | some g =>
        match g vals cm with
        | .returned rvals mem' =>
          if rvals.map (·.ty) == Clif.AbiParam.tys ext.sig.returns then .ok (rvals, mem')
          else .stuck s!"extern %{ext.name} returned values of the wrong types"
        | .trapped c => .trap c
        | .stuck m => .stuck m
        | .outOfFuel => .stuck s!"extern %{ext.name} ran out of fuel"
      | none => .stuck s!"unknown callee %{ext.name}"
  | i => Clif.evalInst fr cm i

/-- Instructions whose trap the lowering makes explicit (check + trap instruction). -/
def explicitTrapInst : Clif.Inst → Bool
  | .div .. => true
  | _ => false

/-- Trap code of a trapping VCode instruction. -/
def trapCode? : MInst → Option Clif.TrapCode
  | .udf c | .trapIf _ c => some c
  | _ => none

/-- The result registers hold the results: one virtual register per result, a fresh vreg
(`≥ lo`) or a defined value's vreg. -/
def ResultsHeld (lo : Nat) (fr : Clif.Frame) (rss : List (List Reg)) (vals : List Clif.Val)
    (ρ : Nat → CV) : Prop :=
  rss.length = vals.length ∧
    ∀ (j : Nat) rs v, rss[j]? = some rs → vals[j]? = some v →
      ∃ out cls, rs = [.vreg out cls] ∧ (lo ≤ out ∨ (fr.regs out).isSome) ∧ VHolds v (ρ out)

/-- The emitted code reads only fresh vregs or defined values. -/
def Uses (st : LState) (fr : Clif.Frame) (ms : List MInst) : Prop :=
  ∀ m ∈ ms, ∀ u ∈ vuseNums m, st.nextVreg ≤ u ∨ (fr.regs u).isSome

/-- **`lower` on a non-terminator** (results `results`; lowering state `st` → `st'`, emitted
code `ms`). -/
structure LowerInstOk (sem : Sem) (MR : MemRelT) (env : Clif.Env) (p : Clif.Program) (ctx : Ctx)
    (inst : Clif.Inst) (results : List Nat) (st : LState) (rss : List (List Reg)) (st' : LState)
    (ms : List MInst) : Prop where
  mono : st.nextVreg ≤ st'.nextVreg
  defs : ∀ m ∈ ms, ∀ d ∈ vdefs m, st.nextVreg ≤ d ∧ d < st'.nextVreg
  run : ∀ (fr : Clif.Frame) (cm : Clif.Mem) (ρ : Nat → CV) (w : Arm.ArmState),
    fr.func = ctx.func → ValsHeld fr ρ → DFGCons ctx fr → MR fr.slots cm w →
    match instOutcome env p fr cm inst with
    | .ok (vals, cm') => Uses st fr ms ∧ ∃ ρ' w', seqRun sem ms ρ w = some (.fall ρ' w') ∧
        (results = [] ∨ ResultsHeld st.nextVreg fr rss vals ρ') ∧ MR fr.slots cm' w'
    | .trap c => explicitTrapInst inst = true → Uses st fr ms ∧
        ∃ k i ops ρ₁ w₁ outs w₂, seqRun sem ms ρ w = some (.stop k i ops ρ₁ w₁ outs w₂ .halt) ∧
          trapCode? i = some c
    | .stuck _ => True

/-- The successor a branch takes, as an index into the driver's target list (`jump`: its
target; `brif`: then, else; `br_table`: default, then the table). -/
def branchIdx (fr : Clif.Frame) : Clif.Terminator → Clif.Res Nat
  | .jump _ => .ok 0
  | .brif c _ _ => Clif.Res.bind (fr.get c) fun v => .ok (if Clif.Sem.truthy v.bits then 0 else 1)
  | .brTable x _ tbl => Clif.Res.bind (fr.get x) fun v =>
      .ok (if v.toNat < tbl.length then v.toNat + 1 else 0)
  | _ => .stuck "not a branch"

/-- **`lower` on `return`/`trap`, `lower_branch` on a branch** (terminator `t`, successor labels
`targets`). -/
structure LowerTermOk (sem : Sem) (MR : MemRelT) (ctx : Ctx) (t : Clif.Terminator)
    (targets : List Label) (st st' : LState) (ms : List MInst) : Prop where
  mono : st.nextVreg ≤ st'.nextVreg
  defs : ∀ m ∈ ms, ∀ d ∈ vdefs m, st.nextVreg ≤ d ∧ d < st'.nextVreg
  run : ∀ (fr : Clif.Frame) (cm : Clif.Mem) (ρ : Nat → CV) (w : Arm.ArmState),
    fr.func = ctx.func → ValsHeld fr ρ → DFGCons ctx fr → MR fr.slots cm w →
    match t with
    | .ret xs => ∀ vals, fr.getMany xs = .ok vals → Uses st fr ms ∧
        ∃ k us ops ρ₁ w₁ outs w₂,
          seqRun sem ms ρ w = some (.stop k (.rets us) ops ρ₁ w₁ outs w₂ .ret) ∧
          us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = vals.length ∧
          AllHold vals (vuses ops ρ₁) ∧ MR fr.slots cm w₂
    | .trap c => Uses st fr ms ∧ ∃ k i ops ρ₁ w₁ outs w₂,
        seqRun sem ms ρ w = some (.stop k i ops ρ₁ w₁ outs w₂ .halt) ∧ trapCode? i = some c
    | t => (∀ i, ms.getLast? = some i → i.targets = targets) ∧
        ∀ j, branchIdx fr t = .ok j → Uses st fr ms ∧
        ∃ k i ops ρ₁ w₁ outs w₂,
          seqRun sem ms ρ w = some (.stop k i ops ρ₁ w₁ outs w₂ (.goto j)) ∧ k + 1 = ms.length ∧
          MR fr.slots cm w₂

/-- The context `lowerFunction` lowers a terminator in (its data filled in). -/
def termCtx (ctx : Ctx) (ti : Nat) (data : V) : Ctx :=
  { ctx with insts := ctx.insts.set! ti ⟨data, [], [], none⟩ }

/-- The ISLE root term and arguments `lowerFunction` uses for a terminator. -/
def termCall (t : Clif.Terminator) (ti : Nat) (targets : List Label) : String × List V :=
  match t with
  | .ret _ | .trap _ => ("lower", [.inst ti])
  | _ => ("lower_branch", [.inst ti, .labels targets])

/-- **M4 hypothesis (placeholder).** Every `lower` / `lower_branch` call `lowerFunction` makes
satisfies its contract. -/
def LowerRulesCorrect (sem : Sem) (MR : MemRelT) (env : Clif.Env) (p : Clif.Program) : Prop :=
  (∀ f ctx ranges st0 ii info inst st rss st' tr,
    buildCtx f = .ok (ctx, ranges, st0) → ctx.insts[ii]? = some info → info.clif = some inst →
    st.emitted = #[] → runTerm ctx "lower" [.inst ii] st = .ok (some (.regsVec rss), st', tr) →
    LowerInstOk sem MR env p ctx inst info.results st rss st' st'.emitted.toList) ∧
  (∀ f ctx ranges st0 ti t data targets out st st' tr,
    buildCtx f = .ok (ctx, ranges, st0) → termData t = .ok data → st.emitted = #[] →
    runTerm (termCtx ctx ti data) (termCall t ti targets).1 (termCall t ti targets).2 st =
      .ok (some out, st', tr) →
    LowerTermOk sem MR (termCtx ctx ti data) t targets st st' st'.emitted.toList)

/-- Facts about the driver-emitted pseudo-instructions and alias resolution that the VCode
semantics must satisfy (M6's `csem`: `Args` reads the argument registers of the world, an edge
block's `jump` goes to its only successor, renaming invariance). -/
structure DriverSem (sem : Sem) : Prop where
  args : ∀ ds w, sem (.args ds) [] w = some (ds.map (fun d => regVal w d.2), w, .next)
  jump : ∀ l w, sem (.jump l) [] w = some ([], w, .goto 0)
  rename : ∀ g gn, VRenaming g gn → ∀ i, sem (i.mapRegs g) = sem i

/-! ## `Clif.step` on a statement is `instOutcome` -/

theorem ofRes_bind {α β : Type} (X : Clif.Res α) (g : α → Clif.Res β)
    (k : β → Clif.StepResult) :
    Clif.StepResult.ofRes (Clif.Res.bind X g) k =
      Clif.StepResult.ofRes X (fun a => Clif.StepResult.ofRes (g a) k) := by
  cases X <;> rfl

theorem ofRes_congr {α : Type} (X : Clif.Res α) {k₁ k₂ : α → Clif.StepResult}
    (h : ∀ a, X = .ok a → k₁ a = k₂ a) : Clif.StepResult.ofRes X k₁ = Clif.StepResult.ofRes X k₂ := by
  cases X with
  | ok a => exact h a rfl
  | _ => rfl

theorem step_stmt (env : Clif.Env) (p : Clif.Program) (s : Clif.State) (st : Clif.Stmt)
    (rest : List Clif.Stmt) (h : s.frame.body = st :: rest)
    (hext : ∀ fn args, st.inst = .call fn args → ∀ e, s.frame.func.extern? fn = some e →
      p.func? e.name = none) :
    Clif.step env p s = Clif.StepResult.ofRes (instOutcome env p s.frame s.mem st.inst)
      fun (vals, mem) => Clif.continueWith s rest st.results vals mem := by
  cases hi : st.inst with
  | call fn args =>
    rw [Clif.step_call env p s rest st.results fn args (by rw [h, ← hi])]
    simp only [Clif.stepCall, instOutcome]
    rw [ofRes_bind]
    apply ofRes_congr
    intro ⟨ext, vals⟩ hX
    have he : s.frame.func.extern? fn = some ext := by
      cases hx : s.frame.func.extern? fn with
      | none => rw [hx] at hX; cases hX
      | some e =>
        rw [hx] at hX
        simp only [Clif.Res.ofOption_some, bind, Clif.Res.bind] at hX
        cases hv : s.frame.getMany args <;> rw [hv] at hX <;> try simp only at hX
        · rename_i vs
          cases hc : Clif.checkTys s!"arguments of call to %{e.name}" vs
              (Clif.AbiParam.tys e.sig.params) <;> rw [hc] at hX <;> try simp only at hX
          all_goals cases hX
          rfl
        all_goals cases hX
    simp only [hext fn args hi ext he]
    cases env.extern ext.name with
    | none => rfl
    | some g =>
      simp only
      cases g vals s.mem with
      | returned rv m =>
        simp only
        split <;> rfl
      | _ => rfl
  | _ =>
    rw [Clif.step_inst env p s st rest h (by intro fn args e; rw [hi] at e; cases e)]
    simp only [hi, instOutcome]

end Backend.Proof.Driver
