import FV.Backend.Isel
import FV.Clif.Run
import FV.Backend.Proof.LowerRename
import FV.Backend.Proof.RegallocOperands

/-!
# The lowering calls the driver consumes (M4's contracts at the `runTerm` level)

The contracts themselves (`LowerInstOk`, `LowerTermOk`, `seqRun`, …) are M4's
(`FV/Backend/Proof/IselContract.lean`, shapes agreed with M7). Here:

* `InstCalls sem MR env p`: every `lower` call on a statement that `lowerFunction` makes (in a
  context satisfying `CtxInv`) satisfies `LowerInstOk`. **Proven** from M4's
  `LowerRulesCorrect program` + `ExcludedUnmatchable program` (`instCalls_of_rules`).
* `TermCalls sem MR`: every terminator call (`lower` on `return`/`trap`, `lower_branch` on a
  branch) satisfies `LowerTermOk`. M4 states `BranchRulesCorrect` per `lower_branch` rule; the
  `runTerm`-level lemma for branches and a statement for the `return`/`trap` rules of `lower`
  are still owed by M4, so `TermCalls` is an explicit hypothesis (e2e.md, "Remaining").
* `DriverSem`: facts about the driver-emitted pseudo-instructions (M6's `csem`).
* `step_stmt`: `Clif.step` on a statement is `instOutcome`.
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof

/-- The context `lowerFunction` lowers a terminator in (its data filled in). -/
def termCtx (ctx : Ctx) (ti : Nat) (data : V) : Ctx :=
  { ctx with insts := ctx.insts.set! ti ⟨data, [], [], none⟩ }

/-- The ISLE root term and arguments `lowerFunction` uses for a terminator. -/
def termCall (t : Clif.Terminator) (ti : Nat) (targets : List Label) : String × List V :=
  match t with
  | .ret _ | .trap _ => ("lower", [.inst ti])
  | _ => ("lower_branch", [.inst ti, .labels targets])

/-- Every `lower` call `lowerFunction` makes on a statement satisfies M4's `LowerInstOk`. -/
def InstCalls (sem : Sem) (MR : MemRelT) (env : Clif.Env) (p : Clif.Program) : Prop :=
  ∀ f ctx ii info inst st rss st' tr, CtxInv f ctx → ctx.insts[ii]? = some info →
    info.clif = some inst → st.emitted = #[] →
    runTerm ctx "lower" [.inst ii] st = .ok (some (.regsVec rss), st', tr) →
    LowerInstOk sem MR env p ctx inst info.results st rss st' st'.emitted.toList

/-- Every terminator call `lowerFunction` makes satisfies M4's `LowerTermOk` (**M4, open**). -/
def TermCalls (sem : Sem) (MR : MemRelT) : Prop :=
  ∀ f ctx ranges st0 ti t data targets out st st' tr,
    buildCtx f = .ok (ctx, ranges, st0) → termData t = .ok data → st.emitted = #[] →
    runTerm (termCtx ctx ti data) (termCall t ti targets).1 (termCall t ti targets).2 st =
      .ok (some out, st', tr) →
    LowerTermOk sem MR (termCtx ctx ti data) t targets st st' st'.emitted.toList

/-- **From M4's rule theorems to the driver's `lower` calls.** -/
theorem instCalls_of_rules (hrules : LowerRulesCorrect Isle.Aarch64.program)
    (hex : ExcludedUnmatchable Isle.Aarch64.program) {F : BitVec 64 → Prop} {sem : Sem}
    {MR : MemRelT} {env : Clif.Env} {p : Clif.Program} (hR : Refines F sem)
    (hMR : MRStable F MR) : InstCalls sem MR env p := by
  intro f ctx ii info inst st rss st' tr hctx hi hc hemp hrun
  obtain ⟨ms, rss', hem, hout, hok⟩ := lowerInstOk_runTerm hrules hex (env := env) (cp := p) hR hMR
    hctx hi hc hrun
  cases hout
  rw [hemp, Array.empty_append] at hem
  rw [hem, List.toList_toArray]
  exact hok

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
