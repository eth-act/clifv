import FV.Backend.Isel
import FV.Backend.Proof.DriverCheck
import FV.Clif.Run
import FV.Backend.Proof.LowerRename
import FV.Backend.Proof.RegallocOperands

/-!
# The lowering calls the driver consumes (M4's contracts at the `runTerm` level)

The contracts themselves (`LowerInstOk`, `LowerTermOk`, `seqRun`, …) are M4's
(`FV/Backend/Proof/IselContract.lean`, shapes agreed with M7). Here:

* `InstCalls sem MR env p`: every `lower` call on a statement that `lowerFunction` makes (in a
  context satisfying `CtxInv`) satisfies `LowerInstOk`. **Proven** from M4's
  `LowerRulesCorrect program` + `ExcludedUnmatchable program` + `CallRulesCorrect program`
  under the callee contract `CallsRefine` (`instCalls_of_rules`).
* `TermCalls sem MR`: every terminator call (`lower` on `return`/`trap`, `lower_branch` on a
  branch) satisfies `LowerTermOk`. **Proven** from M4's terminator statements
  `LowerTermRulesCorrect`/`TermUnmatchable` (`lower` rules 964/1037) and
  `BranchRulesCorrect`/`BranchExcludedUnmatchable` (`termCalls_of_rules`).
* `DriverSem`: facts about the driver-emitted pseudo-instructions (M6's `csem`).
* `step_stmt`: `Clif.step` on a statement is `instOutcome`.
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof

/-- Every `lower` call `lowerFunction` makes on a statement of `f` (from a state whose fresh
vregs are above every value's vreg, `ValsBelow`; an indirect call's signature among `f`'s
indirect-call signatures with register arguments, `IndSigOk`) satisfies M4's `LowerInstOk`. -/
def InstCalls {W : Type} (f : Clif.Function) (sem : ISem CV W) (MR : MemRelTW W) (env : Clif.Env)
    (p : Clif.Program) :
    Prop :=
  ∀ ctx ii info inst st rss st' tr, CtxInv f ctx →
    (∃ B ∈ f.blocks, ∃ stm ∈ B.body, stm.inst = inst) → Compile.functionE f = true →
    ctx.insts[ii]? = some info →
    info.clif = some inst → IndSigOk f (indSigs f) inst → st.emitted = #[] → ValsBelow ctx st →
    runTerm ctx "lower" [.inst ii] st = .ok (some (.regsVec rss), st', tr) →
    LowerInstOk sem MR env p ctx inst info.results st rss st' st'.emitted.toList

/-- Every terminator call `lowerFunction` makes (in a context satisfying `CtxInv` whose slot
`ti` is `buildCtx`'s terminator placeholder, from a state above every value's vreg) satisfies
M4's `LowerTermOk`. From M4's terminator rule statements: `termCalls_of_rules`. -/
def TermCalls {W : Type} (sem : ISem CV W) (MR : MemRelTW W) : Prop :=
  ∀ f ctx ti t data targets out st st' tr, CtxInv f ctx → BrIdxTyped ctx t → TargetsLen t targets →
    ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩ → ValsBelow ctx st →
    termData t = .ok data → st.emitted = #[] →
    runTerm (termCtx ctx ti data) (termCall t ti targets).1 (termCall t ti targets).2 st =
      .ok (some out, st', tr) →
    LowerTermOk sem MR (termCtx ctx ti data) t targets st st' st'.emitted.toList

/-- `f`'s externs are the ones it declares. -/
theorem externsIn_self (f : Clif.Function) : ExternsIn f (f.externs.map (·.2)) := by
  intro fn e he
  unfold Clif.Function.extern? at he
  obtain ⟨l₁, l₂, he2, -⟩ := List.lookup_eq_some_iff.mp he
  rw [he2]
  simp

/-- **From M4's rule theorems to the driver's `lower` calls** (of function `f`, whose memory
relation satisfies `MemRelOk`, under the callee contract for `f`'s externs and the indirect-call
contract for `f`'s indirect-call signatures). -/
theorem instCalls_of_rules (hrules : LowerRulesCorrect Isle.Aarch64.program)
    (hex : ExcludedUnmatchable Isle.Aarch64.program)
    (hcalls : CallRulesCorrect Isle.Aarch64.program) (hind : IndRulesCorrect Isle.Aarch64.program)
    (hmem : MemRulesCorrect Isle.Aarch64.program)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat} {sem : Sem}
    {MR : MemRelT} {env : Clif.Env} {p : Clif.Program} {f : Clif.Function} (hR : Refines F sem)
    (hMR : MRStable F MR) (hcr : CallsRefine F env (f.externs.map (·.2)) MR sem)
    (hicr : IndCallsRefine env (indSigs f) MR sem)
    (hMem : MemRefines F sb syms sem) {outB : Nat} (hout : OutArgsOk F outB MR)
    (hstk : CallsStack f outB)
    (hMRo : MemRelOk F sb syms f MR) : InstCalls f sem MR env p := by
  intro ctx ii info inst st rss st' tr hctx hmem' hE hi hc hsig hemp hvb hrun
  obtain ⟨B, hB, stm, hstm, rfl⟩ := hmem'
  obtain ⟨ms, rss', hem, hov, hok⟩ := lowerInstOk_runTerm hrules hex hcalls hind hmem
    (env := env) (cp := p) hR hMR hcr hicr hMem hctx hout (externsIn_self f) hE hMRo hi hc hsig
    (fun fn args e hc he => hstk B hB stm hstm fn args e hc he) hvb hrun
  cases hov
  rw [hemp, Array.empty_append] at hem
  rw [hem, List.toList_toArray]
  exact hok

/-- The driver's facts about the semantics that do not read the world (generic in the world
type `W`): an edge block's `jump` goes to its only successor, renaming invariance, label
invariance. -/
structure DriverSemG {W : Type} (sem : ISem CV W) : Prop where
  jump : ∀ l w, sem (.jump l) [] w = some ([], w, .goto 0)
  rename : ∀ g gn, VRenaming g gn → ∀ i, sem (i.mapRegs g) = sem i
  /-- a branch's semantics does not depend on its label values (`prepare` retargets split
  critical edges) -/
  retarget : ∀ i ls i', MInst.setTargets i ls = some i' → sem i' = sem i

/-- Facts about the driver-emitted pseudo-instructions and alias resolution that the VCode
semantics must satisfy (M6's `csem`: `Args` reads the argument registers of the world, and
`DriverSemG`). -/
structure DriverSem (sem : Sem) extends DriverSemG sem : Prop where
  args : ∀ ds w, sem (.args ds) [] w = some (ds.map (fun d => regVal w d.2), w, .next)

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

/-- A call of an extern that is not a function of `p` steps as `instOutcome`, the results bound
by `continueWith`. -/
theorem stepCall_eq (env : Clif.Env) (p : Clif.Program) (s : Clif.State) (rest : List Clif.Stmt)
    (results : List Clif.ValueId) (fn : Clif.FnRef) (args : List Clif.ValueId)
    (hext : ∀ e, s.frame.func.extern? fn = some e → p.func? e.name = none) :
    Clif.stepCall env p s rest results fn args =
      Clif.StepResult.ofRes (instOutcome env p s.frame s.mem (.call fn args))
        fun (vals, mem) => Clif.continueWith s rest results vals mem := by
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
  simp only [hext ext he]
  cases env.extern ext.name with
  | none => rfl
  | some g =>
    simp only
    cases g vals s.mem with
    | returned rv m =>
      simp only
      split <;> rfl
    | _ => rfl

theorem resBind_ok {α β : Type} {x : Clif.Res α} {f : α → Clif.Res β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | ok a => exact ⟨a, rfl, h⟩
  | trap c => cases h
  | stuck m => cases h

/-- A CLIF value read `as? .i64` is an `i64` value. -/
theorem val_as_i64 {v : Clif.Val} {x : BitVec Clif.Ty.i64.width} (h : v.as? .i64 = some x) :
    v = ⟨.i64, x⟩ := by
  obtain ⟨ty, bits⟩ := v
  simp only [Clif.Val.as?] at h
  split at h
  · rename_i hty
    subst hty
    cases h
    rfl
  · cases h

/-- An indirect call whose callee address is no function of `p` steps as `instOutcome` (the
extern at that address, `Clif.callExternAt`), the results bound by `continueWith`. -/
theorem stepCallIndirect_eq (env : Clif.Env) (p : Clif.Program) (s : Clif.State)
    (rest : List Clif.Stmt) (results : List Clif.ValueId) (sig callee : Nat)
    (args : List Clif.ValueId)
    (hnp : ∀ cv, s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat) :
    Clif.stepCallIndirect env p s rest results sig callee args =
      Clif.StepResult.ofRes (instOutcome env p s.frame s.mem (.callIndirect sig callee args))
        fun (vals, mem) => Clif.continueWith s rest results vals mem := by
  simp only [Clif.stepCallIndirect, instOutcome]
  rw [ofRes_bind]
  apply ofRes_congr
  intro ⟨declared, addr, vals⟩ hX
  obtain ⟨d, -, hX⟩ := resBind_ok hX
  obtain ⟨cv, hcv, hX⟩ := resBind_ok hX
  have haddr : addr = cv.toNat := by
    cases hc : cv.as? .i64 with
    | none => simp [hc] at hX
    | some y =>
      have := val_as_i64 hc
      subst this
      simp only [Clif.Val.as?_mk, Clif.Res.ofOption_some, Clif.Res.ok_bind] at hX
      obtain ⟨vs, -, hX⟩ := resBind_ok hX
      cases hX
      rfl
  have hfind : p.funcs.find? (fun g => s.mem.symbols g.name == some addr) = none := by
    rw [List.find?_eq_none]
    intro g hg heq
    exact hnp cv hcv g hg (by rw [← haddr]; simpa using heq)
  simp only [hfind]

theorem step_stmt (env : Clif.Env) (p : Clif.Program) (s : Clif.State) (st : Clif.Stmt)
    (rest : List Clif.Stmt) (h : s.frame.body = st :: rest)
    (hext : ∀ fn args, st.inst = .call fn args → ∀ e, s.frame.func.extern? fn = some e →
      p.func? e.name = none)
    (hind : ∀ sig callee args, st.inst = .callIndirect sig callee args → ∀ cv,
      s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat) :
    Clif.step env p s = Clif.StepResult.ofRes (instOutcome env p s.frame s.mem st.inst)
      fun (vals, mem) => Clif.continueWith s rest st.results vals mem := by
  cases hi : st.inst with
  | call fn args =>
    rw [Clif.step_call env p s rest st.results fn args (by rw [h, ← hi])]
    exact stepCall_eq env p s rest st.results fn args (hext fn args hi)
  | callIndirect sig callee args =>
    have hs : Clif.step env p s = Clif.stepCallIndirect env p s rest st.results sig callee args := by
      simp [Clif.step, h, hi]
    rw [hs]
    exact stepCallIndirect_eq env p s rest st.results sig callee args (hind sig callee args hi)
  | _ =>
    rw [Clif.step_inst env p s st rest h (by intro fn args e; rw [hi] at e; cases e)
      (by intro sig callee args e; rw [hi] at e; cases e)]
    simp only [hi, instOutcome]

/-! ## Terminator calls from M4's terminator rule statements -/

theorem termCtx_insts_self {ctx : Ctx} {ti : Nat} {x : IInfo} (h : ctx.insts[ti]? = some x)
    (data : V) : (termCtx ctx ti data).insts[ti]? = some ⟨data, [], [], none⟩ := by
  have hlt : ti < ctx.insts.size := (Array.getElem?_eq_some_iff.mp h).1
  show (ctx.insts.set! ti _)[ti]? = _
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt hlt]

theorem termCtx_insts_ne {ctx : Ctx} {ti j : Nat} (h : j ≠ ti) (data : V) :
    (termCtx ctx ti data).insts[j]? = ctx.insts[j]? := by
  show (ctx.insts.set! ti _)[j]? = _
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (Ne.symm h)]

/-- Filling in the terminator's data at `buildCtx`'s placeholder keeps `CtxInv` (no value is
defined by the placeholder). -/
theorem ctxInv_termCtx {f : Clif.Function} {ctx : Ctx} (h : CtxInv f ctx) {ti : Nat}
    (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩) (data : V) :
    CtxInv f (termCtx ctx ti data) := by
  have hne : ∀ x d, ctx.defInst? x = some d → d ≠ ti := by
    intro x d hd e
    subst e
    obtain ⟨info, hi, hx⟩ := h.defInst x d hd
    rw [hph] at hi; cases hi; cases hx
  refine ⟨h.func, fun ii info inst hi hc => ?_, fun ii info inst hi hc => ?_,
    fun ii info inst hi hc => ?_, h.valueReg,
    h.typedReg, fun x d hd => ?_, fun x d info hd hi => ?_, h.slotOff, fun ii info hi => ?_,
    h.valTyE, fun ii info inst x hi hc hx => ?_⟩
  · by_cases e : ii = ti
    · subst e; rw [termCtx_insts_self hph] at hi; cases hi; cases hc
    · rw [termCtx_insts_ne e] at hi; exact h.data ii info inst hi hc
  · by_cases e : ii = ti
    · subst e; rw [termCtx_insts_self hph] at hi; cases hi; cases hc
    · rw [termCtx_insts_ne e] at hi; exact h.instE ii info inst hi hc
  · by_cases e : ii = ti
    · subst e; rw [termCtx_insts_self hph] at hi; cases hi; cases hc
    · rw [termCtx_insts_ne e] at hi; exact h.resTys ii info inst hi hc
  · rw [termCtx_insts_ne (hne x d hd)]; exact h.defInst x d hd
  · rw [termCtx_insts_ne (hne x d hd)] at hi; exact h.defClif x d info hd hi
  · by_cases e : ii = ti
    · subst e; rw [termCtx_insts_self hph] at hi; cases hi; intro t ht; cases ht
    · rw [termCtx_insts_ne e] at hi; exact h.resTysE ii info hi
  · by_cases e : ii = ti
    · subst e; rw [termCtx_insts_self hph] at hi; cases hi; cases hc
    · rw [termCtx_insts_ne e] at hi; exact h.addr64 ii info inst x hi hc hx

/-- For `return`/`trap`, `LowerTermOk` does not depend on the targets. -/
theorem lowerTermOk_targets {isem : Sem} {MR : MemRelT} {ctx : Ctx} {t : Clif.Terminator}
    (hrt : retOrTrap t = true) {st st' : LState} {ms : List MInst}
    (h : LowerTermOk isem MR ctx t [] st st' ms) (targets : List Label) :
    LowerTermOk isem MR ctx t targets st st' ms := by
  cases t <;> simp [retOrTrap] at hrt <;> exact ⟨h.mono, h.defs, h.run⟩

/-- **From M4's terminator rule statements to the driver's terminator calls.** -/
theorem termCalls_of_rules (hlt : LowerTermRulesCorrect Isle.Aarch64.program)
    (hun : TermUnmatchable Isle.Aarch64.program)
    (hbr : BranchRulesCorrect Isle.Aarch64.program)
    (hbex : BranchExcludedUnmatchable Isle.Aarch64.program) {F : BitVec 64 → Prop} {sem : Sem}
    {MR : MemRelT} (hR : Refines F sem) (hMR : MRStable F MR) : TermCalls sem MR := by
  intro f ctx ti t data targets out st st' tr hctx hbt htl hph hvb hd hemp hrun
  have hctx' := ctxInv_termCtx hctx hph data
  have hi := termCtx_insts_self hph data
  have hvb' : ValsBelow (termCtx ctx ti data) st := hvb
  have key : ∀ ms : List MInst, st'.emitted = st.emitted ++ ms.toArray → ms = st'.emitted.toList := by
    intro ms hem; rw [hemp, Array.empty_append] at hem; rw [hem, List.toList_toArray]
  cases hrt : retOrTrap t
  · have hc : termCall t ti targets = ("lower_branch", [.inst ti, .labels targets]) := by
      cases t <;> simp [retOrTrap] at hrt <;> rfl
    rw [hc] at hrun
    obtain ⟨ms, hem, hok⟩ := branchOk_runTerm hbr hbex hR hMR hctx' hrt hd hi hbt htl hvb' hrun
    rw [← key ms hem]; exact hok
  · have hc : termCall t ti targets = ("lower", [.inst ti]) := by
      cases t <;> simp [retOrTrap] at hrt <;> rfl
    rw [hc] at hrun
    obtain ⟨ms, hem, hok⟩ := lowerTermOk_runTerm hlt hun hR hMR hctx' hrt hd hi hvb' hrun
    rw [← key ms hem]; exact lowerTermOk_targets hrt hok targets

/-! ## `try_call` calls from M4's `try_call` rule statements -/

/-- Every `lower_branch` call `lowerFunction` makes on a `try_call` of `f` (in its `try_call`
context `tryCtx`, whose return/payload vregs `tryRegsOf` allocated from a state `lo` above every
value's vreg) whose callee's stack arguments fit the outgoing area `outB` satisfies
`LowerTryOk`. From M4's rule statements: `tryCalls_of_rules`. -/
def TryCalls {W : Type} (f : Clif.Function) (sem : ISem CV W) (MR : MemRelTW W) (env : Clif.Env)
    (p : Clif.Program)
    (outB : Nat) : Prop :=
  ∀ ctx ti fn args et data sig items targets info trs lo st1 out st' tr, CtxInv f ctx →
    (∀ e, f.extern? fn = some e → SigStackOk e.sig outB) →
    tryCallData f (.tryCall fn args et) = .ok data →
    exnTableOpnd f et = .ok (sig, items) → ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩ →
    tryInfoOf sig items targets = some info → tryRegsOf sig lo = some (trs, st1) →
    ValsBelow ctx lo →
    runTerm (tryCtx ctx ti data trs) "lower_branch" [.inst ti, .labels targets]
      { st1 with emitted := #[] } = .ok (some out, st', tr) →
    LowerTryOk sem MR env p (tryCtx ctx ti data trs) (.call fn args) info
      { st1 with emitted := #[] } st' st'.emitted.toList

/-- `CtxInv` does not depend on the `try_call` vregs. -/
theorem ctxInv_tryRegs {f : Clif.Function} {ctx : Ctx} (h : CtxInv f ctx)
    (trs : List Reg × List Reg) : CtxInv f { ctx with tryRegs := trs } :=
  ⟨h.func, h.data, h.instE, h.resTys, h.valueReg, h.typedReg, h.defInst, h.defClif, h.slotOff,
    h.resTysE, h.valTyE, h.addr64⟩

/-- **From M4's `try_call` rule statements to the driver's `try_call` calls** (of `f`, under the
callee contract for `f`'s externs, the memory forms and the outgoing area `outB`). -/
theorem tryCalls_of_rules (htr : TryRulesCorrect Isle.Aarch64.program)
    (hun : TryUnmatchable Isle.Aarch64.program) {F : BitVec 64 → Prop} {sem : Sem}
    {MR : MemRelT} {env : Clif.Env} {p : Clif.Program} {f : Clif.Function} (hR : Refines F sem)
    (hMR : MRStable F MR) {sb : Nat} {syms : String → Option Nat} (hMem : MemRefines F sb syms sem)
    {outB : Nat} (hout : OutArgsOk F outB MR) (hcr : CallsRefine F env (f.externs.map (·.2)) MR sem) :
    TryCalls f sem MR env p outB := by
  intro ctx ti fn args et data sig items targets info trs lo st1 out st' tr hctx hra hd he hph
    hinfo hregs hvb hrun
  have hctx' := ctxInv_tryRegs (ctxInv_termCtx hctx hph data) trs
  have hi : (tryCtx ctx ti data trs).insts[ti]? = some ⟨data, [], [], none⟩ :=
    termCtx_insts_self hph data
  have hregs' : tryRegsOf sig lo = some ((tryCtx ctx ti data trs).tryRegs, st1) := hregs
  have hvb' : ValsBelow (tryCtx ctx ti data trs) lo := hvb
  obtain ⟨ms, hem, hok⟩ := tryOk_runTerm htr hun hR hMR hMem hout hcr hctx' (externsIn_self f) hra
    hd he hi
    hinfo hregs' hvb' (st := { st1 with emitted := #[] }) (Nat.le_refl _) hrun
  have : ms = st'.emitted.toList := by
    simp only [Array.empty_append] at hem; rw [hem, List.toList_toArray]
  rw [← this]; exact hok

/-- Every `lower_branch` call `lowerFunction` makes on a `try_call_indirect` of `f` whose
call-site signature is in `sigs` with at most 8 parameters (in its `try_call` context, as
`TryCalls`) satisfies `LowerTryOk` for the indirect call. From M4's rule statements:
`tryIndCalls_of_rules`. -/
def TryIndCalls {W : Type} (sem : ISem CV W) (MR : MemRelTW W) (env : Clif.Env) (p : Clif.Program)
    (sigs : List Clif.Signature) : Prop :=
  ∀ f ctx ti callee args et data sig items targets info trs lo st1 out st' tr, CtxInv f ctx →
    tryCallData f (.tryCallIndirect callee args et) = .ok data →
    exnTableOpnd f et = .ok (sig, items) → sig ∈ sigs → sig.params.length ≤ 8 →
    ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩ →
    tryInfoOf sig items targets = some info → tryRegsOf sig lo = some (trs, st1) →
    ValsBelow ctx lo →
    runTerm (tryCtx ctx ti data trs) "lower_branch" [.inst ti, .labels targets]
      { st1 with emitted := #[] } = .ok (some out, st', tr) →
    LowerTryOk sem MR env p (tryCtx ctx ti data trs) (.callIndirect et.sig callee args) info
      { st1 with emitted := #[] } st' st'.emitted.toList

/-- **From M4's `try_call_indirect` rule statements to the driver's `try_call_indirect` calls**
(under the indirect-call contract for the signatures `sigs`). -/
theorem tryIndCalls_of_rules (htr : TryIndRulesCorrect Isle.Aarch64.program)
    (hun : TryIndUnmatchable Isle.Aarch64.program) {F : BitVec 64 → Prop} {sem : Sem}
    {MR : MemRelT} {env : Clif.Env} {p : Clif.Program} {sigs : List Clif.Signature}
    (hR : Refines F sem) (hMR : MRStable F MR) (hcr : IndCallsRefine env sigs MR sem) :
    TryIndCalls sem MR env p sigs := by
  intro f ctx ti callee args et data sig items targets info trs lo st1 out st' tr hctx hd he hsig
    h8 hph hinfo hregs hvb hrun
  have hctx' := ctxInv_tryRegs (ctxInv_termCtx hctx hph data) trs
  have hi : (tryCtx ctx ti data trs).insts[ti]? = some ⟨data, [], [], none⟩ :=
    termCtx_insts_self hph data
  have hregs' : tryRegsOf sig lo = some ((tryCtx ctx ti data trs).tryRegs, st1) := hregs
  have hvb' : ValsBelow (tryCtx ctx ti data trs) lo := hvb
  obtain ⟨ms, hem, hok⟩ := tryIndOk_runTerm htr hun hR hMR hcr hctx' hd he hsig h8 hi
    hinfo hregs' hvb' (st := { st1 with emitted := #[] }) (Nat.le_refl _) hrun
  have : ms = st'.emitted.toList := by
    simp only [Array.empty_append] at hem; rw [hem, List.toList_toArray]
  rw [← this]; exact hok

end Backend.Proof.Driver
