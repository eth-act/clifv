import FV.E2E.LegalUnwind
import FV.E2E.DeadCleanupUnwindWitness
import FV.Opt.Legalize128Pass

/-!
# Non-vacuity of `check_refinesX` and `backend_correct_legal_unwind` (S10f, #233)

The witness function, an `i128` function whose `try_call` callee raises:

```
function %w(i128) system_v {
    sig0 = (i128) system_v
    fn0 = %throw(i128) system_v
block0(v0: i128):
    try_call fn0(v0), sig0, block1, [ tag0: block2(exn0) ]
block1:
    return
block2(v1: i64):
    return
}
```

Its legalisation (`Opt.Legalize128.function128Cert src = .ok (gL, certL)`, `legal_eq`) splits
`v0` and the call's argument into `i64` halves `v3`, `v4` and adds the pad zero `v5`; `check`
and `exnOk` accept it (`validators`). The environment is the trusted Rust environment with
unwinding `Clif.Rust.xenvWith raises 77` with `raises := (· == "throw")`: `%throw` raises Rust's
exception (object 77), the `tag0` handler catches it.

* `refines`: `Opt.Legal.X.check_refinesX` applies with every premise discharged (the contracts by
  `xenvWith_envOkX`, the source run's `NoMemTrapX`/`NoIndInternalX` because `src` has no
  statements), on a source run that really raises and is caught (`caught`); the target run
  returns too.
* `legal_unwind_applies`: `E2E.backend_correct_legal_unwind` applies to the shipped compiler's
  output on `gL` (closed receipt `checks_true`, `native_decide`, the convention of
  `FV/E2E/DeadCleanupUnwindWitness.lean`) with raising callees, leaving open what
  `DeadCleanupUnwindWitness.final_applies` leaves open: the machine's callee contracts
  (`hC`/`hCT`), the linker's symbol addresses (`hsym`) and the run's entry premises.
-/

namespace Clif.Rust.LegalXWitness

open Clif Opt.Legal Opt.Legal.X Opt.Legalize128

/-! ### Runs of a function without statements in a program without functions -/

theorem func?_nil (n : String) : ({ funcs := [] } : Program).func? n = none := by
  simp [Program.func?]

theorem stepCall_nofuncs_next {env : Env} {s s' : State} {rest : List Stmt} {rs : List ValueId}
    {fn : FnRef} {args : List ValueId} (h : stepCall env { funcs := [] } s rest rs fn args = .next s') :
    s'.callers = s.callers ∧ s'.frame.func = s.frame.func ∧ s'.frame.body = rest := by
  unfold stepCall StepResult.ofRes at h
  dsimp only at h
  split at h
  · rename_i q _
    simp only [func?_nil] at h
    split at h
    · split at h
      · split at h
        · exact continueWith_next h |>.imp id fun h' => ⟨h'.1, h'.2.2⟩
        · cases h
      · cases h
      · cases h
      · cases h
    · cases h
  · cases h
  · cases h

theorem stepCallIndirect_nofuncs_next {env : Env} {s s' : State} {rest : List Stmt}
    {rs : List ValueId} {sig : Nat} {callee : ValueId} {args : List ValueId}
    (h : stepCallIndirect env { funcs := [] } s rest rs sig callee args = .next s') :
    s'.callers = s.callers ∧ s'.frame.func = s.frame.func ∧ s'.frame.body = rest := by
  unfold stepCallIndirect StepResult.ofRes at h
  dsimp only at h
  split at h
  · rename_i q _
    simp only [List.find?_nil] at h
    split at h
    · rename_i r _
      exact continueWith_next h |>.imp id fun h' => ⟨h'.1, h'.2.2⟩
    · cases h
    · cases h
  · cases h
  · cases h

/-- A terminator step of a frame without callers in a program without functions that continues:
no callers, the same function, and an empty body or a block's body. -/
theorem step_nofuncs_next {env : Env} {fr : Frame} {m : Mem} {s' : State} (hb : fr.body = [])
    (h : step env { funcs := [] } ⟨fr, [], m⟩ = .next s') :
    s'.callers = [] ∧ s'.frame.func = fr.func ∧
      (s'.frame.body = [] ∨ ∃ B ∈ fr.func.blocks, s'.frame.body = B.body) := by
  have hent : ∀ (bc : BlockCall) (k : Frame → StepResult),
      (∀ fr1, k fr1 = .next ⟨fr1, [], m⟩) → StepResult.ofRes (enterBlock fr bc) k = .next s' →
      s'.callers = [] ∧ s'.frame.func = fr.func ∧
        (s'.frame.body = [] ∨ ∃ B ∈ fr.func.blocks, s'.frame.body = B.body) := by
    intro bc k hk h
    cases he : enterBlock fr bc with
    | ok fr1 =>
      rw [he, StepResult.ofRes_ok, hk] at h
      cases h
      obtain ⟨B, args, regs, hB, -, -, -, rfl⟩ := Opt.enterBlock_ok he
      exact ⟨rfl, rfl, .inr ⟨B, block?_mem hB, rfl⟩⟩
    | trap c => rw [he] at h; cases h
    | stuck msg => rw [he] at h; cases h
  rw [step_term env _ _ hb] at h
  simp only at h
  cases ht : fr.term with
  | jump dest =>
    rw [ht] at h
    exact hent dest _ (fun _ => rfl) h
  | brif c t e =>
    rw [ht] at h
    simp only [stepTerm] at h
    cases hc : fr.get c with
    | ok cv => rw [hc] at h; exact hent _ _ (fun _ => rfl) h
    | trap c => rw [hc] at h; cases h
    | stuck msg => rw [hc] at h; cases h
  | brTable x d tbl =>
    rw [ht] at h
    simp only [stepTerm] at h
    cases hc : fr.get x with
    | ok cv => rw [hc] at h; exact hent _ _ (fun _ => rfl) h
    | trap c => rw [hc] at h; cases h
    | stuck msg => rw [hc] at h; cases h
  | ret xs =>
    rw [ht] at h
    simp only [stepTerm] at h
    cases hc : fr.getMany xs with
    | ok vals =>
      rw [hc] at h
      simp only [StepResult.ofRes_ok, returnValues] at h
      cases hk : checkTys (toString "return values of %" ++ toString fr.func.name) vals
        (AbiParam.tys fr.func.sig.returns) with
      | ok u => rw [hk] at h; simp at h
      | trap c => rw [hk] at h; cases h
      | stuck msg => rw [hk] at h; cases h
    | trap c => rw [hc] at h; cases h
    | stuck msg => rw [hc] at h; cases h
  | returnCall fn args =>
    rw [ht] at h
    simp only [stepTerm] at h
    unfold stepReturnCall StepResult.ofRes at h
    dsimp only at h
    split at h
    · simp only [func?_nil] at h
      split at h
      · split at h
        · simp only [returnValues] at h
          unfold StepResult.ofRes at h
          split at h <;> simp at h
        · cases h
        · cases h
        · cases h
      · cases h
    · cases h
    · cases h
  | trap c => rw [ht] at h; cases h
  | tryCall fn args et =>
    rw [ht] at h
    simp only [stepTerm] at h
    unfold stepTryCall StepResult.ofRes at h
    dsimp only at h
    split at h
    · obtain ⟨h1, h2, h3⟩ := stepCall_nofuncs_next h
      exact ⟨h1, h2, .inl h3⟩
    · cases h
    · cases h
  | tryCallIndirect callee args et =>
    rw [ht] at h
    simp only [stepTerm] at h
    unfold stepTryCallIndirect StepResult.ofRes at h
    dsimp only at h
    split at h
    · obtain ⟨h1, h2, h3⟩ := stepCallIndirect_nofuncs_next h
      exact ⟨h1, h2, .inl h3⟩
    · cases h
    · cases h

theorem catchIn_ok {fr : Frame} {et : ExnTable} {e : Exn} {fr1 : Frame}
    {r : Res Frame} (h : catchIn fr et e = some r) (hr : r = .ok fr1) :
    fr1.func = fr.func ∧ fr1.body = [] := by
  unfold catchIn at h
  obtain ⟨d, -, rfl⟩ := Option.map_eq_some_iff.mp h
  cases hth : tryHandler d fr.func.freshValue with
  | ok bc =>
    simp only [hth, bind, Res.bind] at hr
    cases hs : fr.regs.setMany ((List.range e.payload.length).map (fr.func.freshValue + ·)) e.payload with
    | none => simp [hs, Res.ofOption] at hr
    | some regs =>
      simp only [hs, Res.ofOption, pure, Res.ok.injEq] at hr
      subst hr
      exact ⟨rfl, rfl⟩
  | trap c => simp [hth, bind, Res.bind] at hr
  | stuck m => simp [hth, bind, Res.bind] at hr

/-- A step with unwinding of a frame with an empty body, without callers, in a program without
functions, whose function's blocks have no statements, that continues: the same shape. -/
theorem stepX_nofuncs_next {env : XEnv} {fr : Frame} {m : Mem} {xs' : XState}
    (hf : ∀ B ∈ fr.func.blocks, B.body = []) (hb : fr.body = [])
    (h : stepX env { funcs := [] } ⟨⟨fr, [], m⟩, []⟩ = .next xs') :
    ∃ fr' m', xs' = ⟨⟨fr', [], m'⟩, []⟩ ∧ fr'.func = fr.func ∧ fr'.body = [] := by
  unfold stepX at h
  split at h
  · rename_i e mem _
    unfold raiseIn at h
    split at h
    · rename_i r hr
      cases hr' : r with
      | ok fr1 =>
        rw [hr'] at h
        simp only [XStepResult.ofRes, XStepResult.next.injEq] at h
        subst h
        obtain ⟨p1, -⟩ := Option.bind_eq_some_iff.mp hr
        obtain ⟨et, -, hc⟩ := Option.bind_eq_some_iff.mp hr
        obtain ⟨h1, h2⟩ := catchIn_ok hc hr'
        exact ⟨fr1, mem, rfl, h1, h2⟩
      | trap c => rw [hr'] at h; cases h
      | stuck msg => rw [hr'] at h; cases h
    · simp [unwindFrom] at h
  · cases hs : step env.toEnv { funcs := [] } ⟨fr, [], m⟩ with
    | next s1 =>
      rw [hs] at h
      obtain ⟨h1, h2, h3⟩ := step_nofuncs_next hb hs
      simp only [liftStep, XStepResult.next.injEq, h1] at h
      subst h
      obtain ⟨sf, scl, sm⟩ := s1
      simp only at h1 h2 h3
      subst h1
      refine ⟨sf, sm, by simp, h2, ?_⟩
      rcases h3 with h3 | ⟨B, hB, h3⟩
      · exact h3
      · rw [h3]; exact hf B hB
    | done v m1 => rw [hs] at h; cases h
    | trapped c => rw [hs] at h; cases h
    | stuck msg => rw [hs] at h; cases h

/-- Every state the run with unwinding reaches has an empty body. -/
theorem reach_body_nil {env : XEnv} {f : Function} (hf : ∀ B ∈ f.blocks, B.body = []) :
    ∀ {xs xs' : XState}, SReachX env { funcs := [] } xs xs' →
      ∀ fr m, xs = ⟨⟨fr, [], m⟩, []⟩ → fr.func = f → fr.body = [] → xs'.s.frame.body = [] := by
  intro xs xs' h
  induction h with
  | refl xs => intro fr m he _ hb; subst he; exact hb
  | step hs _ ih =>
    intro fr m he hfn hb
    subst he
    obtain ⟨fr', m', rfl, h1, h2⟩ := stepX_nofuncs_next (hfn ▸ hf) hb hs
    exact ih fr' m' rfl (h1.trans hfn) h2

theorem noMemTrapX_of_nil {env : XEnv} {f : Function} (hf : ∀ B ∈ f.blocks, B.body = [])
    {fr : Frame} {m : Mem} (hfn : fr.func = f) (hb : fr.body = []) :
    NoMemTrapX env { funcs := [] } ⟨fr, [], m⟩ := by
  intro xs' hr c st rest _ hst
  rw [reach_body_nil hf hr fr m rfl hfn hb] at hst
  cases hst

theorem noIndInternalX_of_nil {env : XEnv} {f : Function} (hf : ∀ B ∈ f.blocks, B.body = [])
    {fr : Frame} {m : Mem} (hfn : fr.func = f) (hb : fr.body = []) :
    NoIndInternalX env { funcs := [] } f ⟨fr, [], m⟩ := by
  intro xs' hr
  refine ⟨fun st rest sig callee args cv hst _ _ _ => ?_, fun _ _ _ _ _ _ _ _ g hg => nomatch hg⟩
  rw [reach_body_nil hf hr fr m rfl hfn hb] at hst
  cases hst
/-! ### The source function and its legalisation -/

def i128p : AbiParam := { ty := .i128 }
def i64p : AbiParam := { ty := .i64 }
def sigP : Signature := { params := [i128p], returns := [], callConv := some .systemV }
def sigL : Signature := { params := [i64p, i64p], returns := [], callConv := some .systemV }

def et : ExnTable :=
  { sig := 0, normal := { block := 1, args := [] }, items := [.tag 0 { block := 2, args := [.exn 0] }] }

/-- The source: `try_call %throw(v0)`, a `tag0` handler. -/
def src : Function :=
  { name := "w", sig := sigP, externs := [(0, { name := "throw", sig := sigP })],
    sigDecls := [(0, sigP)],
    blocks := [
      { id := 0, params := [(0, .i128)], term := .tryCall 0 [0] et },
      { id := 1, params := [], term := .ret [] },
      { id := 2, params := [(1, .i64)], term := .ret [] }] }

/-- The legalisation's entry block: the halves `v3`, `v4`, the pad zero `v5`. -/
def b0' : Block :=
  { id := 0, params := [(3, .i64), (4, .i64)], body := [{ results := [5], inst := .iconst .i64 0 }],
    term := .tryCall 0 [3, 4] et }

/-- The legalisation. -/
def gL : Function :=
  { name := "w", sig := sigL, externs := [(0, { name := "throw", sig := sigL })],
    sigDecls := [(0, sigL)],
    blocks := [b0',
      { id := 1, params := [], term := .ret [] },
      { id := 2, params := [(1, .i64)], term := .ret [] }] }

/-- Its certificate: `v0` is split into `v3`, `v4`; the pad zero is `v5`. -/
def certL : Cert := { pairs := [(0, 3, 4)], zero := 5 }

/-- **The legalisation pass computes `gL`, `certL`.** -/
theorem legal_eq : function128Cert src = .ok (gL, certL) := by
  have h : (function128Cert src).toOption.map (fun r => (r.1, r.2.pairs, r.2.zero)) =
      some (gL, certL.pairs, certL.zero) := by native_decide
  cases hc : function128Cert src with
  | error e => rw [hc] at h; simp [Except.toOption] at h
  | ok r =>
    rw [hc] at h
    obtain ⟨g, c⟩ := r
    obtain ⟨ps, z⟩ := c
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl

def C : Ctx := ⟨src, gL, certL⟩

def raises (n : String) : Bool := n == "throw"

def xe : XEnv := xenvWith raises 77

theorem validators : check C.f C.g C.cert = true ∧ exnOk C.f C.g C.cert = true := by
  decide +kernel

/-- The source frame on the argument `5 : i128`. -/
def fr0 : Frame :=
  { func := src, regs := (Regs.empty.setMany [0] [⟨.i128, 5⟩]).getD Regs.empty, slots := [],
    body := [], term := .tryCall 0 [0] et }

/-- The target frame on the halves `5`, `0`. -/
def fr0' : Frame :=
  { func := gL, regs := (Regs.empty.setMany [3, 4] [⟨.i64, 5⟩, ⟨.i64, 0⟩]).getD Regs.empty,
    slots := [], body := b0'.body, term := b0'.term }

/-- **The source run with unwinding raises and catches**: `%throw` raises, the `tag0` handler
catches, the run returns. -/
theorem caught :
    (runLoopX xe { funcs := [] } 10 ⟨⟨fr0, [], Mem.empty⟩, []⟩).returnedVals? = some [] := by
  decide +kernel

/-- `%throw` really raises: Rust's exception with object 77, the memory unchanged. -/
theorem throw_raises : xe.extern "throw" = some fun _ m => .unwound (panicExn 77) m := by
  simp [xe, xenvWith, raises, isDivHelper]

/-- **`check_refinesX` applies** to the raising-and-catching run with every premise discharged:
the target run with unwinding returns too. -/
theorem refines : ∃ vals' k M, runLoopX xe { funcs := [] } k ⟨⟨fr0', [], Mem.empty⟩, []⟩ =
    .returned vals' M := by
  obtain ⟨hc, hx⟩ := validators
  have hE : EnvOkX xe C { funcs := [] } { funcs := [] } :=
    xenvWith_envOkX raises 77 (indOldB_of_check hc) (fun _ _ _ => func?_nil _)
      (fun _ _ _ => func?_nil _)
      (fun ⟨B, hB, st, hst, _⟩ => by
        simp only [C, src, List.mem_cons, List.mem_nil_iff, or_false] at hB
        rcases hB with rfl | rfl | rfl <;> simp at hst)
  have hfb : ∀ B ∈ src.blocks, B.body = [] := by
    intro B hB
    simp only [src, List.mem_cons, List.mem_nil_iff, or_false] at hB
    rcases hB with rfl | rfl | rfl <;> rfl
  have hg : groups C.f.sig.params = some [[.lo, .hi]] := rfl
  have hexp : ExpRel ((groups C.f.sig.params).getD []) [⟨.i128, 5⟩] [⟨.i64, 5⟩, ⟨.i64, 0⟩] := by
    rw [hg]
    exact ⟨⟨5, 0, rfl, rfl, rfl⟩, trivial⟩
  have h := check_refinesX (C := C) hc hx hE (b := src.blocks.head!) (b' := b0')
    (args := [⟨.i128, 5⟩]) (args' := [⟨.i64, 5⟩, ⟨.i64, 0⟩]) (fr0 := fr0) (fr0' := fr0')
    (m := Mem.empty) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hexp
    (fun a n h => by simp [Mem.valid, Mem.empty] at h)
    (noMemTrapX_of_nil hfb rfl rfl) (noIndInternalX_of_nil hfb rfl rfl) 10
  obtain ⟨M, hM⟩ : ∃ M, runLoopX xe { funcs := [] } 10 ⟨⟨fr0, [], Mem.empty⟩, []⟩ = .returned [] M := by
    have := caught
    revert this
    cases runLoopX xe { funcs := [] } 10 ⟨⟨fr0, [], Mem.empty⟩, []⟩ <;> simp [XOutcome.returnedVals?]
  obtain ⟨vals', -, k, hk⟩ := h.1 [] M hM
  exact ⟨vals', k, M, hk⟩

end Clif.Rust.LegalXWitness

/-! ## `backend_correct_legal_unwind` on the compiled legalisation -/

namespace E2E.LegalUnwindWitness

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup Backend.Proof.UnwindTables
open Clif.Rust.LegalXWitness (src gL certL raises)
open E2E.DeadCleanupUnwindWitness (Xr Uw calleeUnwOkG_raise ok_getD ok_unit)

/-- The compiler's outputs on the legalisation (the defaults are never used: `checks_true`). -/
def vc : VCode := (lowerFunction gL).toOption.getD default
def vcp : VCode := (Backend.prepare (cleanupStage gL vc)).toOption.getD default
def rf : RFunc := spillAlloc vcp
def af : AFunc := (lowerRFunc vcp rf).toOption.getD default
def fa : FnAsm := (emitFunc 0 af).toOption.getD default
def fb : FnBin := fa.layout.toOption.getD default
def lsda : Option (List CallSite) := (callSites af fa).toOption.getD none
def rows : List (Nat × Cfi) := (unwindRows af fa).toOption.getD []

/-- The tables the unwinder reads: the emitted CIE, the FDE rows and the LSDA. -/
def T : Unw.FnTables := ⟨cieInsns, insnsFrom 0 rows, lsda.map (List.map (·.entry))⟩

/-- **The closed receipt**: every decidable premise of the pipeline and of the unwinding theorem
on the compiled legalisation (it has a landing pad: `lsda.isSome`, no indirect call). -/
def checks : Bool :=
  Backend.verifiable gL && lowerScopeB gL && !hasTls gL && (indSigs gL).isEmpty &&
  (lowerFunction gL).toBool && lowerCheckU gL vc &&
  (Backend.prepare (cleanupStage gL vc)).toBool && prepCheck (cleanupStage gL vc) vcp &&
  (checkAlloc vcp rf).toBool && (lowerRFunc vcp rf).toBool && (emitFunc 0 af).toBool &&
  fa.layout.toBool && savedCheck vcp rf && padsNonzeroB af fa && lastCallsOk af fa &&
  (callSites af fa).toBool && lsda.isSome && (unwindRows af fa).toBool

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Closed receipt (fixed-witness convention of `DeadCleanupUnwindWitness.checks_true`); not used
by any compiler correctness theorem. -/
theorem checks_true : checks = true := by native_decide

theorem facts :
    Backend.verifiable gL = true ∧ lowerScopeB gL = true ∧ hasTls gL = false ∧
    indSigs gL = [] ∧
    CompiledCleanup gL 0 vc vcp rf af fa fb ∧ lowerCheckU gL vc = true ∧
    savedCheck vcp rf = true ∧ padsNonzeroB af fa = true ∧ lastCallsOk af fa = true ∧
    callSites af fa = .ok lsda ∧ lsda.isSome = true ∧ unwindRows af fa = .ok rows := by
  have h := checks_true
  simp only [checks, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_iff, and_assoc] at h
  obtain ⟨hv, hs, ht, hi, hl, hlU, hp, hpc, hca, hal, hem, hla, hsv, hpad, hlast, hcs, hsome,
    hrows⟩ := h
  exact ⟨hv, hs, ht, hi, ⟨ok_getD hl, lowerCheck_of_U hlU, ok_getD hp, hpc, ok_unit hca,
    ok_getD hal, ok_getD hem, ok_getD hla⟩, hlU, hsv, hpad, hlast, ok_getD hcs, hsome,
    ok_getD hrows⟩

/-- The trusted Rust environment with unwinding, `%throw` raising object 77. -/
abbrev xe : Clif.XEnv := Clif.Rust.xenvWith raises 77

theorem mem_externs {ext : Clif.ExtFunc} (h : ext ∈ gL.externs.map (·.2)) :
    ext.name = "throw" := by
  simp only [gL, List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff, or_false] at h
  subst h; rfl

theorem xe_throw : xe.extern "throw" = some fun _ m => .unwound (Clif.Rust.panicExn 77) m :=
  Clif.Rust.LegalXWitness.throw_raises

/-- `%throw` never returns normally: the normal-return contract holds (vacuously). -/
theorem xCallsOk_xe (MR : MemRelT) (X : ExtSem) :
    XCallsOk xe.toEnv (gL.externs.map (·.2)) MR X := by
  intro ext hext g _ cm _ _ _ _ vals _ _ hg _ _ _ hr
  rw [mem_externs hext, Clif.Rust.xenvWith_toEnv_raise raises 77 (by decide) (by decide)] at hg
  cases hg
  cases hr

/-- **`%throw` raises Rust's exception object 77** (`IselSimUWitness.XR`) from every world. -/
theorem xRaiseOk_xe (MR : MemRelT) (X : ExtSem) :
    XRaiseOk xe (gL.externs.map (·.2)) MR X IselSimUWitness.XR := by
  intro ext hext g sl cm w d uses args vals e m hg _ _ hmr hu
  rw [mem_externs hext, xe_throw, Option.some.injEq] at hg
  subst hg
  simp only [Clif.XOutcome.unwound.injEq] at hu
  obtain ⟨rfl, rfl⟩ := hu
  exact ⟨77, w, rfl, ⟨rfl, rfl, rfl⟩, hmr⟩

/-- **`backend_correct_legal_unwind` applies to the compiled legalisation of the `i128`
function `src` with a `try_call` whose callee raises**: the validators, the program conditions,
the unwinding validator, every table and check premise, the raising callees' contracts
(`CalleeUnwOkG`, `XRaiseOk`, `XRaiseIndOk`), the normal-return contracts (vacuous: `%throw` never
returns), `FormsCovered`, `hTls`, `hslot` are discharged; left open as in
`DeadCleanupUnwindWitness.final_applies`: the machine's callee contracts (`hC`, `hCT`), the
linker's symbol addresses (`hsym`) and the run's entry premises. -/
theorem legal_unwind_applies {X0 : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {K : Nat}
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K (Xr X0) H
      vcp.CallSite)
    (hCT : ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) (Xr X0) H
      vcp.TrySite)
    (hsym : ∀ n b, syms n = some b → (Xr X0).sym n 0 = BitVec.ofNat 64 b)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups src.sig.params).getD []) args args')
    (hargs : ArgsIn gL.sig args' s) (hcs : ClifEntry src args cs) (hcs' : ClifEntry gL args' cs')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, af.slotBase, (RAFrame.compute vcp rf).intBase⟩ gL cs'.frame.slots cs'.mem w₀)
    (htrS : TrapsExplicitX xe { funcs := [] } cs) (htr : TrapsExplicitX xe { funcs := [] } cs')
    (fuel : Nat) :
    ArmRefinesLegalU ((Opt.Legal.groups src.sig.returns).getD []) fb base ra
      (Unw.ArmStepU (Xr X0) H Uw T fa) s (Clif.runLoopX xe { funcs := [] } fuel cs.toX) := by
  have hc : Opt.Legal.check src gL certL = true := Clif.Rust.LegalXWitness.validators.1
  have hx : Opt.Legal.exnOk src gL certL = true := Clif.Rust.LegalXWitness.validators.2
  obtain ⟨hv, hs, ht, hi, hcc, hlU, hsv, hpad, hlast, hsites, -, hrows⟩ := facts
  exact backend_correct_legal_unwind (f := src) (g := gL) (cert := certL) hc hx
    (InSubset.of_verifiable hv (fun _ => rfl)) hcc hlU raises 77
    (fun _ _ _ => Clif.Rust.LegalXWitness.func?_nil _)
    (fun _ _ _ => Clif.Rust.LegalXWitness.func?_nil _)
    (fun ⟨B, hB, st, hst, _⟩ => by
      simp only [src, List.mem_cons, List.mem_nil_iff, or_false] at hB
      rcases hB with rfl | rfl | rfl <;> simp at hst)
    (formsCovered_cleanup_complete (lowerScope_of hs) hcc.lower hcc.prepare _) hC (fun _ => hCT)
    (fun h => absurd h (by rw [ht]; decide))
    (fun base s => calleeUnwOkG_raise _ _ _ s _ X0 _ _)
    (fun _ => xCallsOk_xe _ _) (fun _ => hi ▸ xCallsIndOk_nil _ _ _)
    (fun _ => xRaiseOk_xe _ _) (fun _ => hi ▸ fun _ h => nomatch h)
    hsym rfl hsites rfl hrows rfl rfl hpad hlast hsv hent hres hbe hexp hargs hcs hcs' hsl hmem
    hrel htrS htr fuel

end E2E.LegalUnwindWitness

