import FV.Link.ExeUCompile
import FV.Link.DeadCleanupExe
import FV.E2E.LinkArmUProgNI

/-!
# The executable compiler is correct on the exceptional edges (S10f, #233)

`compileExeU S file0 = .ok file` (`Link.DeadCleanup.compileExe`, then `unwOkB`: what
`lake exe lean-link` decides): for the linked program with unwinding `L` of the compiler's input
(`L.toLinkSys = LinkSys.ofInputCleanup S.inputCleanup B F`, any base environment with its
raising callees `Ub`, `envX`, `XRb`):

* **the unwinder reads the theorem's tables from the executable**: at every pc of a compiled
  function `g`, libunwind's lookup in `file` (`Link.EhCheck.unwTables`: `.eh_frame_hdr`'s search,
  the FDE, its CIE and LSDA) gives `g`'s address and `(L.A g).tables`, the tables the linked
  machine with unwinding `L.machU` uses for `g`'s frames;
* **the program-level theorem with unwinding** (`E2E.backend_correct_program_budgetU'`, resp.
  `_peakU'`): the linked machine refines the whole-program run with unwinding, its `L.Ok` and
  `L.OkU`'s per-function premises discharged (`okBCleanup_sound`, the pipeline's `lowerCheck`,
  `Link.EhCheck.unwFnsB`); open, as there: `OkU`'s base-environment premises (`BaseU`), the
  raising base callees' non-interference `L.OkUNI` (vacuous without `L.NeedNI`) and the stack
  budget `L.Budget κ`.

`compileExe_correct` (and every theorem about `compileExe`) applies to `file` too
(`compileExeU_spec`).
-/

namespace Link.DeadCleanup

set_option autoImplicit false

open E2E E2E.LinkCheck E2E.DeadCleanupBinary Backend Backend.Proof Backend.Proof.Driver

/-- **`LinkSysU.OkU`'s premises about the base environment** (the per-function ones are decided
by the compiler: `okU_of`). -/
structure BaseU (L : LinkSysU) : Prop where
  envX : L.envX.toEnv = L.base
  indScopeX : ∀ g ∈ L.P.funcs, ¬ Clif.IndFree g → Clif.IndScopeX L.P L.envX L.syms
  baseXR : ∀ g ∈ L.P.funcs, ∀ F slotOff out c, XRaiseOk L.envX
    ((g.externs.map (·.2)).filter fun e => (L.P.func? e.name).isNone)
    (RelW ⟨F, L.syms, slotOff, out⟩ g c) L.Xb L.XRb
  baseXRI : ∀ g ∈ L.P.funcs, ∀ F slotOff out c, XRaiseIndOk { L.envX with sigOf := fun _ => none }
    (indSigs g) (RelW ⟨F, L.syms, slotOff, out⟩ g c) L.Xb L.XRb
  baseExcl : ∀ d uses w, L.BaseDest d → L.Xb.call d uses w ≠ none → L.XRb.raise d uses w = none
  baseRaiseExt : ∀ d uses w obj w', L.BaseDest d → L.XRb.raise d uses w = some (obj, w') →
    Arm.r .ERR w = .None → Arm.r .ERR w' = .None ∧ w'.program = w.program
  baseUnw : ∀ g ∈ L.P.funcs, ∀ info, (L.A g).vcp.CallSite info → L.BaseDest (destOf info) →
    ∀ (i : MInst), (i = .call info ∨ ∃ ti, i = .tryCall info ti) →
    ∀ F K G s0 Pc, UnwSoundG F K G s0 Pc (GotV (L.A g).vcp) L.Xb L.XRb L.Ub info i
  baseNoRaise : ∀ g ∈ L.P.funcs, ∀ info, (L.A g).vcp.CallSite info → L.BaseDest (destOf info) →
    ∀ (i : MInst), (i = .call info ∨ ∃ ti, i = .tryCall info ti) →
    ∀ (F : BitVec 64 → Prop) (K : Nat) (G : BitVec 64 → Prop) (s0 : Arm.ArmState)
      (Pc : BitVec 64 → MInst → Prop) (s : Arm.ArmState), K ≤ (spOf s).toNat →
    (∀ a, StackBelow K (spOf s) a → F a) → (∀ a, G a → s.mem a = s0.mem a) →
    ∀ (c : CheckCtx) (wh : String) (ops : Array Operand) (regs : Array Reg) (i' : MInst)
      (w : Arm.ArmState),
      i.operands = .ok ops → c.checkStatic wh ops (regs.map .reg) i.clobbers = .ok () →
      i.assign regs = .ok i' → Pc (Arm.r .PC s) i' → SameWorld F s w →
      Arm.CheckSPAlignment s → Arm.r .ERR s = .None →
      gotGuard (GotV (L.A g).vcp) L.Xb info (useVals ops regs s) →
      L.Xb.call (callDest info) (useVals ops regs s) w ≠ none →
      L.Ub.raise (callDest info) s = none
  baseKeepsPlaceU : L.NeedSlots → ∀ n g, L.envX.extern n = some g → ∀ vals m e m',
    g vals m = .unwound e m' → m'.place = m.place
  baseKeepsAllocsU : (L.NeedSlots ∨
      ∃ g ∈ L.P.funcs, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase ≠ 0) →
    ∀ n g, L.envX.extern n = some g → ∀ vals m,
      (∀ rvals m', g vals m = .returned rvals m' → ∀ x ∈ m'.allocs, x ∈ m.allocs) ∧
      (∀ e m', g vals m = .unwound e m' → ∀ x ∈ m'.allocs, x ∈ m.allocs)

/-- `OkU` from its base-environment premises and the per-function facts (no check on the calls
of the last block, #622). -/
theorem okU_of_any {L : LinkSysU} (hb : BaseU L)
    (hl : ∀ g ∈ L.P.funcs, lowerCheck g (L.A g).vc = true)
    (hf : ∀ g ∈ L.P.funcs, unwCheck g (L.A g).vc = true ∧
      (∃ l, callSites (L.A g).af (L.A g).fa = .ok l) ∧
      (∃ rows, unwindRows (L.A g).af (L.A g).fa = .ok rows) ∧
      padsNonzeroB (L.A g).af (L.A g).fa = true ∧
      savedCheck (L.A g).vcp (L.A g).rf = true) : L.OkU where
  envX := hb.envX
  lowerU g hg := by simp [lowerCheckU, hl g hg, (hf g hg).1]
  sites g hg := (hf g hg).2.1
  rows g hg := (hf g hg).2.2.1
  pads g hg := (hf g hg).2.2.2.1
  saved g hg := (hf g hg).2.2.2.2
  indScopeX := hb.indScopeX
  baseXR := hb.baseXR
  baseXRI := hb.baseXRI
  baseExcl := hb.baseExcl
  baseRaiseExt := hb.baseRaiseExt
  baseUnw := hb.baseUnw
  baseNoRaise := hb.baseNoRaise
  baseKeepsPlaceU := hb.baseKeepsPlaceU
  baseKeepsAllocsU := hb.baseKeepsAllocsU

/-- `OkU` from its base-environment premises and the per-function facts (statement kept;
`okU_of_any`). -/
theorem okU_of {L : LinkSysU} (hb : BaseU L)
    (hl : ∀ g ∈ L.P.funcs, lowerCheck g (L.A g).vc = true)
    (hf : ∀ g ∈ L.P.funcs, unwCheck g (L.A g).vc = true ∧
      (∃ l, callSites (L.A g).af (L.A g).fa = .ok l) ∧
      (∃ rows, unwindRows (L.A g).af (L.A g).fa = .ok rows) ∧
      padsNonzeroB (L.A g).af (L.A g).fa = true ∧
      lastCallsOk (L.A g).af (L.A g).fa = true ∧
      savedCheck (L.A g).vcp (L.A g).rf = true) : L.OkU :=
  okU_of_any hb hl fun g hg =>
    let h := hf g hg
    ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2⟩

/-- **The executable's unwind tables are the compiled functions'**: after
`compileExeU S file0 = .ok file`, at every pc of every compiled function `g`, libunwind's lookup
in `file` gives `g`'s address and its tables `(art I g).tables`. -/
theorem compileExeU_tables {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeU S file0 = .ok file) {g : Clif.Function}
    (hg : g ∈ (prog S.inputCleanup).funcs) {pc : Nat}
    (h1 : (art S.inputCleanup g).base.toNat ≤ pc)
    (h2 : pc < (art S.inputCleanup g).base.toNat + (art S.inputCleanup g).fb.size) :
    EhCheck.unwTables file pc =
      some ((art S.inputCleanup g).base.toNat, (art S.inputCleanup g).tables) := by
  obtain ⟨-, hu⟩ := compileExeU_spec h
  simp only [unwOkB, Bool.and_eq_true, parResultsCleanupT_input] at hu
  obtain ⟨T, hT, hu⟩ := EhCheck.ehOkR_sound hu.1 hg h1 h2
  obtain ⟨l, rows, hs, hr, rfl⟩ := EhCheck.tabsOf_spec hT
  obtain ⟨e1, e2, e3⟩ := Art.tables_eq hs hr
  rw [hu]
  congr 2
  cases ht : (art S.inputCleanup g).tables
  simp_all

/-- **What `compileExeU`'s success gives the linked program with unwinding**: `L.Ok`, `L.OkU`
(from the base-environment premises), and the executable's unwind tables at every pc of every
compiled function are the machine's. -/
theorem compileExeU_facts {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeU S file0 = .ok file) {B : BaseEnv} {F : BitVec 64 → Prop}
    (hB : BaseOk (LinkSys.ofInputCleanup S.inputCleanup B F))
    (hF : ∀ a, (LinkSys.ofInputCleanup S.inputCleanup B F).Img a → F a)
    {L : LinkSysU} (hLs : L.toLinkSys = LinkSys.ofInputCleanup S.inputCleanup B F)
    (hb : BaseU L) :
    L.Ok ∧ L.OkU ∧
      ∀ g ∈ L.P.funcs, ∀ pc, (L.A g).base.toNat ≤ pc → pc < (L.A g).base.toNat + (L.A g).fb.size →
        EhCheck.unwTables file pc = some ((L.A g).base.toNat, (L.A g).tables) := by
  obtain ⟨hc, hu⟩ := compileExeU_spec h
  obtain ⟨hin, hl⟩ := compileExe_spec hc
  have hI := okB_leanLink hin hl
  have hP : L.P = progOf S.inputCleanup.resultsCleanup := by rw [hLs]; rfl
  have hA : L.A = artOf S.inputCleanup.resultsCleanup := by rw [hLs]; rfl
  simp only [unwOkB, Bool.and_eq_true, parResultsCleanupT_input] at hu
  refine ⟨hLs ▸ okBCleanup_sound hI hB hF, okU_of_any hb ?_ ?_, ?_⟩
  · intro g hg
    rw [hP] at hg
    rw [hA]
    exact (factsCleanup hI hg).lowerOk
  · intro g hg
    rw [hP] at hg
    rw [hA]
    exact EhCheck.unwFnsB_sound hu.2 hg
  · intro g hg pc h1 h2
    rw [hP] at hg
    rw [hA] at h1 h2 ⊢
    exact compileExeU_tables h hg h1 h2

/-- **The executable compiler is correct on the exceptional edges** (runs of at most `M + 1`
steps): for `compileExeU S file0 = .ok file`, the linked program with unwinding `L` of the input
(any base environment `B`, `F`, its raising callees `L.Ub`, `L.envX`, `L.XRb` satisfying `BaseU`)
and a function `f` of the program: libunwind's lookup in `file` gives every compiled function's
address and the tables `L.machU` uses for its frames, and, for a stack budget `κ`, the linked
machine with unwinding refines `f`'s whole-program run with unwinding —
a return, a trap, or an exception leaving `f` (an AAPCS64 return to the caller with the
exception object in x0 and the live memory agreeing). -/
theorem compileExe_correct_unwind {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeU S file0 = .ok file) (B : BaseEnv) (F : BitVec 64 → Prop)
    (hB : BaseOk (LinkSys.ofInputCleanup S.inputCleanup B F))
    (hF : ∀ a, (LinkSys.ofInputCleanup S.inputCleanup B F).Img a → F a)
    (L : LinkSysU) (hLs : L.toLinkSys = LinkSys.ofInputCleanup S.inputCleanup B F)
    (hb : BaseU L) (hNI : L.OkUNI) {κ : Nat → Clif.Function → Nat} (hκ : L.Budget κ)
    {f : Clif.Function} (hf : f ∈ L.P.funcs) (M : Nat) {ra : BitVec 64}
    {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s) (hres : StackAvail (κ M f) (L.A f).af s)
    (hFw : L.F = frameWG (κ M f) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + κ M f) (spv s) a)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAt cs.mem (spv w₀))
    (htr : TrapsExplicitX (L.stdX.envRX M f) L.P.bare cs) :
    (∀ g ∈ L.P.funcs, ∀ pc, (L.A g).base.toNat ≤ pc → pc < (L.A g).base.toNat + (L.A g).fb.size →
        EhCheck.unwTables file pc = some ((L.A g).base.toNat, (L.A g).tables)) ∧
      ArmRefinesU (L.A f).fb (L.A f).base ra (L.machU M f) s
        (Clif.runLoopX L.envX L.P (M + 1) cs.toX) := by
  obtain ⟨hL, hU, ht⟩ := compileExeU_facts h hB hF hLs hb
  exact ⟨ht, backend_correct_program_budgetU' L hL hU hNI hκ hf M hent hres hFw hgfree himg hbe
    hargs hcs hsav hrel hpl htr⟩

/-- **The executable compiler is correct on the exceptional edges, for the run's peak call
depth** (`compileExe_correct_unwind` with `E2E.backend_correct_program_peakU'`): the linked
machine of depth `d`, the peak call depth of the whole-program run with unwinding, refines its
run of `Fu + 1` steps. -/
theorem compileExe_correct_unwind_peak {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeU S file0 = .ok file) (B : BaseEnv) (F : BitVec 64 → Prop)
    (hB : BaseOk (LinkSys.ofInputCleanup S.inputCleanup B F))
    (hF : ∀ a, (LinkSys.ofInputCleanup S.inputCleanup B F).Img a → F a)
    (L : LinkSysU) (hLs : L.toLinkSys = LinkSys.ofInputCleanup S.inputCleanup B F)
    (hb : BaseU L) (hNI : L.OkUNI) {κ : Nat → Clif.Function → Nat} (hκ : L.Budget κ)
    {f : Clif.Function} (hf : f ∈ L.P.funcs) (Fu d : Nat) {ra : BitVec 64}
    {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s) (hres : StackAvail (κ d f) (L.A f).af s)
    (hFw : L.F = frameWG (κ d f) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + κ d f) (spv s) a)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAt cs.mem (spv w₀))
    (hd : Clif.DepthLeX L.envX L.P d cs.toX)
    (htr : TrapsExplicitX ((L.peakX Fu).envRX d f) L.P.bare cs) :
    (∀ g ∈ L.P.funcs, ∀ pc, (L.A g).base.toNat ≤ pc → pc < (L.A g).base.toNat + (L.A g).fb.size →
        EhCheck.unwTables file pc = some ((L.A g).base.toNat, (L.A g).tables)) ∧
      ArmRefinesU (L.A f).fb (L.A f).base ra (L.machU d f) s
        (Clif.runLoopX L.envX L.P (Fu + 1) cs.toX) := by
  obtain ⟨hL, hU, ht⟩ := compileExeU_facts h hB hF hLs hb
  exact ⟨ht, backend_correct_program_peakU' L hL hU hNI hκ hf Fu d hent hres hFw hgfree himg hbe
    hargs hcs hsav hrel hpl hd htr⟩

/-- **`compileExe_correct_unwind`'s statement about an executable `file` of `S`**, curried: for
every linked program with unwinding of the input, function `f` of it and entry, the unwinder
reads the compiled functions' tables from `file` and the linked machine with unwinding refines
`f`'s whole-program run with unwinding. -/
def UnwindStmt (S : LinkSpec) (file : ByteArray) : Prop :=
  ∀ (B : BaseEnv) (F : BitVec 64 → Prop), BaseOk (LinkSys.ofInputCleanup S.inputCleanup B F) →
    (∀ a, (LinkSys.ofInputCleanup S.inputCleanup B F).Img a → F a) →
    ∀ (L : LinkSysU), L.toLinkSys = LinkSys.ofInputCleanup S.inputCleanup B F → BaseU L →
    L.OkUNI → ∀ {κ : Nat → Clif.Function → Nat}, L.Budget κ → ∀ {f : Clif.Function},
    f ∈ L.P.funcs → ∀ (M : Nat) {ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State},
    AbiEntry (L.A f).fb (L.A f).base ra s → StackAvail (κ M f) (L.A f).af s →
    L.F = frameWG (κ M f) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s →
    (∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + κ M f) (spv s) a) →
    (∀ a, L.Img a → s.mem a = L.imgMem a) →
    BodyEntry (L.A f).af s w₀ → ArgsIn f.sig args s → ClifEntry f args cs →
    StackArgsAvoid L.Img f.sig args s →
    Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀ →
    (L.NeedSlots → L.PlaceAt cs.mem (spv w₀)) →
    TrapsExplicitX (L.stdX.envRX M f) L.P.bare cs →
    (∀ g ∈ L.P.funcs, ∀ pc, (L.A g).base.toNat ≤ pc → pc < (L.A g).base.toNat + (L.A g).fb.size →
        EhCheck.unwTables file pc = some ((L.A g).base.toNat, (L.A g).tables)) ∧
      ArmRefinesU (L.A f).fb (L.A f).base ra (L.machU M f) s
        (Clif.runLoopX L.envX L.P (M + 1) cs.toX)

/-- `compileExeU`'s executables satisfy `UnwindStmt` (`compileExe_correct_unwind`). -/
theorem unwindStmt_of {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeU S file0 = .ok file) : UnwindStmt S file :=
  fun B F hB hF L hLs hb hNI _ hκ _ hf M _ _ _ _ _ hent hres hFw hgfree himg hbe hargs hcs hsav
    hrel hpl htr =>
  compileExe_correct_unwind h B F hB hF L hLs hb hNI hκ hf M hent hres hFw hgfree himg hbe hargs
    hcs hsav hrel hpl htr

end Link.DeadCleanup
