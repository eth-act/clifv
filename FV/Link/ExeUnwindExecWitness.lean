import FV.Link.OptExeUnwindExec
import FV.Link.OptExeUnwindWitness

/-!
# Witness: the executable-bytes theorems with unwinding apply (S10g, #404)

On the `%rec` executables of `FV/Link/ExeUnwindWitness.lean` (`compileExeU`) and
`FV/Link/OptExeUnwindWitness.lean` (`compileExeOptU`):

* `exec_applies`: `compileExe_correct_unwind_exec_peak_of_good` instantiated at the written
  executable and `%rec` (open: the premises about the base environment, the entry and the
  per-state facts `RunOkU`); `opt_exec_applies`: `compileExeOpt_correct_unwind_exec_peak_of_good`
  at the optimising compiler's executable;
* **the frame walk computed on the file**: at `%rec`'s self-call (offset 152, return address
  `base + 156`), libunwind's lookup in the written executable gives `%rec`'s tables, `%rec` has no
  LSDA (Rust's personality continues), and its row at the call has a CFA rule (`x29 + 16`,
  Cranelift's frame), so the
  frame of every state is unwound by its row (`frame_continues`) and phase 2 of that frame on the
  file is the model's (`frame_eq`: `Unw.unwindAt` with `%rec`'s tables at its address, the
  exception object in x0 over the restored frame); a frame whose restored return address is
  outside the program's code ends the walk there (`walk_out`).
-/

namespace Link.DeadCleanup.UnwindExecWitness

open E2E E2E.LinkCheck E2E.BinCheck E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes Backend
  Backend.Proof Backend.Proof.UnwindTables UnwindWitness

theorem f_eq : (prog spec.inputCleanup).func? "rec" = some f := by
  have : ((prog spec.inputCleanup).func? "rec").isSome = true := by native_decide
  obtain ⟨g, hg⟩ := Option.isSome_iff_exists.1 this
  rw [hg, show f = g by simp [f, hg]]

/-- **`compileExe_correct_unwind_exec_peak_of_good` applies to `file`** (open: the premises
about the base environment, the entry and the per-state facts of the model's run). -/
theorem exec_applies (B : BaseEnv) (hB : BaseOk (sys spec.inputCleanup B)) (Fu d : Nat)
    {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall spec.inputCleanup (BinCheck.roByte spec.inputCleanup spec.data) f
      (frameDrop (art spec.inputCleanup f).af + (spec.inputCleanup.D * d + pbMax spec.inputCleanup))
      r args cs.mem)
    (hr : ClifRun spec.inputCleanup B f r args cs)
    (L : LinkSysU) (hLs : L.toLinkSys = LinkSys.ofInputCleanup spec.inputCleanup B
      (worldF spec.inputCleanup f (spec.inputCleanup.D * d + pbMax spec.inputCleanup) r))
    (hb : BaseU L) (hNI : L.OkUNI) (hUS : UnwSim spec.inputCleanup L.Ub)
    (hra1 : ¬ img spec.inputCleanup (xreg 30 r - 1))
    (hd : Clif.DepthLeX L.envX L.P d cs.toX)
    (htr : TrapsExplicitX ((L.peakX Fu).envRX d f) L.P.bare cs)
    (hrun : RunOkU spec.inputCleanup B file L d f (modelOf spec.inputCleanup f r)) :
    ExecRefinesU (art spec.inputCleanup f).fb (art spec.inputCleanup f).base (xreg 30 r)
      (stepU spec.inputCleanup B L.Ub file) r (DeadCleanupBinCheck.RelocAt spec.inputCleanup)
      (Clif.runLoopX L.envX L.P (Fu + 1) cs.toX) :=
  compileExe_correct_unwind_exec_peak_of_good compile_eq B hB f_eq Fu d hX ho hr L hLs hb hNI
    hUS hra1 hd htr hrun

/-- **`compileExeOpt_correct_unwind_exec_peak_of_good` applies to the optimising compiler's
`file`** (open as `exec_applies`). -/
theorem opt_exec_applies (B : BaseEnv) (hB : BaseOk (sys OptUnwindWitness.specO.opt.inputCleanup B))
    (d : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf OptUnwindWitness.file).Intact r)
    (ho : OutsideCall OptUnwindWitness.specO.opt.inputCleanup
      (BinCheck.roByte OptUnwindWitness.specO.opt.inputCleanup OptUnwindWitness.specO.opt.data)
      OptUnwindWitness.f' (frameDrop (art OptUnwindWitness.specO.opt.inputCleanup
        OptUnwindWitness.f').af + (OptUnwindWitness.specO.opt.inputCleanup.D * d +
          pbMax OptUnwindWitness.specO.opt.inputCleanup)) r args cs'.mem)
    (hr : ClifRun OptUnwindWitness.specO.opt.inputCleanup B OptUnwindWitness.f' r args cs')
    (hcs : ClifEntry OptUnwindWitness.f args cs)
    (hregs : cs.frame.regs = cs'.frame.regs) (hsl : cs.frame.slots = cs'.frame.slots)
    (hmem : cs.mem = cs'.mem)
    (L : LinkSysU) (hLs : L.toLinkSys = LinkSys.ofInputCleanup
      OptUnwindWitness.specO.opt.inputCleanup B (worldF OptUnwindWitness.specO.opt.inputCleanup
        OptUnwindWitness.f' (OptUnwindWitness.specO.opt.inputCleanup.D * d +
          pbMax OptUnwindWitness.specO.opt.inputCleanup) r))
    (hb : BaseU L) (hNI : L.OkUNI) (hkeep : Opt.EnvKeepsSymbolsX L.envX)
    (hUS : UnwSim OptUnwindWitness.specO.opt.inputCleanup L.Ub)
    (hra1 : ¬ img OptUnwindWitness.specO.opt.inputCleanup (xreg 30 r - 1))
    (hd : Clif.DepthLeX L.envX L.P d cs'.toX)
    (htr : ∀ Fu, TrapsExplicitX ((L.peakX Fu).envRX d OptUnwindWitness.f') L.P.bare cs')
    (hrun : RunOkU OptUnwindWitness.specO.opt.inputCleanup B OptUnwindWitness.file L d
      OptUnwindWitness.f' (modelOf OptUnwindWitness.specO.opt.inputCleanup OptUnwindWitness.f' r))
    (k : Nat) :
    ExecRefinesU (art OptUnwindWitness.specO.opt.inputCleanup OptUnwindWitness.f').fb
      (art OptUnwindWitness.specO.opt.inputCleanup OptUnwindWitness.f').base (xreg 30 r)
      (stepU OptUnwindWitness.specO.opt.inputCleanup B L.Ub OptUnwindWitness.file) r
      (DeadCleanupBinCheck.RelocAt OptUnwindWitness.specO.opt.inputCleanup)
      (Clif.runLoopX L.envX (prog OptUnwindWitness.specO.inputCleanup) k cs.toX) :=
  compileExeOpt_correct_unwind_exec_peak_of_good OptUnwindWitness.compile_eq B hB
    OptUnwindWitness.f_eq OptUnwindWitness.f'_eq d hX ho hr hcs hregs hsl hmem L hLs hb hNI hkeep
    hUS hra1 hd htr hrun k

/-! ## The frame walk on the written executable -/

/-- `%rec`'s address. -/
theorem base_eq : (art spec.inputCleanup f).base = 0x1000000#64 := by native_decide

/-- The return address of `%rec`'s self-call (its `bl` at offset 152). -/
def ra : BitVec 64 := 0x100009c#64

theorem lsda_none : (art spec.inputCleanup f).tables.lsda = none := by
  have hs : callSites (art spec.inputCleanup f).af (art spec.inputCleanup f).fa = .ok none := by
    native_decide
  simp [Art.tables, hs, Except.toOption]

/-- The row of `%rec`'s frame at its self-call: CFA = `x29 + 16`. -/
theorem row_cfa :
    (Unw.rowAt (art spec.inputCleanup f).tables.cie (art spec.inputCleanup f).tables.fde 155).cfaReg
      = 29 := by
  have hr : ((unwindRows (art spec.inputCleanup f).af (art spec.inputCleanup f).fa).toOption.map
      fun rows => (Unw.rowAt cieInsns (insnsFrom 0 rows) 155).cfaReg) = some 29 := by
    native_decide
  cases hu : unwindRows (art spec.inputCleanup f).af (art spec.inputCleanup f).fa with
  | error e => rw [hu] at hr; simp [Except.toOption] at hr
  | ok rows =>
    rw [hu] at hr
    simp only [Except.toOption, Option.map_some, Option.some.injEq] at hr
    simp only [Art.tables, hu, Except.toOption, Option.getD_some]
    exact hr

theorem lookup_ra : EhCheck.unwTables file (ra - 1).toNat =
    some ((art spec.inputCleanup f).base.toNat, (art spec.inputCleanup f).tables) :=
  tables (by rw [base_eq]; decide) (by
    have := size_pos
    rw [base_eq]
    show 16777371 < 16777216 + (art spec.inputCleanup f).fb.size
    have : 156 ≤ (art spec.inputCleanup f).fb.size := by native_decide
    omega)

/-- **The frame of `%rec`'s self-call is unwound by its row** in every state: the file's lookup
gives `%rec`'s tables, the personality continues (no LSDA), the row has a CFA rule. -/
theorem frame_continues (t : Arm.ArmState) : Continues file ra t := by
  refine ⟨_, _, lookup_ra, by rw [lsda_none]; rfl, ?_⟩
  have e : (ra - 4 + 4 - 1 - BitVec.ofNat 64 (art spec.inputCleanup f).base.toNat).toNat = 155 := by
    rw [base_eq]; decide
  rw [e]
  simp only [Unw.restore, Unw.Row.cfa?, Unw.regVal?, row_cfa]
  simp

/-- **Phase 2 of that frame on the file is the model's**: `Unw.unwindAt` with `%rec`'s tables at
its address, which (the personality continuing) is the exception object in x0 over the frame
restored by the row. -/
theorem frame_eq (obj : BitVec 64) (t : Arm.ArmState) :
    unwFrame file ra obj t =
      Unw.unwindAt (art spec.inputCleanup f).tables (art spec.inputCleanup f).base
        ((art spec.inputCleanup f).base + 152#64) obj t ∧
    ∃ t', Unw.restore (Unw.rowAt (art spec.inputCleanup f).tables.cie
        (art spec.inputCleanup f).tables.fde 155) t = some t' ∧
      unwFrame file ra obj t = Arm.w (.GPR 0#5) obj t' := by
  have e1 : BitVec.ofNat 64 (art spec.inputCleanup f).base.toNat = (art spec.inputCleanup f).base := by
    simp
  have e2 : ra - 4 = (art spec.inputCleanup f).base + 152#64 := by rw [base_eq]; decide
  have h1 : unwFrame file ra obj t =
      Unw.unwindAt (art spec.inputCleanup f).tables (art spec.inputCleanup f).base
        ((art spec.inputCleanup f).base + 152#64) obj t := by
    simp only [unwFrame, lookup_ra, e1, e2]
  refine ⟨h1, ?_⟩
  obtain ⟨_, _, hl, -, hr⟩ := frame_continues t
  rw [lookup_ra] at hl
  simp only [Option.some.injEq, Prod.mk.injEq] at hl
  obtain ⟨rfl, rfl⟩ := hl
  have e3 : ((art spec.inputCleanup f).base + 152#64 + 4 - 1 - (art spec.inputCleanup f).base).toNat =
      155 := by rw [base_eq]; decide
  have e4 : (ra - 4 + 4 - 1 - BitVec.ofNat 64 (art spec.inputCleanup f).base.toNat).toNat = 155 := by
    rw [base_eq]; decide
  rw [e4] at hr
  obtain ⟨t', ht'⟩ := Option.isSome_iff_exists.1 hr
  refine ⟨t', ht', ?_⟩
  rw [h1]
  simp only [Unw.unwindAt, e3, lsda_none, Unw.personality, ht']

/-- **The walk ends at `%rec`'s frame when its restored return address is outside the program's
code** (the exception leaves the program to the outside caller). -/
theorem walk_out (obj : BitVec 64) (t : Arm.ArmState)
    (h : ¬ img spec.inputCleanup (Arm.r .PC (unwFrame file ra obj t) - 1)) :
    Walk spec.inputCleanup file ra obj t (unwFrame file ra obj t) :=
  .last fun hn => h hn.2

end Link.DeadCleanup.UnwindExecWitness
