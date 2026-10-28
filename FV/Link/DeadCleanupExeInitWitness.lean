import FV.Link.ExeUnwindWitness
import FV.Link.DeadCleanupExeInit

/-!
# Witness: the executable theorem under the slot-byte oracle applies to a compiled executable

`f(x) = x`, compiled by the shipped compiler (`compile_eq`, `native_decide`) into a small static
executable laid out as `ExeUnwindWitness`'s, with no code outside the program (`closedBase`):

* `run_ret`: the whole-program run of `f` on `41` returns `41`;
* `exec_returns`: `Link.DeadCleanup.compileExe_correct_init` with the compiler-side premises
  discharged (`compile_eq`, `BaseOk`, `HooksSim`, the call graph), the entry contract
  (`Image.Intact`, `OutsideCall`, `ClifRunB` of the machine state `r`) and the oracle route's
  `InitOk` left: the run of the written `file` from `r` returns `41` to the caller (`ExecRefines`).

(`f` has no slotted program callee, so the oracle is unused here; a witness exercising an
unwritten slot read through this theorem is open, `docs/plans/uninit.md` §5.9.)
-/

namespace Link.DeadCleanup.InitWitness

open E2E E2E.LinkCheck E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes Backend Backend.Proof
  Backend.Proof.Driver

def srcF : String := "function %f(i64) -> i64 system_v {
block0(v0: i64):
    return v0
}
"

def fiF : FnInput := { clif := srcF, ra := "{}" }

/-- `f` placed at 16 MiB with the size the cleanup pipeline compiles it to. -/
def spec : LinkSpec :=
  let fs := [fiF]
  let names := fs.map (·.func.name)
  { funcs := fs, names,
    sizes := fs.map fun fi => (getOk (pipeCleanupT fi.func fi.k 0 (raJ fi.ra fi.j))).fb.words.size,
    outside := [], symNames := names, R := 0x1000000 }

/-- The compiled functions (`compileExe`'s). -/
def arts : List Art := (tabOf (parResultsCleanupT spec.input0)).map (·.2)

/-- **The executable before the compiler** (as `ExeUnwindWitness.file0`). -/
def file0 : ByteArray :=
  UnwindWitness.exeWith spec.R spec.size
    [(UnwindWitness.hdrAddr, UnwindWitness.ehSegOf arts UnwindWitness.hdrAddr
        UnwindWitness.gccAddr 0x2200000),
      (UnwindWitness.gccAddr, (UnwindWitness.gccOf arts).1 ++ [0, 0, 0, 0])]
    (12 + 8 * arts.length) (spec.addrs.map fun p => (BinCheck.symName p.1, p.2))

theorem compile_ok : (compileExe spec file0).toBool = true := by native_decide

/-- The executable. -/
def file : ByteArray := getOk (compileExe spec file0)

/-- **The shipped compiler compiles `{f}` to `file`.** -/
theorem compile_eq : compileExe spec file0 = .ok file := getOk_eq compile_ok

/-- `i64 -> i64 system_v`. -/
def sig1 : Clif.Signature :=
  { params := [{ ty := .i64 }], returns := [{ ty := .i64 }], callConv := some .systemV }

/-- The parsed `f`. -/
def fF : Clif.Function :=
  { name := "f", sig := sig1,
    blocks := [{ id := 0, params := [(0, .i64)], body := [], term := .ret [0] }] }

def P0 : Clif.Program := { funcs := [fF] }

/-- **The receipt**: the compiled program is `{f}`, no TLS, and `f` reaches no call cycle. -/
def chk : Bool :=
  decide (prog spec.inputCleanup = P0) && [fF].all (fun g => !hasTls g) &&
    DeadCleanupStackBound.goodN spec.inputCleanup "f"

set_option maxRecDepth 100000 in
theorem chk_true : chk = true := by native_decide

theorem P_eq : prog spec.inputCleanup = P0 := by
  have h := chk_true
  simp only [chk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

theorem funcs_tls : ∀ g ∈ (prog spec.inputCleanup).funcs, hasTls g = false := by
  have h := chk_true
  simp only [chk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true'] at h
  intro g hg
  rw [P_eq] at hg
  exact h.1.2 g hg

theorem hf : (prog spec.inputCleanup).func? "f" = some fF := by rw [P_eq]; rfl

theorem hc : ¬ DeadCleanupStackBound.CycleFrom
    (DeadCleanupStackBound.Calls spec.inputCleanup spec.inputCleanup.resultsCleanup) fF := by
  obtain ⟨hin, hl⟩ := compileExe_spec compile_eq
  have hg : DeadCleanupStackBound.goodN spec.inputCleanup "f" = true := by
    have h := chk_true
    simp only [chk, Bool.and_eq_true] at h
    exact h.2
  obtain ⟨f', hf', hcyc⟩ := (DeadCleanupStackBound.goodN_iff (okB_leanLink hin hl)).1 hg
  have : (prog spec.inputCleanup).func? "f" = some f' := hf'
  rw [hf] at this
  cases this
  exact hcyc

abbrev L : LinkSys := sys spec.inputCleanup closedBase

theorem baseOk : BaseOk L := baseOk_closedR funcs_tls

/-! ## The run: `f(41)` -/

def v41 : Clif.Val := ⟨.i64, 41⟩

/-- `f`'s entry state on `41` (empty memory). -/
def cs0 : Clif.State := ⟨⟨fF, Clif.Regs.set Clif.Regs.empty 0 v41, [], [], .ret [0]⟩, [], {}⟩

theorem cs0_init : Clif.initState P0 "f" [v41] {} = .ok cs0 := rfl

/-- **The whole-program run of `f` on `41` returns `41`.** -/
theorem run_ret : Clif.runLoop closedBase.env (prog spec.inputCleanup) (0 + 1) cs0 =
    .returned [v41] {} := by
  rw [P_eq]; rfl

/-! ## The executable theorem under the slot-byte oracle applies -/

/-- **The executable returns `41`** (`compileExe_correct_init`, the compiler-side premises
discharged; the entry contract and the oracle route's `InitOk` left). -/
theorem exec_returns {r : Arm.ArmState} (hX : (imageOf file).Intact r)
    (ho : OutsideCall spec.inputCleanup (BinCheck.roByte spec.inputCleanup spec.data) fF
      (DeadCleanupStackBound.stackFn spec.inputCleanup fF) r [v41] cs0.mem)
    (hr : ClifRunB spec.inputCleanup closedBase 0 fF r [v41] cs0)
    (hIO : InitOk (sysS spec.inputCleanup closedBase fF r (GotSlot spec.inputCleanup file))
      (kapW spec.inputCleanup closedBase fF r)) :
    ExecRefines (art spec.inputCleanup fF).fb (art spec.inputCleanup fF).base (xreg 30 r)
      (step spec.inputCleanup closedBase file) r (E2E.DeadCleanupBinCheck.RelocAt spec.inputCleanup)
      (.returned [v41] {}) :=
  compileExe_correct_init compile_eq closedBase baseOk (hooksSim_closed _) hf hc 0 hX ho hr hIO
    run_ret

end Link.DeadCleanup.InitWitness
