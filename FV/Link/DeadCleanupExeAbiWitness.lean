import FV.Link.ExeUnwindWitness
import FV.Link.DeadCleanupExeAbi

/-!
# Witness: the executable theorem with the `sret` return register (S7)

`s(p)` with an `sret` parameter and no returns (`function %s(i64 sret) system_v { block0(v0:
i64): return }`), compiled by the shipped compiler with the unwind tables checked
(`compileExeU`, `native_decide`) into a small static executable laid out as
`DeadCleanupExeTrapWitness`'s. With no code outside the program (`closedBase`):

* `run_returns`: the whole-program run of `s` on `p0` returns no CLIF value;
* `exec_returns_sret`: `Link.DeadCleanup.compileExe_correct_abi` with every premise discharged
  but the entry contract (`Image.Intact`, `OutsideCall`, `ClifRun` of the machine state `r`):
  the executable machine's run of the written `file` from `r` returns to the caller with the
  `sret` pointer `p0` in x8 (Cranelift's aarch64 ABI; until #587: x0).
-/

namespace Link.DeadCleanup.SretWitness

open E2E E2E.LinkCheck E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes Backend Backend.Proof
  Backend.Proof.Driver

def srcS : String := "function %s(i64 sret) system_v {
block0(v0: i64):
    return
}
"

def fiS : FnInput := { clif := srcS, ra := "{}" }

/-- `s` placed from 16 MiB with the size the cleanup pipeline compiles it to. -/
def spec : LinkSpec :=
  let fs := [fiS]
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

theorem compile_ok : (compileExeU spec file0).toBool = true := by native_decide

/-- The executable. -/
def file : ByteArray := getOk (compileExeU spec file0)

/-- **The shipped compiler (unwind tables checked) compiles `{s}` to `file`.** -/
theorem compile_eq : compileExeU spec file0 = .ok file := getOk_eq compile_ok

/-! ## The program -/

/-- The parsed `s`. -/
def fS : Clif.Function :=
  { name := "s",
    sig := { params := [{ ty := .i64, purpose := .sret }], callConv := some .systemV },
    blocks := [{ id := 0, params := [(0, .i64)], body := [], term := .ret [] }] }

def P0 : Clif.Program := { funcs := [fS] }

/-- **The receipt**: the compiled program is `{s}`, no TLS, `s` reaches no call cycle (`goodN`)
and binds its `sret` value once (`sretStableB`). -/
def chk : Bool :=
  decide (prog spec.inputCleanup = P0) && !hasTls fS &&
    DeadCleanupStackBound.goodN spec.inputCleanup "s" && sretStableB fS

set_option maxRecDepth 100000 in
theorem chk_true : chk = true := by native_decide

theorem P_eq : prog spec.inputCleanup = P0 := by
  have h := chk_true
  simp only [chk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1

theorem hS : sretStableB fS = true := by
  have h := chk_true
  simp only [chk, Bool.and_eq_true] at h
  exact h.2

theorem hf : (prog spec.inputCleanup).func? "s" = some fS := by rw [P_eq]; rfl

theorem hc : ¬ DeadCleanupStackBound.CycleFrom
    (DeadCleanupStackBound.Calls spec.inputCleanup spec.inputCleanup.resultsCleanup) fS := by
  obtain ⟨he, -⟩ := compileExeU_spec compile_eq
  obtain ⟨hin, hl⟩ := compileExe_spec he
  have hg : DeadCleanupStackBound.goodN spec.inputCleanup "s" = true := by
    have h := chk_true
    simp only [chk, Bool.and_eq_true] at h
    exact h.1.2
  obtain ⟨f', hf', hcyc⟩ := (DeadCleanupStackBound.goodN_iff (okB_leanLink hin hl)).1 hg
  have : (prog spec.inputCleanup).func? "s" = some f' := hf'
  rw [hf] at this
  cases this
  exact hcyc

/-! ## The base environment: no code outside the program -/

abbrev L : LinkSys := sys spec.inputCleanup closedBase

theorem baseOk : BaseOk L := baseOk_closedR fun g hg => by
  change g ∈ (prog spec.inputCleanup).funcs at hg
  rw [P_eq] at hg
  simp only [P0, List.mem_singleton] at hg
  subst hg
  have h := chk_true
  simp only [chk, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact h.1.1.2

/-! ## The run: `s(p0)` returns -/

/-- The struct pointer. -/
def p0 : Clif.Val := ⟨.i64, 0x4000⟩

def regs0 : Clif.Regs := Clif.Regs.set Clif.Regs.empty 0 p0

/-- `s`'s entry state on `p0` (empty memory). -/
def cs0 : Clif.State := ⟨⟨fS, regs0, [], [], .ret []⟩, [], {}⟩

/-- **The whole-program run of `s` on `p0` returns no CLIF value.** -/
theorem run_returns : ∃ cm, Clif.runLoop closedBase.env (prog spec.inputCleanup) (0 + 1) cs0 =
    .returned [] cm := by
  rw [P_eq]; exact ⟨_, rfl⟩

/-- `s`'s only state returns (no reachable state but the entry). -/
theorem cs0_reach {E : Clif.Env} {p : Clif.Program} {s : Clif.State} (h : Reach E p cs0 s) :
    s = cs0 := by
  cases h with
  | refl => rfl
  | step h1 _ =>
    obtain ⟨cm, h⟩ : ∃ cm, Clif.step E p cs0 = .done [] cm := ⟨_, rfl⟩
    rw [h] at h1; cases h1

/-- **`TrapsExplicit` holds**: `s` has no statement and no `try_call`. -/
theorem cs0_traps : TrapsExplicit (Clif.linkEnvN (prog spec.inputCleanup) closedBase.env 0)
    (prog spec.inputCleanup).bare cs0 where
  stmt _ _ _ _ hr _ hb := by rw [cs0_reach hr] at hb; cases hb
  tryCall _ _ _ _ _ _ _ _ _ B hB := by simp only [cs0, fS, List.mem_singleton] at hB; subst hB; simp
  tryCallInd _ _ _ _ _ _ _ _ _ B hB := by simp only [cs0, fS, List.mem_singleton] at hB; subst hB; simp
  indirect _ _ _ _ _ _ _ _ _ := fun ⟨B, hB, hst⟩ => by
    simp only [cs0, fS, List.mem_singleton] at hB; subst hB; simp at hst
  tryIndirect _ _ _ _ _ _ _ := fun ⟨B, hB, ht⟩ => by
    simp only [cs0, fS, List.mem_singleton] at hB; subst hB; simp at ht

/-- **`compileExe_correct_abi` applies to `s`**: every premise but the entry contract of `r`
discharged, a return of the executable machine's run of `file` from `r` leaves the `sret`
pointer `p0` in x8. -/
theorem exec_returns_sret {r : Arm.ArmState} (hX : (imageOf file).Intact r)
    (ho : OutsideCall spec.inputCleanup (BinCheck.roByte spec.inputCleanup spec.data) fS
      (DeadCleanupStackBound.stackFn spec.inputCleanup fS) r [p0] cs0.mem)
    (hr : ClifRun spec.inputCleanup closedBase fS r [p0] cs0) :
    ∃ k, ArmRet (xreg 30 r) r (runX (step spec.inputCleanup closedBase file) k r) ∧
      XHolds p0 (xreg 8 (runX (step spec.inputCleanup closedBase file) k r)) := by
  obtain ⟨he, -⟩ := compileExeU_spec compile_eq
  have := compileExe_correct_abi he closedBase baseOk (hooksSim_closed _) hf hS hc 0 hX ho hr
    cs0_traps
  obtain ⟨cm, hrun⟩ := run_returns
  rw [hrun, sretArg_of_sret (f := fS) (i := 0) (by decide) rfl] at this
  obtain ⟨k, hret, hx, -⟩ := this
  exact ⟨k, hret, by simpa using hx 0 p0 rfl⟩

end Link.DeadCleanup.SretWitness
