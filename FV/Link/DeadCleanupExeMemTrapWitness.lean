import FV.Link.ExeUnwindWitness
import FV.Link.DeadCleanupExeMemTrap

/-!
# Witness: the executable theorem with memory traps applies to a compiled executable (A3, #412)

`f(a, e, x) = atomic_cas.i64 a, e, x`, compiled by the shipped compiler (`compile_eq`,
`native_decide`) into a small static executable laid out as `ExeUnwindWitness`'s. With no code
outside the program (`closedBase`) and the memory map `nullMap` (nothing mapped below 4096, the
null page; everything else read-write):

* `run_traps`: the whole-program run of `f` on `(0, 1, 2)` traps with `heap_oob`: its
  `atomic_cas` accesses address 0, outside every CLIF allocation;
* `cs0_trapsExplicitM`, `cs0_mapFaults`: the new premises `TrapsExplicitM` and
  `MapFaults nullMap` hold for it; `cs0_not_trapsExplicit`: the old premise `TrapsExplicit` (of
  `compileExe_correct`) does not — the run was excluded before;
* `exec_traps`: `Link.DeadCleanup.compileExe_correct_memtrap` with every premise discharged but
  the entry contract (`Image.Intact`, `OutsideCall`, `ClifRun` of the machine state `r`): the
  executable machine's run of the written `file` from `r` reaches a trap site of `f` with
  `heap_oob` whose instruction word errs or faults under `nullMap` (`ExecTrapM`).
-/

namespace Link.DeadCleanup.MemTrapWitness

open E2E E2E.LinkCheck E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes Backend Backend.Proof
  Backend.Proof.Driver

def srcF : String := "function %f(i64, i64, i64) -> i64 system_v {
block0(v0: i64, v1: i64, v2: i64):
    v3 = atomic_cas.i64 v0, v1, v2
    return v3
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

/-! ## The program -/

/-- `(i64, i64, i64) -> i64 system_v`. -/
def sig3 : Clif.Signature :=
  { params := [{ ty := .i64 }, { ty := .i64 }, { ty := .i64 }], returns := [{ ty := .i64 }],
    callConv := some .systemV }

/-- `v3 = atomic_cas.i64 v0, v1, v2` (default flags: trap code `heap_oob`). -/
def casStmt : Clif.Stmt := { results := [3], inst := .atomicCas .i64 {} 0 1 2 }

/-- The parsed `f`. -/
def fF : Clif.Function :=
  { name := "f", sig := sig3,
    blocks := [{ id := 0, params := [(0, .i64), (1, .i64), (2, .i64)], body := [casStmt],
                 term := .ret [3] }] }

def P0 : Clif.Program := { funcs := [fF] }

/-- **The receipt**: the compiled program is `{f}`, no TLS, and `f` reaches no call cycle
(`goodN`). -/
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

/-! ## The base environment and the memory map -/

abbrev L : LinkSys := sys spec.inputCleanup closedBase

theorem baseOk : BaseOk L := baseOk_closedR funcs_tls

/-- **The memory map of the process**: nothing mapped below 4096 (the null page: Linux maps
nothing below `vm.mmap_min_addr`), everything else read-write. -/
def nullMap : ArmFault.MemMap := fun a => if a.toNat < 4096 then .none else .rw

/-! ## A run trapping at the `atomic_cas` on the null page: `f(0, 1, 2)` -/

def vA : Clif.Val := ⟨.i64, 0⟩
def vE : Clif.Val := ⟨.i64, 1⟩
def vX : Clif.Val := ⟨.i64, 2⟩

def regs0 : Clif.Regs :=
  Clif.Regs.set (Clif.Regs.set (Clif.Regs.set Clif.Regs.empty 0 vA) 1 vE) 2 vX

/-- `f`'s entry state on `(0, 1, 2)` (empty memory). -/
def cs0 : Clif.State := ⟨⟨fF, regs0, [], [casStmt], .ret [3]⟩, [], {}⟩

theorem cs0_init : Clif.initState P0 "f" [vA, vE, vX] {} = .ok cs0 := rfl

/-- `f`'s step is the `atomic_cas` at address 0: it traps `heap_oob` under every environment. -/
theorem cs0_step (E : Clif.Env) (p : Clif.Program) : Clif.step E p cs0 = .trapped .heapOob :=
  Opt.step_eq_lift_of (r := .trap .heapOob) rfl (fun _ h => nomatch h)

theorem cs0_reach {E : Clif.Env} {p : Clif.Program} {s : Clif.State} (h : Reach E p cs0 s) :
    s = cs0 := by
  cases h with
  | refl => rfl
  | step h1 _ => rw [cs0_step] at h1; cases h1

/-- **The whole-program run of `f` on `(0, 1, 2)` traps with `heap_oob`.** -/
theorem run_traps : Clif.runLoop closedBase.env (prog spec.inputCleanup) (0 + 1) cs0 =
    .trapped .heapOob := by
  rw [Clif.runLoop_succ', cs0_step]; rfl

/-- **The run premise `TrapsExplicitM` holds**: the only trapping statement is the `atomic_cas`. -/
theorem cs0_trapsExplicitM :
    TrapsExplicitM (Clif.linkEnvN (prog spec.inputCleanup) closedBase.env 0)
      (prog spec.inputCleanup).bare cs0 := by
  refine ⟨fun s c st rest hr _ hb => ?_, fun s _ _ _ _ hr _ hb => ?_,
    fun s _ _ _ _ hr _ hb => ?_, fun s st rest _ _ _ hr hb hi => ?_,
    fun s _ _ _ hr hb => ?_⟩
  · obtain rfl := cs0_reach hr
    simp only [cs0, List.cons.injEq] at hb
    obtain ⟨rfl, -⟩ := hb
    exact .inr rfl
  · obtain rfl := cs0_reach hr; cases hb
  · obtain rfl := cs0_reach hr; cases hb
  · obtain rfl := cs0_reach hr
    simp only [cs0, List.cons.injEq] at hb
    obtain ⟨rfl, -⟩ := hb
    cases hi
  · obtain rfl := cs0_reach hr; cases hb

/-- **The memory map premise `MapFaults nullMap` holds**: the trapping access is at address 0,
on the null page. -/
theorem cs0_mapFaults :
    MapFaults nullMap (Clif.linkEnvN (prog spec.inputCleanup) closedBase.env 0)
      (prog spec.inputCleanup).bare cs0 := by
  rintro s c a n hr ⟨-, -, st, rest, hb, hacc⟩
  obtain rfl := cs0_reach hr
  simp only [cs0, List.cons.injEq] at hb
  obtain ⟨rfl, -⟩ := hb
  change Clif.Access _ (.atomicCas .i64 {} 0 1 2) a n at hacc
  cases hacc with
  | atomicCas hv =>
    have h0 : cs0.frame.get 0 = .ok vA := rfl
    rw [h0] at hv
    cases hv
    exact ⟨0, by decide, by decide⟩

/-- **`TrapsExplicit` does not hold** for `f`'s run on `(0, 1, 2)`: the premise of
`compileExe_correct` excludes this run (its trapping statement is an `atomic_cas`). -/
theorem cs0_not_trapsExplicit :
    ¬ TrapsExplicit (Clif.linkEnvN (prog spec.inputCleanup) closedBase.env 0)
      (prog spec.inputCleanup).bare cs0 := by
  intro h
  have := h.stmt cs0 _ casStmt [] (.refl _) (cs0_step _ _) rfl
  simp [casStmt, explicitTrapInst] at this

/-! ## The executable theorem applies -/

/-- **The executable reaches the `atomic_cas`'s memory trap**: for every machine state `r`
meeting the entry contract of an outside call of `f` on `(0, 1, 2)` (`Image.Intact`,
`OutsideCall`, `ClifRun`), the run of the written executable `file` from `r` reaches a trap site
of `f` with `heap_oob` whose instruction word errs or faults under `nullMap`
(`Link.DeadCleanup.compileExe_correct_memtrap`, every other premise discharged). -/
theorem exec_traps {r : Arm.ArmState} (hX : (imageOf file).Intact r)
    (ho : OutsideCall spec.inputCleanup (BinCheck.roByte spec.inputCleanup spec.data) fF
      (DeadCleanupStackBound.stackFn spec.inputCleanup fF) r [vA, vE, vX] cs0.mem)
    (hr : ClifRun spec.inputCleanup closedBase fF r [vA, vE, vX] cs0) :
    ∃ k, ExecTrapM nullMap spec.inputCleanup file fF .heapOob
      (runX (step spec.inputCleanup closedBase file) k r) := by
  have := compileExe_correct_memtrap compile_eq closedBase baseOk (hooksSim_closed _) hf hc 0 hX
    ho hr cs0_trapsExplicitM cs0_mapFaults
  rw [run_traps] at this
  exact this

end Link.DeadCleanup.MemTrapWitness
