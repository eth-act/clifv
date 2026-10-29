module

public import FV.Link.ExeUnwindWitness
public import FV.Link.DeadCleanupExeInitR

@[expose] public section

/-!
# Witness: the executable theorem under the slot-byte oracle covers a trapping run

`f(x) = 1 / x` (`udiv`), compiled by the shipped compiler (`compile_eq`, `native_decide`) into a
small static executable laid out as `ExeUnwindWitness`'s, with no code outside the program
(`closedBase`). For a concrete caller state `rC` (the executable's bytes, `x0 = 0`,
`sp = 0x100000`):

* `run_traps`: the whole-program run of `f` on `0` traps with `int_divz` (its division);
* `trapsExplicit`: the trap is the division, an explicitly trapping instruction (`TrapsExplicit`,
  the run premise of `compileExe_correct_initTR`), under every environment;
* `intact`, `outsideCall`, `clifRunB`: the entry contract of `rC` and the reference CLIF run
  (`f` has no stack slots and no program callee, so the slot-placement oracle is not needed:
  `not_needSlots`);
* **`divz_traps_initR`**: `compileExe_correct_initTR` on this run: the executable's run from `rC`
  reaches the trap site with `int_divz` (`ExecRefines`), under the corrected oracle-route premises
  `InitOkR` only.
-/

namespace Link.DeadCleanup.InitTrapWitness

open E2E E2E.LinkCheck E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes Backend Backend.Proof
  Backend.Proof.Driver

def srcF : String := "function %f(i64) -> i64 system_v {
block0(v0: i64):
    v1 = iconst.i64 1
    v2 = udiv v1, v0
    return v2
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

abbrev I : LinkInput := spec.inputCleanup

abbrev B : BaseEnv := closedBase

/-! ## The program -/

/-- `i64 -> i64 system_v`. -/
def sig1 : Clif.Signature :=
  { params := [{ ty := .i64 }], returns := [{ ty := .i64 }], callConv := some .systemV }

/-- `v1 = iconst.i64 1`. -/
def constStmt : Clif.Stmt := { results := [1], inst := .iconst .i64 1#64 }

/-- `v2 = udiv v1, v0`. -/
def divStmt : Clif.Stmt := { results := [2], inst := .div .udiv .i64 1 0 }

/-- The parsed `f`. -/
def fF : Clif.Function :=
  { name := "f", sig := sig1,
    blocks := [{ id := 0, params := [(0, .i64)], body := [constStmt, divStmt], term := .ret [2] }] }

def P0 : Clif.Program := { funcs := [fF] }

/-- **The receipt**: the compiled program is `{f}`, no TLS, and `f` reaches no call cycle. -/
def chk : Bool :=
  decide (prog I = P0) && [fF].all (fun g => !hasTls g) && DeadCleanupStackBound.goodN I "f"

set_option maxRecDepth 100000 in
theorem chk_true : chk = true := by native_decide

theorem P_eq : prog I = P0 := by
  have h := chk_true
  simp only [chk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

theorem funcs_tls : ∀ g ∈ (prog I).funcs, hasTls g = false := by
  have h := chk_true
  simp only [chk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true'] at h
  intro g hg
  rw [P_eq] at hg
  exact h.1.2 g hg

theorem hf : (prog I).func? "f" = some fF := by rw [P_eq]; rfl

theorem hc : ¬ DeadCleanupStackBound.CycleFrom
    (DeadCleanupStackBound.Calls I I.resultsCleanup) fF := by
  obtain ⟨hin, hl⟩ := compileExe_spec compile_eq
  have hg : DeadCleanupStackBound.goodN I "f" = true := by
    have h := chk_true
    simp only [chk, Bool.and_eq_true] at h
    exact h.2
  obtain ⟨f', hf', hcyc⟩ := (DeadCleanupStackBound.goodN_iff (okB_leanLink hin hl)).1 hg
  have : (prog I).func? "f" = some f' := hf'
  rw [hf] at this
  cases this
  exact hcyc

theorem baseOk : BaseOk (sys I B) := baseOk_closedR funcs_tls

/-- **No function of the program has stack slots**: the slot-placement oracle is not needed. -/
theorem not_needSlots : ¬ (sys I B).NeedSlots := by
  rintro ⟨g, -, h, hcl, hne⟩
  have hh := (sys I B).callee_mem hcl
  change h ∈ (prog I).funcs at hh
  rw [P_eq] at hh
  simp only [P0, List.mem_singleton] at hh
  subst hh
  exact hne rfl

/-! ## The run: `f(0)` divides by zero -/

def v0 : Clif.Val := ⟨.i64, 0⟩

def regs0 : Clif.Regs := Clif.Regs.set Clif.Regs.empty 0 v0

/-- The caller's CLIF memory: the image's symbols, nothing allocated, no slot placement. -/
def mem0 : Clif.Mem := { symbols := fun n => I.syms.lookup n }

/-- `f`'s entry state on `0`. -/
def cs0 : Clif.State := ⟨⟨fF, regs0, [], [constStmt, divStmt], .ret [2]⟩, [], mem0⟩

theorem cs0_init : Clif.initState (prog I) "f" [v0] mem0 = .ok cs0 := by rw [P_eq]; rfl

/-- The state after `v1 = iconst.i64 1`. -/
def cs1 : Clif.State :=
  ⟨⟨fF, Clif.Regs.set regs0 1 ⟨.i64, 1#64⟩, [], [divStmt], .ret [2]⟩, [], mem0⟩

theorem cs0_step (E : Clif.Env) (p : Clif.Program) : Clif.step E p cs0 = .next cs1 :=
  Opt.step_eq_lift_of (r := .next cs1.frame mem0) rfl (fun _ h => nomatch h)

/-- The division by zero traps under every environment. -/
theorem cs1_step (E : Clif.Env) (p : Clif.Program) : Clif.step E p cs1 = .trapped .intDivz :=
  Opt.step_eq_lift_of (r := .trap .intDivz) rfl (fun _ h => nomatch h)

theorem reach {E : Clif.Env} {p : Clif.Program} {s : Clif.State} (h : Reach E p cs0 s) :
    s = cs0 ∨ s = cs1 := by
  cases h with
  | refl => exact .inl rfl
  | step h1 h2 =>
    rw [cs0_step] at h1
    cases h1
    cases h2 with
    | refl => exact .inr rfl
    | step h3 _ => rw [cs1_step] at h3; cases h3

def M0 : Nat := 2

/-- **The whole-program run of `f` on `0` traps with `int_divz`.** -/
theorem run_traps : Clif.runLoop B.env (prog I) (M0 + 1) cs0 = .trapped .intDivz := by
  rw [Clif.runLoop_succ', cs0_step]
  show Clif.runLoop B.env (prog I) (1 + 1) cs1 = _
  rw [Clif.runLoop_succ', cs1_step]
  rfl

/-- **The run premise**: the only trapping step is the division, an explicitly trapping
instruction; `f` has neither `try_call` terminators nor indirect calls. -/
theorem trapsExplicit (E : Clif.Env) (p : Clif.Program) : TrapsExplicit E p cs0 where
  stmt s c st rest hr hs hb := by
    rcases reach hr with rfl | rfl
    · rw [cs0_step] at hs; cases hs
    · simp only [cs1, List.cons.injEq] at hb
      obtain ⟨rfl, -⟩ := hb
      rfl
  tryCall s _ _ _ _ hr _ hb := by rcases reach hr with rfl | rfl <;> cases hb
  tryCallInd s _ _ _ _ hr _ hb := by rcases reach hr with rfl | rfl <;> cases hb
  indirect s st rest _ _ _ hr hb hi := by
    rcases reach hr with rfl | rfl
    · simp only [cs0, List.cons.injEq] at hb
      obtain ⟨rfl, -⟩ := hb
      cases hi
    · simp only [cs1, List.cons.injEq] at hb
      obtain ⟨rfl, -⟩ := hb
      cases hi
  tryIndirect s _ _ _ hr hb := by rcases reach hr with rfl | rfl <;> cases hb

/-! ## The caller's state and the entry contract -/

def raC : BitVec 64 := 0x500000

/-- **The caller's machine state**: the executable's bytes, `x0 = 0`, `sp = 0x100000`, the
return address `0x500000`, at `f`. -/
def rC : Arm.ArmState :=
  Arm.w .PC (art I fF).base (Arm.w (.GPR 30#5) raC (Arm.w (.GPR 0#5) 0#64
    (Arm.w (.GPR 31#5) 0x100000#64
      (setMem Arm.ArmState.default fun a => ((imageOf file).mem a).getD 0))))

theorem intact : (imageOf file).Intact rC := by
  intro a b _ hb
  simp only [rC, Arm.w, Arm.write_base_pc, Arm.write_base_gpr]
  show ((imageOf file).mem a).getD 0 = b
  rw [hb]; rfl

/-- The image predicate as a `Bool`. -/
def imgD (a : BitVec 64) : Bool :=
  (tabOf I.resultsCleanup).any fun e =>
    (e.2.fb.program e.2.base).any fun p => decide ((a - p.1).toNat < 4)

theorem imgD_iff (a : BitVec 64) : imgD a = true ↔ img I a := by
  unfold imgD img ImgT CodeAddr
  rw [List.any_eq_true]
  constructor
  · rintro ⟨e, he, hp⟩
    obtain ⟨p, hp, hlt⟩ := List.any_eq_true.mp hp
    exact ⟨e, he, p, by rw [program_set_program]; exact hp, of_decide_eq_true hlt⟩
  · rintro ⟨e, he, p, hp, hlt⟩
    rw [program_set_program] at hp
    exact ⟨e, he, List.any_eq_true.mpr ⟨p, hp, decide_eq_true hlt⟩⟩

/-- The caller's facts: `pc` at `f`, no error, the return address outside the code, `sp` the
16-aligned `0x100000` with `f`'s stack bound below it, the code at and above `0x1000000` (so above
the stack), `f`'s only parameter in `x0` holding `0`. -/
def entryB : Bool :=
  Arm.r .PC rC == (art I fF).base && (match Arm.r .ERR rC with | .None => true | _ => false) &&
  !imgD (xreg 30 rC) && spv rC == 0x100000#64 &&
  decide (DeadCleanupStackBound.stackFn I fF ≤ 0x100000) &&
  (tabOf I.resultsCleanup).all (fun e => (e.2.fb.program e.2.base).all fun p =>
    decide (0x1000000 ≤ p.1.toNat ∧ p.1.toNat + 4 ≤ 2 ^ 64)) &&
  (match locsOf fF.sig with
    | [.reg x] => (regVal rC x).setWidth v0.ty.width == v0.bits
    | _ => false)

set_option maxRecDepth 100000 in
theorem entryB_true : entryB = true := by native_decide

/-- **The entry contract of the caller's state** (`OutsideCall`), each field from `entryB`: no
code below `sp` (the code lies at and above `0x1000000`); the CLIF memory has no allocation, so
its byte, image and validity clauses are vacuous; the symbols are the image's. -/
theorem outsideCall : OutsideCall I (BinCheck.roByte I spec.data) fF
    (DeadCleanupStackBound.stackFn I fF) rC [v0] cs0.mem := by
  have h := entryB_true
  simp only [entryB, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_true_eq,
    List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hpc, herr⟩, hra⟩, hsp⟩, hst⟩, hcode⟩, hargs⟩ := h
  have hv : ∀ a n, cs0.mem.valid a n = false := fun _ _ => rfl
  refine ⟨hpc, ?_, fun hi => ?_, ?_, ?_, fun a ha hb => ?_, ?_, fun a b hva => ?_,
    fun a b b' hva => ?_, fun a n hva => ?_, rfl⟩
  · split at herr <;> first | assumption | cases herr
  · rw [(imgD_iff _).mpr hi] at hra; cases hra
  · rw [hsp]; decide
  · rw [hsp]; exact Nat.le_trans hst (by decide)
  · obtain ⟨e, he, hp⟩ := List.any_eq_true.mp ((imgD_iff a).mpr ha)
    obtain ⟨p, hp, hlt⟩ := List.any_eq_true.mp hp
    have hlt := of_decide_eq_true hlt
    obtain ⟨hlo, hhi⟩ := of_decide_eq_true (List.all_eq_true.mp (hcode e he) p hp)
    rw [hsp] at hb
    have hs := BitVec.toNat_sub a p.1
    have ha' := a.isLt
    have hb1 := hb.1
    simp only [BitVec.toNat_ofNat] at hb1 hs
    omega
  · intro loc v hm
    split at hargs
    · rename_i x hl
      rw [hl] at hm
      simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      exact beq_iff_eq.mp hargs
    · cases hargs
  · rw [hv] at hva; cases hva
  · rw [hv] at hva; cases hva
  · rw [hv] at hva; cases hva

/-- **The reference CLIF run of the outside call**: `f`'s entry on `0` (no slots; the placement
clause is vacuous, `not_needSlots`). -/
theorem clifRunB : ClifRunB I B M0 fF rC [v0] cs0 :=
  ⟨clifEntry_initState (p := prog I) hf cs0_init, (fun _ _ h => by cases h),
    fun hN => absurd hN not_needSlots⟩

/-! ## The executable theorem on the trapping run -/

/-- **The executable traps with `int_divz`, corrected premises** (module doc): the run of the
written `file` from `rC` refines the whole-program CLIF run of `f` on `0`, which traps with
`int_divz`. The only premise left is the oracle route's `InitOkR`. -/
theorem divz_traps_initR
    (hIO : InitOkR (sysS I B fF rC (GotSlot I file)) (kapW I B fF rC)) :
    ExecRefines (art I fF).fb (art I fF).base (xreg 30 rC) (step I B file) rC
      (E2E.DeadCleanupBinCheck.RelocAt I) (.trapped .intDivz) :=
  compileExe_correct_initTR compile_eq B baseOk (hooksSim_closed _) hf hc M0 intact outsideCall
    clifRunB hIO (trapsExplicit _ _) run_traps

end Link.DeadCleanup.InitTrapWitness
