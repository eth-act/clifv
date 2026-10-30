import FV.Link.ExeUnwindWitness
import FV.Link.DeadCleanupExeInit
import FV.E2E.LinkSlotSysWitness
import FV.E2E.LinkMachEval
import FV.E2E.LinkPlaceBTable

/-!
# Witness: the executable theorem under the slot-byte oracle covers a stale read

The slotted program of `LinkSlotSysWitness` (`f n = r (h n)`; `h` stores `n` in its slot; `r`
loads its slot without writing it and adds it), compiled by the shipped compiler into a static
executable (`compile_eq`). `h` and `r` have the same frame, so `r`'s load reads the stack bytes
`h` left: the machine computes `f 41 = 82`.

For a concrete caller state `rC` (the executable's bytes, `x0 = 41`, `sp = 0x100000`):

* `modelOf_eq`: the model state is the computable `sC`;
* `iniB_one`, `iniB_two`: the machine's own slot table (`iniB`, noncomputable) at its entries
  `1` (`h`) and `2` (`r`) is the memory at the machine's calls of `h` and `r`, read off the
  certified mirror (`LinkMachEval`, `tabB_at`);
* `run_csC`: the whole-program CLIF run under the computable table `bC` (those two entries)
  returns `82`; `run_zero`: with a zero table it returns `41` (the read is stale);
* **`run_init`**: the CLIF run from the reference entry placed with the machine's own table
  returns `82` (`runWith_withTable`);
* **`stale_read_returns`**: `compileExe_correct_init` on this run: the executable's run from `rC`
  returns `82` to the caller (`ExecRefines`), under the entry contract `OutsideCall` and the oracle
  route's `InitOk`;
* `outsideCall`: the entry contract holds for `rC`; **`stale_read_returns_init`**: the same with
  only `InitOk` left.
-/

namespace Link.DeadCleanup.InitSlotWitness

open E2E E2E.LinkCheck E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes Backend Backend.Proof
  Backend.Proof.Driver

/-! ## The executable -/

def fis : List FnInput := [{ clif := LinkSlotSysWitness.srcF, ra := "{}" },
  { clif := LinkSlotSysWitness.srcH, ra := "{}" }, { clif := LinkSlotSysWitness.srcR, ra := "{}" }]

/-- `f`, `h`, `r` placed at 16 MiB. -/
def spec : LinkSpec :=
  let fs := fis
  let names := fs.map (·.func.name)
  { funcs := fs, names,
    sizes := fs.map fun fi => (getOk (pipeCleanupT fi.func fi.k 0 (raJ fi.ra fi.j))).fb.words.size,
    outside := [], symNames := names, R := 0x1000000 }

def arts : List Art := (tabOf (parResultsCleanupT spec.input0)).map (·.2)

def file0 : ByteArray :=
  UnwindWitness.exeWith spec.R spec.size
    [(UnwindWitness.hdrAddr, UnwindWitness.ehSegOf arts UnwindWitness.hdrAddr
        UnwindWitness.gccAddr 0x2200000),
      (UnwindWitness.gccAddr, (UnwindWitness.gccOf arts).1 ++ [0, 0, 0, 0])]
    (12 + 8 * arts.length) (spec.addrs.map fun p => (BinCheck.symName p.1, p.2))

theorem compile_ok : (compileExe spec file0).toBool = true := by native_decide

def file : ByteArray := getOk (compileExe spec file0)

/-- **The shipped compiler compiles `{f, h, r}` to `file`.** -/
theorem compile_eq : compileExe spec file0 = .ok file := getOk_eq compile_ok

abbrev I : LinkInput := spec.inputCleanup

abbrev B : BaseEnv := closedBase

def fF : Clif.Function := ((prog I).func? "f").getD default
def fH : Clif.Function := ((prog I).func? "h").getD default
def fR : Clif.Function := ((prog I).func? "r").getD default

/-- The program's facts: the three functions, no TLS, no call cycle from `f`, slots. -/
def progB : Bool :=
  (prog I).func? "f" == some fF && (prog I).func? "h" == some fH && (prog I).func? "r" == some fR &&
    fF.name == "f" && (prog I).funcs.all (fun g => !hasTls g) &&
    DeadCleanupStackBound.goodN I "f" && !fH.slots.isEmpty && !fR.slots.isEmpty &&
    fH.blocks.length == 1

set_option maxRecDepth 100000 in
theorem progB_true : progB = true := by native_decide

theorem hf : (prog I).func? "f" = some fF := by
  have h := progB_true; simp only [progB, Bool.and_eq_true, beq_iff_eq] at h; exact h.1.1.1.1.1.1.1.1
theorem hfH : (prog I).func? "h" = some fH := by
  have h := progB_true; simp only [progB, Bool.and_eq_true, beq_iff_eq] at h; exact h.1.1.1.1.1.1.1.2
theorem hfR : (prog I).func? "r" = some fR := by
  have h := progB_true; simp only [progB, Bool.and_eq_true, beq_iff_eq] at h; exact h.1.1.1.1.1.1.2
theorem fF_name : fF.name = "f" := by
  have h := progB_true; simp only [progB, Bool.and_eq_true, beq_iff_eq] at h; exact h.1.1.1.1.1.2
theorem funcs_tls : ∀ g ∈ (prog I).funcs, hasTls g = false := by
  have h := progB_true
  simp only [progB, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at h
  exact h.1.1.1.1.2
theorem goodN_f : DeadCleanupStackBound.goodN I "f" = true := by
  have h := progB_true; simp only [progB, Bool.and_eq_true] at h; exact h.1.1.1.2
theorem slotted_fH : LinkSys.slotted fH = 1 := by
  have h := progB_true; simp only [progB, Bool.and_eq_true, Bool.not_eq_true'] at h
  simp [LinkSys.slotted, h.1.1.2]
theorem slotted_fR : LinkSys.slotted fR = 1 := by
  have h := progB_true; simp only [progB, Bool.and_eq_true, Bool.not_eq_true'] at h
  simp [LinkSys.slotted, h.1.2]

theorem hc : ¬ DeadCleanupStackBound.CycleFrom
    (DeadCleanupStackBound.Calls I I.resultsCleanup) fF := by
  obtain ⟨hin, hl⟩ := compileExe_spec compile_eq
  obtain ⟨f', hf', hcyc⟩ := (DeadCleanupStackBound.goodN_iff (okB_leanLink hin hl)).1 goodN_f
  have : (prog I).func? "f" = some f' := hf'
  rw [hf] at this
  cases this
  exact hcyc

theorem baseOk : BaseOk (sys I B) := baseOk_closedR funcs_tls

theorem okC : okBCleanup I = true := by
  obtain ⟨hin, hl⟩ := compileExe_spec compile_eq
  exact okB_leanLink hin hl

/-! ## The caller's state and the model state -/

def raC : BitVec 64 := 0x500000

/-- **The caller's machine state**: the executable's bytes, `x0 = 41`, `sp = 0x100000`, the
return address `0x500000`, at `f`. -/
def rC : Arm.ArmState :=
  Arm.w .PC (art I fF).base (Arm.w (.GPR 30#5) raC (Arm.w (.GPR 0#5) 41#64
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

/-- **The model state**, computable. -/
def sC : Arm.ArmState :=
  Arm.set_program (setMem rC fun a => if imgD a then imgMem I a else rC.mem a)
    ((art I fF).fb.program (art I fF).base)

theorem modelOf_eq : modelOf I fF rC = sC := by
  unfold modelOf sC
  congr 2
  funext a
  by_cases h : img I a
  · simp only [h, (imgD_iff a).mpr h, ↓reduceIte]
  · have h' : imgD a = false := by
      cases hd : imgD a
      · rfl
      · exact absurd ((imgD_iff a).mp hd) h
    simp only [h, h', ↓reduceIte, Bool.false_eq_true]

/-! ## The machine run -/

/-- The linked system the binary-level proofs instantiate (`sysW`). -/
abbrev LO : LinkSys := sysW I B fF rC

abbrev LS : LinkSys := sys I B

def M0 : Nat := 15
def fuel0 : Nat := 400

/-- The mirrored machine run of `f` from the model state. -/
def runM (n : Nat) : Arm.ArmState := runX (LS.machC fuel0 M0 fF) n sC

/-- The machine's facts: the mirror takes the machine's path for `18` steps, without error;
`f` calls `h` at step `14` (its first call) and `r` at step `17` (its second); `h` has no call
instruction. -/
def machB : Bool :=
  LS.okC fuel0 M0 fF sC 18 &&
  (List.range 18).all (fun j => match Arm.r .ERR (runM j) with | .None => true | _ => false) &&
  decide (insnAtC (LS.A fF).fa (progBase (runM 14)) (Arm.r .PC (runM 14)) = some (.bl "h")) &&
  decide (insnAtC (LS.A fF).fa (progBase (runM 17)) (Arm.r .PC (runM 17)) = some (.bl "r")) &&
  ((List.range 14).filter fun j => callPcB (LS.A fF).fa (LS.A fF).base (Arm.r .PC (runM j))).length == 0 &&
  ((List.range 17).filter fun j => callPcB (LS.A fF).fa (LS.A fF).base (Arm.r .PC (runM j))).length == 1 &&
  callPcB (LS.A fF).fa (LS.A fF).base (Arm.r .PC (runM 14)) &&
  callPcB (LS.A fF).fa (LS.A fF).base (Arm.r .PC (runM 17)) &&
  progBase (runM 14) == (LS.A fF).base && progBase (runM 17) == (LS.A fF).base &&
  (LS.A fH).fa.lines.toList.all (fun l => match l with
      | Line.ins (.bl _) _ | Line.ins (.blr _) _ => false | _ => true) &&
  (LS.P.funcs.all fun g => decide (((LS.A g).fa.lines.toList.map Line.size).sum ≤ 2 ^ 64))

set_option maxRecDepth 100000 in
theorem machB_true : machB = true := by native_decide

theorem machB_parts : LS.okC fuel0 M0 fF sC 18 = true ∧
    (∀ j < 18, Arm.r .ERR (runM j) = .None) ∧
    insnAtC (LS.A fF).fa (progBase (runM 14)) (Arm.r .PC (runM 14)) = some (.bl "h") ∧
    insnAtC (LS.A fF).fa (progBase (runM 17)) (Arm.r .PC (runM 17)) = some (.bl "r") ∧
    ((List.range 14).filter fun j => callPcB (LS.A fF).fa (LS.A fF).base (Arm.r .PC (runM j))).length = 0 ∧
    ((List.range 17).filter fun j => callPcB (LS.A fF).fa (LS.A fF).base (Arm.r .PC (runM j))).length = 1 ∧
    callPcB (LS.A fF).fa (LS.A fF).base (Arm.r .PC (runM 14)) = true ∧
    callPcB (LS.A fF).fa (LS.A fF).base (Arm.r .PC (runM 17)) = true ∧
    progBase (runM 14) = (LS.A fF).base ∧ progBase (runM 17) = (LS.A fF).base ∧
    (LS.A fH).fa.lines.toList.all (fun l => match l with
      | Line.ins (.bl _) _ | Line.ins (.blr _) _ => false | _ => true) = true ∧
    (∀ g ∈ LS.P.funcs, ((LS.A g).fa.lines.toList.map Line.size).sum ≤ 2 ^ 64) := by
  have h := machB_true
  simp only [machB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  refine ⟨h1, fun j hj => ?_, h3, h4, h5, h6, h7, h8, h9, h10, List.all_eq_true.mpr h11, h12⟩
  have := h2 j hj
  split at this
  · assumption
  · cases this

theorem fF_mem : fF ∈ LS.P.funcs := (Clif.Program.func?_some hf).1
theorem fH_mem : fH ∈ LS.P.funcs := (Clif.Program.func?_some hfH).1

/-- **The machine's first `18` steps are the mirror's.** -/
theorem runEq {j : Nat} (hj : j ≤ 18) : runX (LO.std.mach M0 fF) j sC = runM j := by
  rw [LinkSys.mach_std, mach_F I B _ (fun _ => False)]
  exact LS.runX_mach_eq fuel0 machB_parts.2.2.2.2.2.2.2.2.2.2.2 M0 fF sC 18 fF_mem machB_parts.1 j hj

theorem cb_eq {n : Nat} (hn : n ≤ 18) :
    callsBefore (LO.std.mach M0 fF) (LO.std.A fF).fa (LO.std.A fF).base sC n =
      ((List.range n).filter fun j => callPcB (LS.A fF).fa (LS.A fF).base (Arm.r .PC (runM j))).length := by
  rw [callsBefore_eq]
  congr 1
  refine List.filter_congr fun j hj => ?_
  rw [runEq (by have := List.mem_range.mp hj; omega)]
  rfl

theorem hL : LO.std.Ok :=
  (okBCleanup_sound okC (baseOk_F baseOk) (fun _ h => .inr h)).withCrun _

theorem hK : LO.std.HooksKeep :=
  ⟨fun _ s h => by
      show Arm.r .ERR (Arm.w .PC (Arm.r .PC s + 4) s) ≠ .None
      rw [Arm.r_of_w_different (by simp)]; exact h,
    fun _ _ _ h => h, fun _ s => Arm.w_program, fun _ _ _ => rfl⟩

theorem hprog : sC.program = (LO.std.A fF).fb.program (LO.std.A fF).base := by
  simp only [sC, program_set_program]; rfl

theorem insnAt_at {j : Nat} (hj : j ≤ 18) (hpb : progBase (runM j) = (LS.A fF).base) {i : Insn}
    (hi : insnAtC (LS.A fF).fa (progBase (runM j)) (Arm.r .PC (runM j)) = some i) :
    insnAt (LO.std.A fF).fa (LO.std.A fF).base (Arm.r .PC (runX (LO.std.mach M0 fF) j sC)) = some i := by
  rw [runEq hj]
  show insnAt (LS.A fF).fa (LS.A fF).base _ = _
  rw [insnAt_eq_insnAtC (machB_parts.2.2.2.2.2.2.2.2.2.2.2 fF fF_mem)]
  rw [hpb] at hi
  exact hi

theorem herr {i : Nat} (hi : i < 18) :
    ∀ j ≤ i, Arm.r .ERR (runX (LO.std.mach (14 + 1) fF) j sC) = .None := fun j hj => by
  rw [show 14 + 1 = M0 from rfl, runEq (by omega)]
  exact machB_parts.2.1 j (by omega)

theorem hcp {j : Nat} (hj : j ≤ 18)
    (h : callPcB (LS.A fF).fa (LS.A fF).base (Arm.r .PC (runM j)) = true) :
    CallPc (LO.std.A fF).fa (LO.std.A fF).base (Arm.r .PC (runX (LO.std.mach (14 + 1) fF) j sC)) := by
  rw [show 14 + 1 = M0 from rfl, runEq hj]
  exact (callPc_iff _ _ _).mpr h

theorem hct1 : LO.std.CallsTo fF (runX (LO.std.mach (14 + 1) fF) 14 sC) fH :=
  .inl ⟨"h", insnAt_at (by decide) machB_parts.2.2.2.2.2.2.2.2.1 machB_parts.2.2.1, hfH⟩

theorem hct2 : LO.std.CallsTo fF (runX (LO.std.mach (14 + 1) fF) 17 sC) fR :=
  .inl ⟨"r", insnAt_at (by decide) machB_parts.2.2.2.2.2.2.2.2.2.1 machB_parts.2.2.2.1, hfR⟩

theorem cb23 : callsBefore (LO.std.mach (14 + 1) fF) (LO.std.A fF).fa (LO.std.A fF).base sC 14 = 0 :=
  (cb_eq (by decide)).trans machB_parts.2.2.2.2.1

theorem cb26 : callsBefore (LO.std.mach (14 + 1) fF) (LO.std.A fF).fa (LO.std.A fF).base sC 17 = 1 :=
  (cb_eq (by decide)).trans machB_parts.2.2.2.2.2.1

/-- The first call's entries: `h`'s own, and none of its run's (`h` makes no call). -/
theorem callE0 : LO.std.callE (14 + 1) fF sC 0 = 1 := by
  have := LO.std.callE_call (hcp (by decide) machB_parts.2.2.2.2.2.2.1) hct1
  rw [cb23, slotted_fH] at this
  rw [this]
  split
  · simp only [LinkSys.cntE]
    rw [callsBefore_noCalls (fa := (LO.std.A fH).fa) _ machB_parts.2.2.2.2.2.2.2.2.2.2.1]
    rfl
  · rfl

theorem callE1_ge : 1 ≤ LO.std.callE (14 + 1) fF sC 1 := by
  have := LO.std.callE_call (hcp (by decide) machB_parts.2.2.2.2.2.2.2.1) hct2
  rw [cb26, slotted_fR] at this
  omega

/-- **Entry `1` of the machine's table**: the memory at the machine's call of `h`. -/
theorem tab1 : LO.std.tabB M0 fF sC 0 1 = fun a => (runM 14).mem (BitVec.ofNat 64 a) := by
  have e := LO.std.tabB_at (M := 14) hL hK fF_mem hprog (herr (by decide))
    (hcp (by decide) machB_parts.2.2.2.2.2.2.1) hct1 (x := 1) (k := 0)
    (by rw [cb23]; simp [Clif.sumTo]) (fun _ => by rw [cb23]; simp [Clif.sumTo, callE0])
  rw [cb23, slotted_fH, ite_eq_left_of_eq_true _ _ (eq_true (by simp [Clif.sumTo]))] at e
  rw [show M0 = 14 + 1 from rfl, e]
  funext a
  show (runX (LO.std.mach M0 fF) 14 sC).mem _ = _
  rw [runEq (by decide)]

/-- **Entry `2` of the machine's table**: the memory at the machine's call of `r`. -/
theorem tab2 : LO.std.tabB M0 fF sC 0 2 = fun a => (runM 17).mem (BitVec.ofNat 64 a) := by
  have e := LO.std.tabB_at (M := 14) hL hK fF_mem hprog (herr (by decide))
    (hcp (by decide) machB_parts.2.2.2.2.2.2.2.1) hct2 (x := 2) (k := 0)
    (by rw [cb26]; simp [Clif.sumTo, callE0])
    (fun _ => by rw [cb26]; have := callE1_ge; simp only [Clif.sumTo, callE0]; omega)
  rw [cb26, slotted_fR, ite_eq_left_of_eq_true _ _ (eq_true (by simp [Clif.sumTo, callE0]))] at e
  rw [show M0 = 14 + 1 from rfl, e]
  funext a
  show (runX (LO.std.mach M0 fF) 17 sC).mem _ = _
  rw [runEq (by decide)]

/-- The machine's own table of the outside call is the sysW one at the model state. -/
theorem iniB_eq : iniB I B M0 fF rC = LO.std.iniOf M0 fF sC := by
  unfold iniB
  rw [← iniOf_F I B (worldF I fF (DeadCleanupStackBound.bud I fF) rC), modelOf_eq]

/-! ## The CLIF run -/

/-- **The computable table**: entries `1` and `2` are the memory at the machine's calls of `h`
and `r` (`tab1`, `tab2`); zero elsewhere. -/
def bC (k a : Nat) : BitVec 8 :=
  if k = 1 then (runM 14).mem (BitVec.ofNat 64 a)
  else if k = 2 then (runM 17).mem (BitVec.ofNat 64 a) else 0

/-- The caller's CLIF memory: placed at `sp = 0x100000` with the table `b`. -/
def memB (b : Nat → Nat → BitVec 8) : Clif.Mem :=
  { symbols := fun n => I.syms.lookup n, place := some ⟨[0x100000#64], LS.frames, some ⟨b, 0⟩⟩ }

def v41 : Clif.Val := ⟨.i64, 41#64⟩

def csOf (b : Nat → Nat → BitVec 8) : Clif.State :=
  match Clif.initState (prog I) "f" [v41] (memB b) with
  | .ok cs => cs
  | _ => default

def csC : Clif.State := csOf bC

/-- The CLIF facts: `f`'s entry on `41` under `bC` (placed at `f`'s body `sp`, counter `0`, no
slots), its run returns `82` with the counter advanced by `2`; under the zero table it returns
`41`. -/
def clifB : Bool :=
  (match Clif.initState (prog I) "f" [v41] (memB bC) with | .ok _ => true | _ => false) &&
  csC.mem.place.map (fun pl => (pl.sps, pl.init.map (·.next))) ==
    some ([spBody (art I fF).af rC, 0x100000#64], some 0) &&
  csC.frame.slots.isEmpty &&
  (match Clif.runLoop B.env (prog I) (M0 + 1) csC with
    | .returned [v] m => v.ty == .i64 && v.bits.toNat == 82 &&
        m.place.map (fun pl => pl.init.map (·.next)) == some (some 2)
    | _ => false) &&
  (match Clif.runLoop B.env (prog I) (M0 + 1) (csOf fun _ _ => 0) with
    | .returned [v] _ => v.bits.toNat == 41
    | _ => false)

set_option maxRecDepth 100000 in
theorem clifB_true : clifB = true := by native_decide

theorem init_ok : Clif.initState (prog I) "f" [v41] (memB bC) = .ok csC := by
  have h := clifB_true
  simp only [clifB, Bool.and_eq_true] at h
  have h1 := h.1.1.1.1
  unfold csC csOf
  split at h1 <;> rename_i hi
  · rw [hi]
  · cases h1

theorem run_csC : ∃ v m, Clif.runLoop B.env (prog I) (M0 + 1) csC = .returned [v] m ∧
    v.ty = .i64 ∧ v.bits.toNat = 82 ∧ m.place.map (fun pl => pl.init.map (·.next)) = some (some 2) := by
  have h := clifB_true
  simp only [clifB, Bool.and_eq_true] at h
  have h2 := h.1.2
  split at h2
  · rename_i v m hr
    simp only [Bool.and_eq_true, beq_iff_eq] at h2
    exact ⟨v, m, hr, h2.1.1, h2.1.2, h2.2⟩
  · cases h2

/-- **With a zero table the same entry returns `41`**: the run's result depends on the stale
bytes. -/
theorem run_zero : ∃ v m, Clif.runLoop B.env (prog I) (M0 + 1) (csOf fun _ _ => 0) = .returned [v] m ∧
    v.bits.toNat = 41 := by
  have h := clifB_true
  simp only [clifB, Bool.and_eq_true] at h
  have h3 := h.2
  split at h3
  · rename_i v m hr
    exact ⟨v, m, hr, by simpa using h3⟩
  · cases h3

theorem csC_place : csC.mem.place =
    some ⟨[spBody (art I fF).af rC, 0x100000#64], LS.frames, some ⟨bC, 0⟩⟩ := by
  obtain ⟨l, e, hl, hlen⟩ := Clif.initState_placeB init_ok (pl := ⟨[0x100000#64], LS.frames, some ⟨bC, 0⟩⟩)
    rfl rfl
  have h := clifB_true
  simp only [clifB, Bool.and_eq_true, beq_iff_eq] at h
  have h2 := h.1.1.1.2
  rw [hl] at h2 ⊢
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
  obtain ⟨hs, hn⟩ := h2
  simp only [Clif.SlotInit.adv, Nat.zero_add] at hn
  have hl' : l = [spBody (art I fF).af rC] :=
    List.append_cancel_right (hs.trans (by simp : [spBody (art I fF).af rC, 0x100000#64] =
      [spBody (art I fF).af rC] ++ [0x100000#64]))
  subst hl' hn
  rfl

/-- The machine's own table (`iniB`) is `bC` on the run's entries `1`, `2`. -/
theorem iniB_agree : ∀ x, 0 < x → x ≤ 0 + 2 → (iniB I B M0 fF rC).bytes x = bC x := by
  intro x h0 h2
  rw [iniB_eq]
  show LO.std.tabB M0 fF sC 0 x = bC x
  rcases (show x = 1 ∨ x = 2 by omega) with rfl | rfl
  · rw [tab1]; rfl
  · rw [tab2]; rfl

/-- **The CLIF entry and run under the machine's own table** (`runWith_withTable`). -/
theorem run_init : ∃ v m,
    Clif.initState (prog I) "f" [v41] ((memB bC).withTable (iniB I B M0 fF rC).bytes) =
      .ok (csC.withTable (iniB I B M0 fF rC).bytes) ∧
    Clif.runLoop B.env (prog I) (M0 + 1) (csC.withTable (iniB I B M0 fF rC).bytes) = .returned [v] m ∧
    v.ty = .i64 ∧ v.bits.toNat = 82 := by
  obtain ⟨v, m, hr, hty, hv, hn⟩ := run_csC
  have hP : ∀ g ∈ (prog I).funcs, Clif.LinkFree g := hL.free
  have hk : Clif.EnvAdv B.env := fun _ _ h => by cases h
  obtain ⟨e, he⟩ := Clif.runLoop_placeB hP hk (M0 + 1) csC [v] m (Clif.initState_linv init_ok)
    (Clif.initState_placeB init_ok (pl := ⟨[0x100000#64], LS.frames, some ⟨bC, 0⟩⟩) rfl rfl) hr
  have he2 : e = 2 := by
    rw [he] at hn
    simp only [Option.map_some, Option.some.injEq, Clif.SlotInit.adv] at hn
    omega
  subst he2
  obtain ⟨hi, hr'⟩ := Clif.runWith_withTable (b := (iniB I B M0 fF rC).bytes) hP Clif.envTable_empty hk
    init_ok (pl := ⟨[0x100000#64], LS.frames, some ⟨bC, 0⟩⟩) rfl rfl hr he iniB_agree
  exact ⟨v, _, hi, hr', hty, hv⟩

/-- The entry state under the machine's own table. -/
noncomputable def csI : Clif.State := csC.withTable (iniB I B M0 fF rC).bytes

/-- **The reference CLIF run of the outside call**: `f`'s entry on `41`, placed at its body `sp`
with the machine's own slot table. -/
theorem clifRunB : ClifRunB I B M0 fF rC [v41] csI := by
  obtain ⟨v, m, hi, -, -, -⟩ := run_init
  have hpl := csC_place
  have hsl : csC.frame.slots = [] := by
    have h := clifB_true
    simp only [clifB, Bool.and_eq_true] at h
    exact List.isEmpty_iff.mp h.1.1.2
  refine ⟨clifEntry_initState (p := prog I) (by rw [fF_name]; exact hf) (by rw [fF_name]; exact hi),
    fun id b h => ?_, fun _ => ⟨[0x100000#64], ?_⟩⟩
  · change csC.frame.slots.lookup id = some b at h
    rw [hsl] at h
    cases h
  · change (csC.mem.withTable (iniB I B M0 fF rC).bytes).place = _
    simp only [Clif.Mem.withTable, hpl, Option.map_some]
    rfl

/-! ## The entry contract of the caller's state -/

/-- The caller's facts: `pc` at `f`, no error, the return address outside the code, `sp` the
16-aligned `0x100000` with `f`'s stack bound below it, the code at and above `0x1000000` (so above
the stack), `f`'s only parameter in `x0` holding `41`, `f`'s entry allocates nothing. -/
def entryB : Bool :=
  Arm.r .PC rC == (art I fF).base && (match Arm.r .ERR rC with | .None => true | _ => false) &&
  !imgD (xreg 30 rC) && spv rC == 0x100000#64 &&
  decide (DeadCleanupStackBound.stackFn I fF ≤ 0x100000) &&
  (tabOf I.resultsCleanup).all (fun e => (e.2.fb.program e.2.base).all fun p =>
    decide (0x1000000 ≤ p.1.toNat ∧ p.1.toNat + 4 ≤ 2 ^ 64)) &&
  (match locsOf fF.sig with
    | [.reg x] => (regVal rC x).setWidth v41.ty.width == v41.bits
    | _ => false) &&
  csC.mem.allocs.isEmpty

set_option maxRecDepth 100000 in
theorem entryB_true : entryB = true := by native_decide

/-- **The entry contract of the caller's state** (`OutsideCall`), each field from `entryB`: no
code below `sp` (the code lies at and above `0x1000000`); the CLIF memory has no allocation, so
its byte, image and validity clauses are vacuous; the symbols are the entry memory's. -/
theorem outsideCall : OutsideCall I (BinCheck.roByte I spec.data) fF
    (DeadCleanupStackBound.stackFn I fF) rC [v41] csI.mem := by
  have h := entryB_true
  simp only [entryB, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_true_eq,
    List.all_eq_true, List.isEmpty_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hpc, herr⟩, hra⟩, hsp⟩, hst⟩, hcode⟩, hargs⟩, hal⟩ := h
  have hv : ∀ a n, csI.mem.valid a n = false := fun a n => by
    show csC.mem.allocs.any _ = false
    rw [hal]; rfl
  refine ⟨hpc, ?_, fun hi => ?_, ?_, ?_, fun a ha hb => ?_, ?_, fun a b hva => ?_,
    fun a b b' hva => ?_, fun a n hva => ?_, ?_⟩
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
  · show csC.mem.symbols = _
    rw [(Clif.initState_symbols init_ok).1]
    rfl

/-! ## The executable theorem on the stale read -/

/-- **The executable returns `82` on a stale read** (`compileExe_correct_init`, module doc): the
run of the written `file` from `rC` refines the whole-program CLIF run from `f`'s entry placed
with the machine's own slot table, in which `r` loads the bytes `h` left in its slot; that run
returns `82` (with a zero table it returns `41`, `run_zero`). Left: the entry contract
`OutsideCall` and the oracle route's `InitOk`. -/
theorem stale_read_returns
    (ho : OutsideCall I (BinCheck.roByte I spec.data) fF (DeadCleanupStackBound.stackFn I fF) rC [v41]
      csI.mem)
    (hIO : InitOk (sysS I B fF rC (GotSlot I file)) (kapW I B fF rC)) :
    ∃ v cm, v.ty = .i64 ∧ v.bits.toNat = 82 ∧
      ExecRefines (art I fF).fb (art I fF).base (xreg 30 rC) (step I B file) rC
        (E2E.DeadCleanupBinCheck.RelocAt I) (.returned [v] cm) := by
  obtain ⟨v, m, -, hr, hty, hv⟩ := run_init
  exact ⟨v, m, hty, hv, compileExe_correct_init compile_eq B baseOk (hooksSim_closed _) hf hc M0
    intact ho clifRunB hIO hr⟩

/-- **The executable returns `82` on a stale read, entry contract discharged**
(`stale_read_returns` with `outsideCall`): the only premise left is the oracle route's `InitOk`. -/
theorem stale_read_returns_init
    (hIO : InitOk (sysS I B fF rC (GotSlot I file)) (kapW I B fF rC)) :
    ∃ v cm, v.ty = .i64 ∧ v.bits.toNat = 82 ∧
      ExecRefines (art I fF).fb (art I fF).base (xreg 30 rC) (step I B file) rC
        (E2E.DeadCleanupBinCheck.RelocAt I) (.returned [v] cm) :=
  stale_read_returns outsideCall hIO

end Link.DeadCleanup.InitSlotWitness
