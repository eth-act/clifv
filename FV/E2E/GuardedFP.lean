import FV.E2E.Guarded
import FV.Backend.Proof.MemRefines
import FV.Backend.Proof.RegallocMemFP

/-!
# The float accesses of the guarded semantics (S11e4, #238)

`csemGF`: the guarded semantics `csemG` extended by the scalar float loads and stores
(`fpuLoad`/`fpuStore` of an `s`/`d` register), which `csemG` leaves undefined (`GuardR` is
`False` there). A float access is defined when it has the form the float memory rules use
(`GuardFP`: an addressing mode with an address avoiding the frame `F`, every byte read
satisfying `Rd`); it is then `csem`, the Arm run of the canonical allocation
(`straight_fpuLoad`/`straight_fpuStore`, from `RegallocMemFP.execMInst_fpuLoad`/
`execMInst_fpuStore`), on a well-formed, error-free, aligned world, and its specification
`fspec` (as `mspec` for the integer accesses) elsewhere. Every other form is `csemG`'s.

`csemGF` satisfies the three premises of `MemRulesCorrectRT` (`refines_csemGF`,
`memRefinesR_csemGF`, `memRefinesFP_csemGF`): they are not vacuous.

**Bridge and lockstep (S11e5, Stage C slice 4).** `csem`'s specification fallback `mspec`
covers the float accesses as `fspec` states them (`fspec_mspec`), so `csem` itself refines them
(`csem_fpuLoad`/`csem_fpuStore`, `memRefinesFP_csem`), `csemGF` is a sub-semantics of `csem`
(`csemGF_sub`) extending `csemG` (`csemG_csemGF`), with `csemG`'s pinned call contracts
(`callsRefineP_csemGF`, `indCallsRefineP_csemGF`), and two `csemGF` runs of one instruction on
worlds that agree outside `Z` go in lockstep (`csemGF_lockstep2`, the float accesses' reads
guarded by `¬ Z`).
-/

namespace Backend.Proof

open Backend

/-- A canonical float load into `v0` through `amC`, from the world `w` with the uses placed. -/
theorem ss_fpuLoad {F : BitVec 64 → Prop} {ctx : FnCtx} {sz : ScalarSize} (hsz : FpSz sz)
    {i : MInst} {uses : List CV} {w : Arm.ArmState} {ops : Array Operand} {fl : Clif.MemFlags}
    {amC : AMode} (hops : i.operands = .ok ops)
    (hic : i.assign (canonRegs ops) = .ok (.fpuLoad sz (.v 0) amC fl))
    (hdv : ∀ s, defVals ops (canonRegs ops) s = [regVal s (.v 0)])
    (hmm : MemMode sz.bytes amC)
    (hsw : SameWorld F (placeUses ops (canonRegs ops) uses w) w)
    (herr : Arm.r .ERR w = .None) (hal : Arm.CheckSPAlignment w) {a : BitVec 64}
    (ha : amC.addr ctx sz.bytes (placeUses ops (canonRegs ops) uses w) = a)
    (hav : Avoids F sz.bytes a) :
    ∃ w', straightSem F ctx i uses w = some ([ldV sz a w], w', .next) ∧ SameWorld F w' w := by
  generalize ht : placeUses ops (canonRegs ops) uses w = t at hsw ha
  have hal' : Arm.CheckSPAlignment t :=
    align_of_spEq (sw_r_eq hsw (f := .GPR 31#5) (by simp [Masked])).symm hal
  obtain ⟨ls, o, hl, hS⟩ := execMInst_fpuLoad ctx env0 sz hsz (d := 0) (by omega) amC fl hmm t hal'
  have hex : execMInst ctx env0 (.fpuLoad sz (.v 0) amC fl) t = some (fldPost t
      (Arm.r .PC t + BitVec.ofNat 64 (4 * ls.length)) 0 (ldV sz (amC.addr ctx sz.bytes t) t) o) := by
    simp only [execMInst, hl]; exact hS.exec
  obtain ⟨-, -, f3, -⟩ := fldPost_facts t (Arm.r .PC t + BitVec.ofNat 64 (4 * ls.length)) (a := 0)
    (by omega) (ldV sz (amC.addr ctx sz.bytes t) t) o
  have hx := x16w_facts o t
  have herrt : Arm.r .ERR t = .None := by
    rw [← herr]; exact hsw.1 .ERR (by simp [Masked])
  refine ⟨fldPost t (Arm.r .PC t + BitVec.ofNat 64 (4 * ls.length)) 0
    (ldV sz (amC.addr ctx sz.bytes t) t) o, ?_, ?_⟩
  · rw [straightSem_of hops hic (by rw [ht]; intro p hp; simp [MInst.accesses] at hp; subst hp; rw [ha]; exact hav)
      (by rw [ht]; exact hex) ?_ ?_, hdv, f3, ha, ldV_congr sz hsw.2.1 hav]
    · simp only [fldPost]
      rw [Arm.r_of_w_different (by simp), Arm.r_of_w_different (by simp), hx.2.1, herrt]
    · simp only [fldPost]
      rw [Arm.w_program, Arm.w_program, hx.2.2.1, hsw.2.2]
  · simp only [fldPost]
    exact SameWorld.w_left (by simp [Masked]) (SameWorld.w_left (by simp [Masked])
      (sameWorld_x16w o none hsw))

/-- A canonical float store of `v0` through `amC`, from the world `w` with the uses placed. -/
theorem ss_fpuStore {F : BitVec 64 → Prop} {ctx : FnCtx} {sz : ScalarSize} (hsz : FpSz sz)
    {i : MInst} {uses : List CV} {w : Arm.ArmState} {ops : Array Operand} {fl : Clif.MemFlags}
    {amC : AMode} (hops : i.operands = .ok ops)
    (hic : i.assign (canonRegs ops) = .ok (.fpuStore sz (.v 0) amC fl))
    (hdv : ∀ s, defVals ops (canonRegs ops) s = [])
    (hmm : MemMode sz.bytes amC)
    (hsw : SameWorld F (placeUses ops (canonRegs ops) uses w) w) {v : CV}
    (hv0 : Arm.r (.SFP (BitVec.ofNat 5 0)) (placeUses ops (canonRegs ops) uses w) = v)
    (herr : Arm.r .ERR w = .None) (hal : Arm.CheckSPAlignment w) {a : BitVec 64}
    (ha : amC.addr ctx sz.bytes (placeUses ops (canonRegs ops) uses w) = a)
    (hav : Avoids F sz.bytes a) :
    ∃ w', straightSem F ctx i uses w = some ([], w', .next) ∧
      SameWorld F w' (Arm.write_mem_bytes sz.bytes a (v.setWidth (sz.bytes * 8)) w) := by
  generalize ht : placeUses ops (canonRegs ops) uses w = t at hsw ha hv0
  have hal' : Arm.CheckSPAlignment t :=
    align_of_spEq (sw_r_eq hsw (f := .GPR 31#5) (by simp [Masked])).symm hal
  obtain ⟨ls, o, hl, hS⟩ := execMInst_fpuStore ctx env0 sz hsz (d := 0) (by omega) amC fl hmm t hal'
  have hex := hS.exec
  have hx := x16w_facts o t
  have herrt : Arm.r .ERR t = .None := by
    rw [← herr]; exact hsw.1 .ERR (by simp [Masked])
  refine ⟨Arm.w .PC (Arm.r .PC t + BitVec.ofNat 64 (4 * ls.length))
    (Arm.write_mem_bytes sz.bytes (amC.addr ctx sz.bytes t)
      ((Arm.r (.SFP (BitVec.ofNat 5 0)) t).setWidth (sz.bytes * 8)) (x16w o t)), ?_, ?_⟩
  · rw [straightSem_of hops hic (by rw [ht]; intro p hp; simp [MInst.accesses] at hp; subst hp; rw [ha]; exact hav)
      (by rw [ht]; simp only [execMInst, hl]; exact hex) ?_ ?_, hdv]
    · rw [Arm.r_of_w_different (by simp), Arm.r_of_write_mem_bytes, hx.2.1, herrt]
    · rw [Arm.w_program, Arm.write_mem_bytes_program, hx.2.2.1, hsw.2.2]
  · rw [ha, hv0]
    exact SameWorld.w_left (by simp [Masked])
      (SameWorld.write_mem_bytes (sameWorld_x16w o none hsw) _ _ _)

theorem fpSz_bytes4 {sz : ScalarSize} (hsz : FpSz sz) :
    sz.bytes = 1 ∨ sz.bytes = 2 ∨ sz.bytes = 4 ∨ sz.bytes = 8 := by
  rcases fpSz_bytes hsz with h | h <;> simp [h]

variable (F : BitVec 64 → Prop) (ctx : FnCtx)

set_option maxHeartbeats 1000000 in
/-- A float load through a covered addressing mode, on the canonical run (`straightSem`). -/
theorem straight_fpuLoad (sz : ScalarSize) (hsz : FpSz sz) (d : Nat) (am : AMode)
    (fl : Clif.MemFlags) (uses : List CV) (w : Arm.ArmState) (a : BitVec 64)
    (ha : amodeAddr ctx.slotBase am sz.bytes uses w = some a) (hav : Avoids F sz.bytes a)
    (herr : Arm.r .ERR w = .None) (hal : Arm.CheckSPAlignment w) :
    ∃ w', straightSem F ctx (.fpuLoad sz (.vreg d .float) am fl) uses w =
      some ([ldV sz a w], w', .next) ∧ SameWorld F w' w := by
  have hb := fpSz_bytes4 hsz
  unfold amodeAddr at ha
  split at ha
  · cases ha
    exact ss_fpuLoad hsz (amC := .regReg (.x 1) (.x 2)) rfl rfl (by mr_fin)
      (mm_regReg 1 2 (by omega) (by omega)) (by mr_fin)
      herr hal (by mr_fin) hav
  · cases ha
    exact ss_fpuLoad hsz (amC := .regScaled (.x 1) (.x 2)) rfl rfl (by mr_fin)
      (mm_regScaled 1 2 (by omega) (by omega)) (by mr_fin)
      herr hal (by mr_fin) hav
  · split at ha
    · cases ha
      rename_i e _ _ he
      exact ss_fpuLoad hsz (amC := .regScaledExtended (.x 1) (.x 2) e) rfl rfl (by mr_fin)
        (mm_regScaledExtended (by rcases he with rfl | rfl <;> decide) 1 2 (by omega) (by omega))
        (by mr_fin) herr hal (by rcases he with rfl | rfl <;> mr_fin) hav
    · cases ha
  · split at ha
    · cases ha
      rename_i e _ _ he
      exact ss_fpuLoad hsz (amC := .regExtended (.x 1) (.x 2) e) rfl rfl (by mr_fin)
        (mm_regExtended (by rcases he with rfl | rfl <;> decide) 1 2 (by omega) (by omega))
        (by mr_fin) herr hal (by rcases he with rfl | rfl <;> mr_fin) hav
    · cases ha
  · split at ha
    · cases ha
      rename_i off _ ho
      exact ss_fpuLoad hsz (amC := .unscaled (.x 1) off) rfl rfl (by mr_fin)
        (mm_unscaled ho.1 (by omega) 1 (by omega)) (by mr_fin)
        herr hal (by mr_fin) hav
    · cases ha
  · split at ha
    · cases ha
      rename_i off _ ho
      exact ss_fpuLoad hsz (amC := .unsignedOffset (.x 1) off) rfl rfl (by mr_fin)
        (mm_uoff ho.1 (div_lt_of_bytes hb ho.2) 1 (by omega)) (by mr_fin)
        herr hal (by mr_fin) hav
    · cases ha
  · cases ha
    rename_i off
    exact ss_fpuLoad hsz (amC := .slotOffset off) rfl rfl (by mr_fin) trivial (by mr_fin)
      herr hal (by mr_fin) hav
  · cases ha
    rename_i off
    exact ss_fpuLoad hsz (amC := .spOffset off) rfl rfl (by mr_fin) trivial (by mr_fin)
      herr hal (by mr_fin) hav
  · cases ha
    rename_i off
    exact ss_fpuLoad hsz (amC := .fpOffset off) rfl rfl (by mr_fin) trivial (by mr_fin)
      herr hal (by mr_fin) hav
  · cases ha

set_option maxHeartbeats 1000000 in
/-- A float store through a covered addressing mode, on the canonical run (`straightSem`). -/
theorem straight_fpuStore (sz : ScalarSize) (hsz : FpSz sz) (d : Nat) (am : AMode)
    (fl : Clif.MemFlags) (v : CV) (uses : List CV) (w : Arm.ArmState) (a : BitVec 64)
    (ha : amodeAddr ctx.slotBase am sz.bytes uses w = some a) (hav : Avoids F sz.bytes a)
    (herr : Arm.r .ERR w = .None) (hal : Arm.CheckSPAlignment w) :
    ∃ w', straightSem F ctx (.fpuStore sz (.vreg d .float) am fl) (v :: uses) w = some ([], w', .next) ∧
      SameWorld F w' (Arm.write_mem_bytes sz.bytes a (v.setWidth (sz.bytes * 8)) w) := by
  have hb := fpSz_bytes4 hsz
  unfold amodeAddr at ha
  split at ha
  · cases ha
    exact ss_fpuStore hsz (amC := .regReg (.x 1) (.x 2)) rfl rfl (by mr_fin)
      (mm_regReg 1 2 (by omega) (by omega)) (by mr_fin)
      (by mr_fin) herr hal (by mr_fin) hav
  · cases ha
    exact ss_fpuStore hsz (amC := .regScaled (.x 1) (.x 2)) rfl rfl (by mr_fin)
      (mm_regScaled 1 2 (by omega) (by omega)) (by mr_fin)
      (by mr_fin) herr hal (by mr_fin) hav
  · split at ha
    · cases ha
      rename_i e _ _ he
      exact ss_fpuStore hsz (amC := .regScaledExtended (.x 1) (.x 2) e) rfl rfl (by mr_fin)
        (mm_regScaledExtended (by rcases he with rfl | rfl <;> decide) 1 2 (by omega) (by omega))
        (by mr_fin) (by mr_fin) herr hal (by rcases he with rfl | rfl <;> mr_fin) hav
    · cases ha
  · split at ha
    · cases ha
      rename_i e _ _ he
      exact ss_fpuStore hsz (amC := .regExtended (.x 1) (.x 2) e) rfl rfl (by mr_fin)
        (mm_regExtended (by rcases he with rfl | rfl <;> decide) 1 2 (by omega) (by omega))
        (by mr_fin) (by mr_fin) herr hal (by rcases he with rfl | rfl <;> mr_fin) hav
    · cases ha
  · split at ha
    · cases ha
      rename_i off _ ho
      exact ss_fpuStore hsz (amC := .unscaled (.x 1) off) rfl rfl (by mr_fin)
        (mm_unscaled ho.1 (by omega) 1 (by omega)) (by mr_fin)
        (by mr_fin) herr hal (by mr_fin) hav
    · cases ha
  · split at ha
    · cases ha
      rename_i off _ ho
      exact ss_fpuStore hsz (amC := .unsignedOffset (.x 1) off) rfl rfl (by mr_fin)
        (mm_uoff ho.1 (div_lt_of_bytes hb ho.2) 1 (by omega))
        (by mr_fin) (by mr_fin) herr hal (by mr_fin) hav
    · cases ha
  · cases ha
    rename_i off
    exact ss_fpuStore hsz (amC := .slotOffset off) rfl rfl (by mr_fin) trivial (by mr_fin) (by mr_fin)
      herr hal (by mr_fin) hav
  · cases ha
    rename_i off
    exact ss_fpuStore hsz (amC := .spOffset off) rfl rfl (by mr_fin) trivial (by mr_fin) (by mr_fin)
      herr hal (by mr_fin) hav
  · cases ha
    rename_i off
    exact ss_fpuStore hsz (amC := .fpOffset off) rfl rfl (by mr_fin) trivial (by mr_fin) (by mr_fin)
      herr hal (by mr_fin) hav
  · cases ha

end Backend.Proof

namespace E2E
open Backend Backend.Proof

/-- The specification of the scalar float accesses (`MemRefinesFP`'s results): `csemGF`'s
fallback for them, as `mspec` is `csem`'s for the integer accesses. -/
def fspec (sb : Nat) : Sem := fun i uses w =>
  match i, uses with
  | .fpuLoad sz (.vreg _ .float) am _, us =>
    if sz = .size32 ∨ sz = .size64 then
      (amodeAddr sb am sz.bytes us w).map fun a =>
        ([(Arm.read_mem_bytes sz.bytes a w).setWidth 128], w, .next)
    else none
  | .fpuStore sz (.vreg _ .float) am _, v :: us =>
    if sz = .size32 ∨ sz = .size64 then
      (amodeAddr sb am sz.bytes us w).map fun a =>
        ([], Arm.write_mem_bytes sz.bytes a (v.setWidth (sz.bytes * 8)) w, .next)
    else none
  | _, _ => none

/-- The guard of the float accesses of `csemGF`: the forms the float memory rules use (an
addressing mode with an address, avoiding the frame `F`), every byte read satisfying `Rd`. -/
def GuardFP (F Rd : BitVec 64 → Prop) (sb : Nat) : MInst → List CV → Arm.ArmState → Prop
  | .fpuLoad sz (.vreg _ .float) am _, us, w => (sz = .size32 ∨ sz = .size64) ∧
      ∃ a, amodeAddr sb am sz.bytes us w = some a ∧ Avoids F sz.bytes a ∧
        ∀ k < sz.bytes, Rd (a + BitVec.ofNat 64 k)
  | .fpuStore sz (.vreg _ .float) am _, _ :: us, w => (sz = .size32 ∨ sz = .size64) ∧
      ∃ a, amodeAddr sb am sz.bytes us w = some a ∧ Avoids F sz.bytes a
  | _, _, _ => False

open Classical in
/-- **The guarded semantics with the scalar float accesses**: a guarded (`GuardFP`) float load
or store is `csem` on a well-formed, error-free, aligned world and `fspec` elsewhere; an
unguarded one is undefined; every other form is `csemG`'s. -/
noncomputable def csemGF (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) (Rd : BitVec 64 → Prop)
    (syms : String → Option Nat) (exts : List Clif.ExtFunc) (sigs : List Clif.Signature)
    (sp0 : BitVec 64) (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop) :
    Sem := fun i us w =>
  match i with
  | .fpuLoad .. | .fpuStore .. =>
    if GuardFP F Rd ctx.slotBase i us w then
      if csemWF ctx i us = true ∧ Arm.r .ERR w = .None ∧ Arm.CheckSPAlignment w then
        csem F ctx X i us w
      else fspec ctx.slotBase i us w
    else none
  | _ => csemG F ctx X Rd syms exts sigs sp0 Pc i us w

variable {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {Rd : BitVec 64 → Prop}
  {syms : String → Option Nat} {exts : List Clif.ExtFunc} {sigs : List Clif.Signature}
  {sp0 : BitVec 64}
  {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop}

/-- **`csemGF` refines the instruction specification** (`Refines`; `ispec` leaves the float
accesses undefined). -/
theorem refines_csemGF : Refines F (csemGF F ctx X Rd syms exts sigs sp0 Pc) := by
  intro i us w outs w' ctl h
  have hG := refines_csemG (F := F) (ctx := ctx) (X := X) (Rd := Rd) (syms := syms) (exts := exts)
    (sigs := sigs) (sp0 := sp0) (Pc := Pc) i us w outs w' h
  cases i
  case fpuLoad => simp [ispec] at h
  case fpuStore => simp [ispec] at h
  all_goals exact hG

/-- **`csemGF` refines the integer memory forms with guarded reads** (`MemRefinesR Rd`): there
it is `csemG`. -/
theorem memRefinesR_csemGF {sb : Nat} (hsb : ctx.slotBase = sb)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b) :
    MemRefinesR Rd F sb syms (csemGF F ctx X Rd syms exts sigs sp0 Pc) :=
  memRefinesR_csemG (exts := exts) (sigs := sigs) (sp0 := sp0) (Pc := Pc) hsb hsym

/-- **`csemGF` refines the scalar float accesses with guarded reads** (`MemRefinesFP Rd`): the
Arm run of `ldr`/`str` of an `s`/`d` register (`straight_fpuLoad`/`straight_fpuStore`). -/
theorem memRefinesFP_csemGF {sb : Nat} (hsb : ctx.slotBase = sb) :
    MemRefinesFP Rd F sb (csemGF F ctx X Rd syms exts sigs sp0 Pc) := by
  subst hsb
  refine ⟨?_, ?_⟩
  · intro sz d am fl uses w a hsz ha hav hrd
    have hg : GuardFP F Rd ctx.slotBase (.fpuLoad sz (.vreg d .float) am fl) uses w :=
      ⟨hsz, a, ha, hav, hrd⟩
    simp only [csemGF, if_pos hg]
    split
    · rename_i hc
      rw [csem_straight rfl, if_pos hc]
      exact straight_fpuLoad F ctx sz hsz d am fl uses w a ha hav hc.2.1 hc.2.2
    · exact ⟨w, by simp [fspec, hsz, ha], SameWorld.refl F w⟩
  · intro sz d am fl v uses w a hsz ha hav
    have hg : GuardFP F Rd ctx.slotBase (.fpuStore sz (.vreg d .float) am fl) (v :: uses) w :=
      ⟨hsz, a, ha, hav⟩
    simp only [csemGF, if_pos hg]
    split
    · rename_i hc
      rw [csem_straight rfl, if_pos hc]
      exact straight_fpuStore F ctx sz hsz d am fl v uses w a ha hav hc.2.1 hc.2.2
    · exact ⟨_, by simp [fspec, hsz, ha], SameWorld.refl F _⟩


/-! ## The float accesses of `csem` (S11e5, Stage C slice 4) -/

/-- `csem`'s specification fallback states the float accesses as `fspec` does. -/
theorem fspec_mspec {sb : Nat} {i : MInst} {us : List CV} {w : Arm.ArmState}
    {r : List CV × Arm.ArmState × Ctl} (h : fspec sb i us w = some r) : mspec sb i us w = some r := by
  unfold fspec at h
  split at h
  · rw [mspec_fpuLoad_ne sb ?_]
    · exact h
    · intro v e; subst e; simp [amodeAddr] at h
  · exact h
  · cases h

/-- Where `GuardFP` holds, `fspec` is `mspec`. -/
theorem fspec_eq_mspec {sb : Nat} {i : MInst} {us : List CV} {w : Arm.ArmState}
    (hg : GuardFP F Rd sb i us w) : fspec sb i us w = mspec sb i us w := by
  unfold GuardFP at hg
  split at hg
  · rw [mspec_fpuLoad_ne sb ?_]
    · rfl
    · intro v e; subst e; obtain ⟨-, a, ha, -⟩ := hg; simp [amodeAddr] at ha
  · rfl
  · exact hg.elim

/-- **A float load of `csem`** through an addressing mode whose access avoids `F` (any world). -/
theorem csem_fpuLoad (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) (sz : ScalarSize)
    (hsz : sz = .size32 ∨ sz = .size64) (d : Nat) (am : AMode) (fl : Clif.MemFlags) (us : List CV)
    (w : Arm.ArmState) (a : BitVec 64) (ha : amodeAddr ctx.slotBase am sz.bytes us w = some a)
    (hav : Avoids F sz.bytes a) :
    ∃ w', csem F ctx X (.fpuLoad sz (.vreg d .float) am fl) us w =
      some ([(Arm.read_mem_bytes sz.bytes a w).setWidth 128], w', .next) ∧ SameWorld F w' w := by
  rw [csem_straight rfl]
  split
  · rename_i hc
    exact straight_fpuLoad F ctx sz hsz d am fl us w a ha hav hc.2.1 hc.2.2
  · refine ⟨w, ?_, SameWorld.refl F w⟩
    rw [mspec_fpuLoad_ne (am := am) _ (fun v e => by subst e; simp [amodeAddr] at ha)]
    simp [hsz, ha]

/-- **A float store of `csem`** through an addressing mode whose access avoids `F` (any world). -/
theorem csem_fpuStore (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) (sz : ScalarSize)
    (hsz : sz = .size32 ∨ sz = .size64) (d : Nat) (am : AMode) (fl : Clif.MemFlags) (v : CV)
    (us : List CV) (w : Arm.ArmState) (a : BitVec 64)
    (ha : amodeAddr ctx.slotBase am sz.bytes us w = some a) (hav : Avoids F sz.bytes a) :
    ∃ w', csem F ctx X (.fpuStore sz (.vreg d .float) am fl) (v :: us) w = some ([], w', .next) ∧
      SameWorld F w' (Arm.write_mem_bytes sz.bytes a (v.setWidth (sz.bytes * 8)) w) := by
  rw [csem_straight rfl]
  split
  · rename_i hc
    exact straight_fpuStore F ctx sz hsz d am fl v us w a ha hav hc.2.1 hc.2.2
  · exact ⟨_, by simp [mspec, hsz, ha], SameWorld.refl F _⟩

/-- **`csem` refines the scalar float accesses** (`MemRefinesFP`, for every read guard `Rd`). -/
theorem memRefinesFP_csem (Rd F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) {sb : Nat}
    (hsb : ctx.slotBase = sb) : MemRefinesFP Rd F sb (csem F ctx X) := by
  subst hsb
  exact ⟨fun sz d am fl us w a hsz ha hav _ => csem_fpuLoad F ctx X sz hsz d am fl us w a ha hav,
    fun sz d am fl v us w a hsz ha hav => csem_fpuStore F ctx X sz hsz d am fl v us w a ha hav⟩

/-! ## `csemGF` against `csem` and `csemG` -/

open Classical in
/-- On a float access, `csemGF` is `csem` where `GuardFP` holds, undefined elsewhere. -/
theorem csemGF_fp {i : MInst}
    (hfp : (∃ sz rd am fl, i = .fpuLoad sz rd am fl) ∨ ∃ sz rd am fl, i = .fpuStore sz rd am fl)
    (us : List CV) (w : Arm.ArmState) :
    csemGF F ctx X Rd syms exts sigs sp0 Pc i us w =
      if GuardFP F Rd ctx.slotBase i us w then csem F ctx X i us w else none := by
  rcases hfp with ⟨sz, rd, am, fl, rfl⟩ | ⟨sz, rd, am, fl, rfl⟩ <;>
  · simp only [csemGF]
    split
    · rename_i hg
      rw [csem_straight rfl]
      split
      · rfl
      · exact fspec_eq_mspec hg
    · rfl

/-- Off the float accesses, `csemGF` is `csemG`. -/
theorem csemGF_other {i : MInst} (h1 : ∀ sz rd am fl, i ≠ .fpuLoad sz rd am fl)
    (h2 : ∀ sz rd am fl, i ≠ .fpuStore sz rd am fl) (us : List CV) (w : Arm.ArmState) :
    csemGF F ctx X Rd syms exts sigs sp0 Pc i us w = csemG F ctx X Rd syms exts sigs sp0 Pc i us w := by
  cases i <;> first | rfl | exact absurd rfl (h1 _ _ _ _) | exact absurd rfl (h2 _ _ _ _)

/-- **`csemGF` is a sub-semantics of `csem`**: where it is defined, it is `csem`. -/
theorem csemGF_sub {i : MInst} {us : List CV} {w : Arm.ArmState} {r : List CV × Arm.ArmState × Ctl}
    (h : csemGF F ctx X Rd syms exts sigs sp0 Pc i us w = some r) : csem F ctx X i us w = some r := by
  by_cases hfp : (∃ sz rd am fl, i = .fpuLoad sz rd am fl) ∨ ∃ sz rd am fl, i = .fpuStore sz rd am fl
  · rw [csemGF_fp hfp] at h
    split at h
    · exact h
    · cases h
  · rw [csemGF_other (fun sz rd am fl e => hfp (.inl ⟨sz, rd, am, fl, e⟩))
      (fun sz rd am fl e => hfp (.inr ⟨sz, rd, am, fl, e⟩))] at h
    exact (csemG_sub h).2.2

/-- **`csemGF` extends `csemG`**: where `csemG` is defined, `csemGF` is too, with its result. -/
theorem csemG_csemGF {i : MInst} {us : List CV} {w : Arm.ArmState} {r : List CV × Arm.ArmState × Ctl}
    (h : csemG F ctx X Rd syms exts sigs sp0 Pc i us w = some r) :
    csemGF F ctx X Rd syms exts sigs sp0 Pc i us w = some r := by
  by_cases hfp : (∃ sz rd am fl, i = .fpuLoad sz rd am fl) ∨ ∃ sz rd am fl, i = .fpuStore sz rd am fl
  · obtain ⟨hg, -, -⟩ := csemG_sub h
    rcases hfp with ⟨sz, rd, am, fl, rfl⟩ | ⟨sz, rd, am, fl, rfl⟩ <;>
      simp [GuardR] at hg
  · rw [csemGF_other (fun sz rd am fl e => hfp (.inl ⟨sz, rd, am, fl, e⟩))
      (fun sz rd am fl e => hfp (.inr ⟨sz, rd, am, fl, e⟩))]
    exact h

/-- **The pinned callee contract for `csemGF`** (its calls are `csemG`'s). -/
theorem callsRefineP_csemGF {env : Clif.Env} {MR : MemRelT}
    (hX : XCallsOk env exts MR X) (hMRm : ∀ sl cm w, MR sl cm w → MemRel F syms cm w)
    (hMRc : ∀ sl cm w, MR sl cm w → spv w = sp0) :
    CallsRefineP Pc F env exts MR (csemGF F ctx X Rd syms exts sigs sp0 Pc) := by
  obtain ⟨sym, h1, h2, h3⟩ := callsRefineP_csemG (ctx := ctx) (Rd := Rd) (sigs := sigs) (Pc := Pc)
    hX hMRm hMRc
  exact ⟨sym, h1, h2, h3⟩

/-- **The pinned indirect-call contract for `csemGF`.** -/
theorem indCallsRefineP_csemGF {env : Clif.Env} {MR : MemRelT}
    (hX : XCallsIndOk env sigs MR X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hMRm : ∀ sl cm w, MR sl cm w → MemRel F syms cm w)
    (hMRc : ∀ sl cm w, MR sl cm w → spv w = sp0) :
    IndCallsRefineP Pc env sigs MR (csemGF F ctx X Rd syms exts sigs sp0 Pc) := by
  obtain ⟨h1, h2⟩ := indCallsRefineP_csemG (ctx := ctx) (Rd := Rd) (exts := exts) (Pc := Pc)
    hX hsym hMRm hMRc
  exact ⟨h1, h2⟩

/-! ## Two `csemGF` runs in lockstep -/

theorem guardFP_fpuLoad {sb : Nat} {sz : ScalarSize} {rd : Reg} {am : AMode} {fl : Clif.MemFlags}
    {us : List CV} {w : Arm.ArmState} (h : GuardFP F Rd sb (.fpuLoad sz rd am fl) us w) :
    ∃ d, rd = .vreg d .float ∧ (sz = .size32 ∨ sz = .size64) ∧
      ∃ a, amodeAddr sb am sz.bytes us w = some a ∧ Avoids F sz.bytes a ∧
        ∀ k < sz.bytes, Rd (a + BitVec.ofNat 64 k) := by
  rcases rd with ⟨d, _ | _⟩ | _ | _ | _ | _
  all_goals first | exact ⟨_, rfl, h⟩ | (simp [GuardFP] at h)

theorem guardFP_fpuStore {sb : Nat} {sz : ScalarSize} {rd : Reg} {am : AMode} {fl : Clif.MemFlags}
    {us : List CV} {w : Arm.ArmState} (h : GuardFP F Rd sb (.fpuStore sz rd am fl) us w) :
    ∃ d v us', rd = .vreg d .float ∧ us = v :: us' ∧ (sz = .size32 ∨ sz = .size64) ∧
      ∃ a, amodeAddr sb am sz.bytes us' w = some a ∧ Avoids F sz.bytes a := by
  rcases us with _ | ⟨v, us'⟩
  · rcases rd with ⟨d, _ | _⟩ | _ | _ | _ | _ <;> simp [GuardFP] at h
  · rcases rd with ⟨d, _ | _⟩ | _ | _ | _ | _
    all_goals first | exact ⟨_, _, _, rfl, rfl, h⟩ | (simp [GuardFP] at h)

/-- **Two guarded runs of one instruction with the float accesses, in lockstep**
(`csemG_lockstep2` for `csemGF`): where `csemGF` with the reads guarded by `¬ Z` runs an
instruction on two worlds that agree outside `Z ⊇ F`, with callees (`hX`) and the TLSDESC
resolver (`hT`) that keep the agreement: the same outputs and control, worlds that agree outside
`Z`. A float load reads the same bytes on both worlds (outside `Z`); a float store writes the
same value at the same address (registers `sp`/`x29` agree). -/
theorem csemGF_lockstep2 {Z : BitVec 64 → Prop} (hFZ : ∀ a, F a → Z a) {i : MInst} {us : List CV}
    {w w' : Arm.ArmState} (hw : SameWorld Z w w')
    (hX : ∀ dest, CallG F syms X exts sigs sp0 Pc dest us w → CallG F syms X exts sigs sp0 Pc dest us w' →
      ∀ o x o' x', X.call (destName dest) us w = some (o, x) →
        X.call (destName dest) us w' = some (o', x') → o = o' ∧ SameWorld Z x x')
    (hT : ∀ n, X.tlsFlags n w = X.tlsFlags n w')
    {o o' : List CV} {w₁ w₁' : Arm.ArmState} {c c' : Ctl}
    (h : csemGF F ctx X (fun b => ¬ Z b) syms exts sigs sp0 Pc i us w = some (o, w₁, c))
    (h' : csemGF F ctx X (fun b => ¬ Z b) syms exts sigs sp0 Pc i us w' = some (o', w₁', c')) :
    o = o' ∧ c = c' ∧ SameWorld Z w₁ w₁' := by
  by_cases hfp : (∃ sz rd am fl, i = .fpuLoad sz rd am fl) ∨ ∃ sz rd am fl, i = .fpuStore sz rd am fl
  · rw [csemGF_fp hfp] at h h'
    split at h
    · rename_i hg
      split at h'
      · rcases hfp with ⟨sz, rd, am, fl, rfl⟩ | ⟨sz, rd, am, fl, rfl⟩
        · obtain ⟨d, rfl, hsz, a, ha, hF, hrd⟩ := guardFP_fpuLoad hg
          obtain ⟨w₂, h2, hs2⟩ := csem_fpuLoad F ctx X sz hsz d am fl us w a ha hF
          obtain ⟨w₂', h2', hs2'⟩ := csem_fpuLoad F ctx X sz hsz d am fl us w' a
            (by rw [← amodeAddr_sameWorld hw]; exact ha) hF
          rw [h2] at h
          rw [h2'] at h'
          simp only [Option.some.injEq, Prod.mk.injEq] at h h'
          obtain ⟨rfl, rfl, rfl⟩ := h
          obtain ⟨rfl, rfl, rfl⟩ := h'
          refine ⟨by rw [read_mem_bytes_sameWorld hw (fun k hk hz => hrd k hk hz)], rfl, ?_⟩
          exact SameWorld.trans (SameWorld.mono hFZ hs2) (hw.trans (SameWorld.mono hFZ hs2').symm)
        · obtain ⟨d, v, us', rfl, rfl, hsz, a, ha, hF⟩ := guardFP_fpuStore hg
          obtain ⟨w₂, h2, hs2⟩ := csem_fpuStore F ctx X sz hsz d am fl v us' w a ha hF
          obtain ⟨w₂', h2', hs2'⟩ := csem_fpuStore F ctx X sz hsz d am fl v us' w' a
            (by rw [← amodeAddr_sameWorld hw]; exact ha) hF
          rw [h2] at h
          rw [h2'] at h'
          simp only [Option.some.injEq, Prod.mk.injEq] at h h'
          obtain ⟨rfl, rfl, rfl⟩ := h
          obtain ⟨rfl, rfl, rfl⟩ := h'
          refine ⟨rfl, rfl, ?_⟩
          exact SameWorld.trans (SameWorld.mono hFZ hs2)
            ((SameWorld.write_mem_bytes hw _ _ _).trans (SameWorld.mono hFZ hs2').symm)
      · cases h'
    · cases h
  · have e := csemGF_other (F := F) (ctx := ctx) (X := X) (Rd := fun b => ¬ Z b) (syms := syms)
      (exts := exts) (sigs := sigs) (sp0 := sp0) (Pc := Pc)
      (fun sz rd am fl e => hfp (.inl ⟨sz, rd, am, fl, e⟩))
      (fun sz rd am fl e => hfp (.inr ⟨sz, rd, am, fl, e⟩))
    rw [e] at h
    rw [e] at h'
    exact csemG_lockstep2 hFZ hw hX hT h h'

end E2E
