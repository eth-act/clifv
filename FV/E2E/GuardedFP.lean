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
`memRefinesR_csemGF`, `memRefinesFP_csemGF`): they are not vacuous. Wiring `csemGF` into the
lockstep and the end-to-end theorem (the float accesses of two runs agree outside `Z`) is part
of the float end-to-end work (S11e5+), not of this file.
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

end E2E
