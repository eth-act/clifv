import FV.Backend.Proof.RefinesInsts
import FV.Backend.Proof.RegallocCover

/-!
# `MemRefines` for `csem` (M6 proof)

`memRefines_csem`: M6's concrete instruction semantics `csem F ctx X` satisfies M4's memory
obligation `MemRefines F sb syms` when the slot region is at `ctx.slotBase = sb` and the external
semantics' symbol addresses agree with the linked symbols `syms`. A load/store/slot address on a
world with an error or a misaligned `sp` (or an ill-formed use list) is `csem`'s fallback
`mspec`, which states exactly `MemRefines`' result; otherwise it is `straightSem`, the Arm run of
the canonical allocation (`ss_load`/`ss_store`, from `execMInst_load`/`execMInst_store`, and
`execMInst_loadAddr_slot'`), computed per addressing mode of `amodeAddr`. A GOT load is
`X.sym n 0`.
-/

namespace Backend.Proof

open Backend

theorem ldX_loadVal (op : LoadOp) (hop : op ≠ .fpuLoad128) (a : BitVec 64) (w : Arm.ArmState) :
    ldX op a w = loadVal op a w := by
  cases op <;> simp_all [ldX, loadVal, loadSigned, LoadOp.bytes]

/-- `straightSem` of an instruction whose canonical run is known. -/
theorem straightSem_of {F : BitVec 64 → Prop} {ctx : FnCtx} {i : MInst} {uses : List CV}
    {w : Arm.ArmState} {ops : Array Operand} {ic : MInst} {t' : Arm.ArmState}
    (hops : i.operands = .ok ops) (hic : i.assign (canonRegs ops) = .ok ic)
    (hacc : AccessOk F ctx ic (placeUses ops (canonRegs ops) uses w))
    (hex : execMInst ctx env0 ic (placeUses ops (canonRegs ops) uses w) = some t')
    (herr : Arm.r .ERR t' = .None) (hprog : t'.program = w.program) :
    straightSem F ctx i uses w = some (defVals ops (canonRegs ops) t', t', .next) := by
  simp [straightSem, hops, hic, hacc, hex, herr, hprog]

/-- A canonical load into `x0` through `amC`, from the world `w` with the uses placed. -/
theorem ss_load {F : BitVec 64 → Prop} {ctx : FnCtx} {op : LoadOp} (hop : op ≠ .fpuLoad128)
    {i : MInst} {uses : List CV} {w : Arm.ArmState} {ops : Array Operand} {fl : Clif.MemFlags}
    {amC : AMode} (hops : i.operands = .ok ops)
    (hic : i.assign (canonRegs ops) = .ok (.load op (.x 0) amC fl))
    (hdv : ∀ s, defVals ops (canonRegs ops) s = [regVal s (.x 0)])
    (hmm : MemMode op.bytes amC)
    (hsw : SameWorld F (placeUses ops (canonRegs ops) uses w) w)
    (herr : Arm.r .ERR w = .None) (hal : Arm.CheckSPAlignment w) {a : BitVec 64}
    (ha : amC.addr ctx op.bytes (placeUses ops (canonRegs ops) uses w) = a)
    (hav : Avoids F op.bytes a) :
    ∃ w', straightSem F ctx i uses w = some ([ofX (loadVal op a w)], w', .next) ∧
      SameWorld F w' w := by
  generalize ht : placeUses ops (canonRegs ops) uses w = t at hsw ha
  have hal' : Arm.CheckSPAlignment t :=
    align_of_spEq (sw_r_eq hsw (f := .GPR 31#5) (by simp [Masked])).symm hal
  obtain ⟨ls, o, hl, hS⟩ := execMInst_load ctx env0 op hop (d := 0) (by omega) amC fl hmm t hal'
  have hex : execMInst ctx env0 (.load op (.x 0) amC fl) t = some (ldPost t
      (Arm.r .PC t + BitVec.ofNat 64 (4 * ls.length)) 0 (ldX op (amC.addr ctx op.bytes t) t) o) := by
    simp only [execMInst, hl]; exact hS.exec
  obtain ⟨-, -, f3, -⟩ := ldPost_facts t (Arm.r .PC t + BitVec.ofNat 64 (4 * ls.length)) (a := 0)
    (by omega) (ldX op (amC.addr ctx op.bytes t) t) o
  have hx := x16w_facts o t
  have herrt : Arm.r .ERR t = .None := by
    rw [← herr]; exact hsw.1 .ERR (by simp [Masked])
  refine ⟨ldPost t (Arm.r .PC t + BitVec.ofNat 64 (4 * ls.length)) 0
    (ldX op (amC.addr ctx op.bytes t) t) o, ?_, ?_⟩
  · rw [straightSem_of hops hic (by rw [ht]; intro p hp; simp [MInst.accesses] at hp; subst hp; rw [ha]; exact hav)
      (by rw [ht]; exact hex) ?_ ?_, hdv, f3, ha, ldX_congr op hsw.2.1 hav, ldX_loadVal op hop]
    · rfl
    · simp only [ldPost]
      rw [Arm.r_of_w_different (by simp), Arm.r_of_w_different (by simp), hx.2.1, herrt]
    · simp only [ldPost]
      rw [Arm.w_program, Arm.w_program, hx.2.2.1, hsw.2.2]
  · simp only [ldPost]
    exact SameWorld.w_left (by simp [Masked]) (SameWorld.w_left (by simp [Masked])
      (sameWorld_x16w o none hsw))

/-- A canonical store of `x0` through `amC`, from the world `w` with the uses placed. -/
theorem ss_store {F : BitVec 64 → Prop} {ctx : FnCtx} {op : StoreOp} (hop : op ≠ .fpuStore128)
    {i : MInst} {uses : List CV} {w : Arm.ArmState} {ops : Array Operand} {fl : Clif.MemFlags}
    {amC : AMode} (hops : i.operands = .ok ops)
    (hic : i.assign (canonRegs ops) = .ok (.store op (.x 0) amC fl))
    (hdv : ∀ s, defVals ops (canonRegs ops) s = [])
    (hmm : MemMode op.bytes amC)
    (hsw : SameWorld F (placeUses ops (canonRegs ops) uses w) w) {v : CV}
    (hx0 : Arm.r (.GPR (BitVec.ofNat 5 0)) (placeUses ops (canonRegs ops) uses w) = lo64 v)
    (herr : Arm.r .ERR w = .None) (hal : Arm.CheckSPAlignment w) {a : BitVec 64}
    (ha : amC.addr ctx op.bytes (placeUses ops (canonRegs ops) uses w) = a)
    (hav : Avoids F op.bytes a) :
    ∃ w', straightSem F ctx i uses w = some ([], w', .next) ∧
      SameWorld F w' (Arm.write_mem_bytes op.bytes a ((lo64 v).setWidth (op.bytes * 8)) w) := by
  generalize ht : placeUses ops (canonRegs ops) uses w = t at hsw ha hx0
  have hal' : Arm.CheckSPAlignment t :=
    align_of_spEq (sw_r_eq hsw (f := .GPR 31#5) (by simp [Masked])).symm hal
  obtain ⟨ls, o, hl, hS⟩ := execMInst_store ctx env0 op hop (d := 0) (by omega) (by omega) amC fl
    hmm t hal'
  have hex := hS.exec
  have hx := x16w_facts o t
  have herrt : Arm.r .ERR t = .None := by
    rw [← herr]; exact hsw.1 .ERR (by simp [Masked])
  refine ⟨Arm.w .PC (Arm.r .PC t + BitVec.ofNat 64 (4 * ls.length))
    (Arm.write_mem_bytes op.bytes (amC.addr ctx op.bytes t)
      ((Arm.r (.GPR (BitVec.ofNat 5 0)) t).setWidth (op.bytes * 8)) (x16w o t)), ?_, ?_⟩
  · rw [straightSem_of hops hic (by rw [ht]; intro p hp; simp [MInst.accesses] at hp; subst hp; rw [ha]; exact hav)
      (by rw [ht]; simp only [execMInst, hl]; exact hex) ?_ ?_, hdv]
    · rw [Arm.r_of_w_different (by simp), Arm.r_of_write_mem_bytes, hx.2.1, herrt]
    · rw [Arm.w_program, Arm.write_mem_bytes_program, hx.2.2.1, hsw.2.2]
  · rw [ha, hx0]
    exact SameWorld.w_left (by simp [Masked])
      (SameWorld.write_mem_bytes (sameWorld_x16w o none hsw) _ _ _)


theorem ext_uxtw (x : BitVec 64) {k : Nat} (hk : k ≤ 32) :
    Arm.extend_reg x (Arm.decode_reg_extend ExtendOp.uxtw.bits) k = ((x.setWidth 32).setWidth 64) <<< k := by
  have h : min 32 (64 - k) = 32 := Nat.min_eq_left (by omega)
  simp only [Arm.extend_reg, Arm.ExtendType.unsigned_len, dre_uxtw]
  rw [h]
  simp [ext0]

theorem ext_sxtw (x : BitVec 64) {k : Nat} (hk : k ≤ 32) :
    Arm.extend_reg x (Arm.decode_reg_extend ExtendOp.sxtw.bits) k = ((x.setWidth 32).signExtend 64) <<< k := by
  have h : min 32 (64 - k) = 32 := Nat.min_eq_left (by omega)
  simp only [Arm.extend_reg, Arm.ExtendType.unsigned_len, dre_sxtw]
  rw [h]
  simp [ext0]

theorem log2_le_of_bytes {b : Nat} (hb : b = 1 ∨ b = 2 ∨ b = 4 ∨ b = 8) : log2 b ≤ 32 := by
  rcases hb with rfl | rfl | rfl | rfl <;> decide

theorem loadOp_bytes (op : LoadOp) (hop : op ≠ .fpuLoad128) :
    op.bytes = 1 ∨ op.bytes = 2 ∨ op.bytes = 4 ∨ op.bytes = 8 := by
  cases op <;> simp_all [LoadOp.bytes]

theorem storeOp_bytes (op : StoreOp) (hop : op ≠ .fpuStore128) :
    op.bytes = 1 ∨ op.bytes = 2 ∨ op.bytes = 4 ∨ op.bytes = 8 := by
  cases op <;> simp_all [StoreOp.bytes]

theorem div_lt_of_bytes {b off : Nat} (hb : b = 1 ∨ b = 2 ∨ b = 4 ∨ b = 8) (h : off ≤ 4095 * b) :
    off / b < 4096 := by
  rcases hb with rfl | rfl | rfl | rfl <;> omega

/-- The canonical set-up of a memory form (operands, canonical registers, placed uses, address). -/
syntax "mr_simp" : tactic
macro_rules
  | `(tactic| mr_simp) => `(tactic| simp [defVals, placeUses, canonRegs, canonReg, canonBase,
      List.range_succ, OpSpec.def_, OpSpec.use, Operand.isUse, Operand.isDef, AMode.addr, regX, rnum, spOf,
      extendVal, ext_uxtw, ext_sxtw, log2_le_of_bytes, *])

/-- Close the side goals of `ss_load`/`ss_store` for a concrete addressing mode. -/
syntax "mr_fin" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| mr_fin) => `(tactic| first
    | (intro s; mr_simp; done)
    | (mr_simp; repeat (refine SameWorld.w_left (by simp [Masked, rnum]) ?_)
       exact SameWorld.refl F _)
    | (mr_simp; done))

variable (F : BitVec 64 → Prop) (ctx : FnCtx)

set_option maxHeartbeats 1000000 in
/-- A load through a covered addressing mode, on the canonical run (`straightSem`). -/
theorem straight_load (op : LoadOp) (hop : op ≠ .fpuLoad128) (d : Nat) (am : AMode)
    (fl : Clif.MemFlags) (uses : List CV) (w : Arm.ArmState) (a : BitVec 64)
    (ha : amodeAddr ctx.slotBase am op.bytes uses w = some a) (hav : Avoids F op.bytes a)
    (herr : Arm.r .ERR w = .None) (hal : Arm.CheckSPAlignment w) :
    ∃ w', straightSem F ctx (.load op (.vreg d .int) am fl) uses w =
      some ([ofX (loadVal op a w)], w', .next) ∧ SameWorld F w' w := by
  have hb := loadOp_bytes op hop
  unfold amodeAddr at ha
  split at ha
  · cases ha
    exact ss_load hop (amC := .regReg (.x 1) (.x 2)) rfl rfl (by mr_fin)
      (mm_regReg 1 2 (by omega) (by omega)) (by mr_fin)
      herr hal (by mr_fin) hav
  · cases ha
    exact ss_load hop (amC := .regScaled (.x 1) (.x 2)) rfl rfl (by mr_fin)
      (mm_regScaled 1 2 (by omega) (by omega)) (by mr_fin)
      herr hal (by mr_fin) hav
  · split at ha
    · cases ha
      rename_i e _ _ he
      exact ss_load hop (amC := .regScaledExtended (.x 1) (.x 2) e) rfl rfl (by mr_fin)
        (mm_regScaledExtended (by rcases he with rfl | rfl <;> decide) 1 2 (by omega) (by omega))
        (by mr_fin) herr hal (by rcases he with rfl | rfl <;> mr_fin) hav
    · cases ha
  · split at ha
    · cases ha
      rename_i e _ _ he
      exact ss_load hop (amC := .regExtended (.x 1) (.x 2) e) rfl rfl (by mr_fin)
        (mm_regExtended (by rcases he with rfl | rfl <;> decide) 1 2 (by omega) (by omega))
        (by mr_fin) herr hal (by rcases he with rfl | rfl <;> mr_fin) hav
    · cases ha
  · split at ha
    · cases ha
      rename_i off _ ho
      exact ss_load hop (amC := .unscaled (.x 1) off) rfl rfl (by mr_fin)
        (mm_unscaled ho.1 (by omega) 1 (by omega)) (by mr_fin)
        herr hal (by mr_fin) hav
    · cases ha
  · split at ha
    · cases ha
      rename_i off _ ho
      exact ss_load hop (amC := .unsignedOffset (.x 1) off) rfl rfl (by mr_fin)
        (mm_uoff ho.1 (div_lt_of_bytes hb ho.2) 1 (by omega)) (by mr_fin)
        herr hal (by mr_fin) hav
    · cases ha
  · cases ha
    rename_i off
    exact ss_load hop (amC := .slotOffset off) rfl rfl (by mr_fin) trivial (by mr_fin)
      herr hal (by mr_fin) hav
  · cases ha

set_option maxHeartbeats 1000000 in
/-- A store through a covered addressing mode, on the canonical run (`straightSem`). -/
theorem straight_store (op : StoreOp) (hop : op ≠ .fpuStore128) (d : Nat) (am : AMode)
    (fl : Clif.MemFlags) (v : CV) (uses : List CV) (w : Arm.ArmState) (a : BitVec 64)
    (ha : amodeAddr ctx.slotBase am op.bytes uses w = some a) (hav : Avoids F op.bytes a)
    (herr : Arm.r .ERR w = .None) (hal : Arm.CheckSPAlignment w) :
    ∃ w', straightSem F ctx (.store op (.vreg d .int) am fl) (v :: uses) w = some ([], w', .next) ∧
      SameWorld F w' (Arm.write_mem_bytes op.bytes a ((lo64 v).setWidth (op.bytes * 8)) w) := by
  have hb := storeOp_bytes op hop
  unfold amodeAddr at ha
  split at ha
  · cases ha
    exact ss_store hop (amC := .regReg (.x 1) (.x 2)) rfl rfl (by mr_fin)
      (mm_regReg 1 2 (by omega) (by omega)) (by mr_fin)
      (by mr_fin) herr hal (by mr_fin) hav
  · cases ha
    exact ss_store hop (amC := .regScaled (.x 1) (.x 2)) rfl rfl (by mr_fin)
      (mm_regScaled 1 2 (by omega) (by omega)) (by mr_fin)
      (by mr_fin) herr hal (by mr_fin) hav
  · split at ha
    · cases ha
      rename_i e _ _ he
      exact ss_store hop (amC := .regScaledExtended (.x 1) (.x 2) e) rfl rfl (by mr_fin)
        (mm_regScaledExtended (by rcases he with rfl | rfl <;> decide) 1 2 (by omega) (by omega))
        (by mr_fin) (by mr_fin) herr hal (by rcases he with rfl | rfl <;> mr_fin) hav
    · cases ha
  · split at ha
    · cases ha
      rename_i e _ _ he
      exact ss_store hop (amC := .regExtended (.x 1) (.x 2) e) rfl rfl (by mr_fin)
        (mm_regExtended (by rcases he with rfl | rfl <;> decide) 1 2 (by omega) (by omega))
        (by mr_fin) (by mr_fin) herr hal (by rcases he with rfl | rfl <;> mr_fin) hav
    · cases ha
  · split at ha
    · cases ha
      rename_i off _ ho
      exact ss_store hop (amC := .unscaled (.x 1) off) rfl rfl (by mr_fin)
        (mm_unscaled ho.1 (by omega) 1 (by omega)) (by mr_fin)
        (by mr_fin) herr hal (by mr_fin) hav
    · cases ha
  · split at ha
    · cases ha
      rename_i off _ ho
      exact ss_store hop (amC := .unsignedOffset (.x 1) off) rfl rfl (by mr_fin)
        (mm_uoff ho.1 (div_lt_of_bytes hb ho.2) 1 (by omega))
        (by mr_fin) (by mr_fin) herr hal (by mr_fin) hav
    · cases ha
  · cases ha
    rename_i off
    exact ss_store hop (amC := .slotOffset off) rfl rfl (by mr_fin) trivial (by mr_fin) (by mr_fin)
      herr hal (by mr_fin) hav
  · cases ha

/-- A stack-slot address on the canonical run (`straightSem`). -/
theorem straight_loadAddr (d : Nat) (off : Int) (w : Arm.ArmState)
    (herr : Arm.r .ERR w = .None) :
    ∃ w', straightSem F ctx (.loadAddr (.vreg d .int) (.slotOffset off)) [] w =
      some ([ofX (spOf w + BitVec.ofInt 64 (off + ctx.slotBase))], w', .next) ∧ SameWorld F w' w := by
  obtain ⟨P, o, hT⟩ := execMInst_loadAddr_slot' ctx env0 (d := 0) (by omega) off w
  obtain ⟨-, -, f3, -⟩ := ldPost_facts w P (a := 0) (by omega)
    (spOf w + BitVec.ofInt 64 (off + ctx.slotBase)) o
  have hx := x16w_facts o w
  have hpl : placeUses #[⟨d, .int, .def, .late, .reg⟩] (canonRegs #[⟨d, .int, .def, .late, .reg⟩])
      [] w = w := by mr_simp
  have hcanon : canonRegs #[⟨d, .int, .def, .late, .reg⟩] = #[.x 0] := by
    simp [canonRegs, canonReg, canonBase, List.range_succ]
  refine ⟨ldPost w P 0 (spOf w + BitVec.ofInt 64 (off + ctx.slotBase)) o, ?_, ?_⟩
  · rw [straightSem_of (ops := #[⟨d, .int, .def, .late, .reg⟩])
      (ic := .loadAddr (.x 0) (.slotOffset off)) rfl (by rw [hcanon]; rfl)
      (by rw [hpl]; intro p hp; simp [MInst.accesses] at hp) (by rw [hpl]; exact hT) ?_ ?_]
    · simp [defVals, hcanon, Operand.isDef, f3, ofX]
    · simp only [ldPost]
      rw [Arm.r_of_w_different (by simp), Arm.r_of_w_different (by simp), hx.2.1, herr]
    · simp only [ldPost]
      rw [Arm.w_program, Arm.w_program, hx.2.2.1]
  · simp only [ldPost]
    exact SameWorld.w_left (by simp [Masked]) (SameWorld.w_left (by simp [Masked])
      (sameWorld_x16w o none (SameWorld.refl F w)))

/-- **`MemRefines` for `csem`** (M6): at slot base `ctx.slotBase` and the link-time symbol
addresses `syms` that the external semantics' `sym` agrees with. -/
theorem memRefines_csem (X : ExtSem) {sb : Nat} {syms : String → Option Nat}
    (hsb : ctx.slotBase = sb) (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b) :
    MemRefines F sb syms (csem F ctx X) := by
  subst hsb
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro op d am fl uses w a hop ha hav
    rw [csem_straight rfl]
    split
    · rename_i hc
      exact straight_load F ctx op hop d am fl uses w a ha hav hc.2.1 hc.2.2
    · exact ⟨w, by simp [mspec, hop, ha], SameWorld.refl F w⟩
  · intro op d am fl v uses w a hop ha hav
    rw [csem_straight rfl]
    split
    · rename_i hc
      exact straight_store F ctx op hop d am fl v uses w a ha hav hc.2.1 hc.2.2
    · exact ⟨_, by simp [mspec, hop, ha], SameWorld.refl F _⟩
  · intro d off w
    rw [csem_straight rfl]
    split
    · rename_i hc
      exact straight_loadAddr F ctx d off w hc.2.1
    · exact ⟨w, by simp [mspec], SameWorld.refl F w⟩
  · intro d n b w hn
    exact ⟨w, by simp [csem, hsym n b hn], SameWorld.refl F w⟩

end Backend.Proof
