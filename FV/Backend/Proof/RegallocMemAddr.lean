import FV.Backend.Proof.RegallocMemCorr
import FV.Backend.Proof.RegallocOS

/-!
# `loadAddr` of a stack-slot offset (M6 proof)

`loadAddr xd, [sp + off + slotBase]` (the lowering of `stack_addr`) expands, after
`memFinalize`, to `mov xd, sp` / `add|sub xd, sp, #imm` / (x16 constant load) `add xd, sp,
x16, sxtx`. `execMInst_loadAddr_slot`: every expansion writes `sp + off + slotBase` into `xd`
(x16 possibly clobbered). `corr_loadAddr_slot`/`os_loadAddr_slot`: its `OperandsSound`.
-/

namespace Backend.Proof

open Backend

theorem execLines_append : ∀ (env : Env) (A B : List Line) (s : Arm.ArmState),
    execLines env (A ++ B) s =
      (execLines env A s).bind (execLines { env with pc := env.pc + 4 * A.length } B)
  | env, [], B, s => by simp [execLines]
  | env, .ins i t :: A, B, s => by
    simp only [List.cons_append, execLines]
    split
    · split
      · rw [execLines_append]
        congr 2
        cases env; simp; omega
      · rfl
    · rfl
  | _, .label _ :: _, _, _ => rfl
  | _, .word _ _ :: _, _, _ => rfl

theorem zext_imm12 {k : Nat} (hk : k < 4096) : (0#52 ++ BitVec.ofNat 12 k) = BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append]
  simp [Nat.mod_eq_of_lt hk]
  omega

theorem exec_add_sp (env : Env) {d : Nat} (hd : d < 29) {k : Nat} (hk : k < 4096) (s : Arm.ArmState) :
    execLines env [.ins (.aluImm12 .add true (.x d) .sp ⟨k, false⟩)] s =
      some (Arm.w (.GPR (BitVec.ofNat 5 d)) (Arm.r (.GPR 31#5) s + BitVec.ofNat 64 k)
        (Arm.w .PC (Arm.r .PC s + 4#64) s)) := by
  have e0 := ne31_of hd
  have l0 := le30_of hd
  simp (config := {decide := true}) [csimp_rules, e0, l0, hk, Arm.fst_AddWithCarry_eq_add, zext_imm12 hk]

theorem exec_sub_sp (env : Env) {d : Nat} (hd : d < 29) {k : Nat} (hk : k < 4096) (s : Arm.ArmState) :
    execLines env [.ins (.aluImm12 .sub true (.x d) .sp ⟨k, false⟩)] s =
      some (Arm.w (.GPR (BitVec.ofNat 5 d)) (Arm.r (.GPR 31#5) s - BitVec.ofNat 64 k)
        (Arm.w .PC (Arm.r .PC s + 4#64) s)) := by
  have e0 := ne31_of hd
  have l0 := le30_of hd
  simp (config := {decide := true}) [csimp_rules, e0, l0, hk, Arm.fst_AddWithCarry_eq_sub_neg,
    zext_imm12 hk]

theorem exec_mov_sp (env : Env) {d : Nat} (hd : d < 29) (s : Arm.ArmState) :
    execLines env [.ins (.mov true (.x d) .sp)] s =
      some (Arm.w (.GPR (BitVec.ofNat 5 d)) (Arm.r (.GPR 31#5) s)
        (Arm.w .PC (Arm.r .PC s + 4#64) s)) := by
  have e0 := ne31_of hd
  have l0 := le30_of hd
  simp (config := {decide := true}) [csimp_rules, e0, l0, Arm.fst_AddWithCarry_eq_add]

theorem exec_add_sp_x16 (env : Env) {d : Nat} (hd : d < 29) (s : Arm.ArmState) :
    execLines env [.ins (.aluRRRExtend .add true (.x d) .sp (.x 16) .sxtx)] s =
      some (Arm.w (.GPR (BitVec.ofNat 5 d)) (Arm.r (.GPR 31#5) s + Arm.r (.GPR 16#5) s)
        (Arm.w .PC (Arm.r .PC s + 4#64) s)) := by
  have e0 := ne31_of hd
  have l0 := le30_of hd
  simp (config := {decide := true}) [csimp_rules, e0, l0, Arm.fst_AddWithCarry_eq_add,
    show ExtendOp.sxtx.bits = 7#3 from rfl, sxtx_id]

/-- **`loadAddr` of a slot offset on the Arm model.** -/
theorem execMInst_loadAddr_slot (ctx : FnCtx) (env : Env) {d : Nat} (hd : d < 29) (off : Int)
    (s : Arm.ArmState) :
    ∃ P o, execMInst ctx env (.loadAddr (.x d) (.slotOffset off)) s =
      some (Arm.w (.GPR (BitVec.ofNat 5 d)) (spOf s + BitVec.ofInt 64 (off + ctx.slotBase))
        (Arm.w .PC P (x16w o s))) := by
  simp only [execMInst, MInst.lines, memFinalize, bind, Except.bind, pure, Except.pure]
  generalize off + (ctx.slotBase : Int) = v
  cases h9 : simm9? v with
  | some k =>
    have hk : k = v ∧ -256 ≤ v ∧ v ≤ 255 := by
      simp only [simm9?] at h9; split at h9 <;> simp_all
    obtain ⟨rfl, h1, h2⟩ := hk
    simp only [h9, MInst.lines.addOff, List.nil_append]
    by_cases k0 : k = 0
    · subst k0
      refine ⟨Arm.r .PC s + 4#64, none, ?_⟩
      simp [exec_mov_sp env hd, x16w, spOf]
    · by_cases kp : k > 0
      · refine ⟨Arm.r .PC s + 4#64, none, ?_⟩
        simp [k0, kp, exec_add_sp env hd (k := k.toNat) (by omega), x16w, spOf]
        congr; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofInt]; omega
      · refine ⟨Arm.r .PC s + 4#64, none, ?_⟩
        simp [k0, kp, exec_sub_sp env hd (k := (-k).toNat) (by omega), x16w, spOf]
        congr 1; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofInt]; omega
  | none =>
    cases hu : uimm12Scaled? v 1 with
    | some o =>
      have hk : (o : Int) = v ∧ o ≤ 4095 := by
        simp only [uimm12Scaled?] at hu
        split at hu
        · rename_i hc
          simp only [Option.some.injEq] at hu
          subst hu
          omega
        · cases hu
      simp only [h9, hu, MInst.lines.addOff, List.nil_append]
      refine ⟨Arm.r .PC s + 4#64, none, ?_⟩
      by_cases o0 : o = 0
      · subst o0; simp at hk; subst hk; simp [simm9?] at h9
      · obtain ⟨rfl, ho⟩ := hk
        have hp : 0 < o := by omega
        simp only [o0, hp, if_true, if_false, beq_iff_eq, Int.natCast_eq_zero, gt_iff_lt, Int.natCast_pos,
          Int.toNat_natCast]
        rw [exec_add_sp env hd (k := o) (by omega)]
        simp [x16w, spOf]
    | none =>
      refine ⟨Arm.r .PC s + BitVec.ofNat 64 (4 * (loadConst64 (.x 16) (u64 v)).length) + 4#64,
        some (BitVec.ofNat 64 (u64 v)), ?_⟩
      simp only [h9, hu]
      rw [execLines_append, (steps_loadConst64 env (n := 16) (by omega) (u64 v) s).exec]
      simp only [Option.bind_some, pcx]
      rw [exec_add_sp_x16 _ hd]
      simp [x16w, spOf, Arm.r_of_w_different, Arm.r_of_w_same, ofNat_u64, pcx, Arm.w_of_w_shadow]

theorem execMInst_loadAddr_slot' (ctx : FnCtx) (env : Env) {d : Nat} (hd : d < 29) (off : Int)
    (s : Arm.ArmState) :
    ∃ P o, execMInst ctx env (.loadAddr (.x d) (.slotOffset off)) s =
      some (ldPost s P d (spOf s + BitVec.ofInt 64 (off + ctx.slotBase)) o) := by
  obtain ⟨P, o, h⟩ := execMInst_loadAddr_slot ctx env hd off s
  exact ⟨P, o, by rw [h, ldPost, Arm.w_of_w_commute (by simp)]⟩

theorem corr_loadAddr_slot (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (d : Nat) (off : Int) :
    Corr F ctx env #[⟨d, .int, .def, .late, .reg⟩]
      (fun r => .loadAddr (r.getD 0 .xzr) (.slotOffset off)) := by
  intro regs s w t' ha hw hal hacc hex herr
  have hsz := ha.size
  simp only [List.size_toArray, List.length_cons, List.length_nil] at hsz
  have hf := ha.fits
  obtain ⟨r0, rfl⟩ := regs1 hsz
  simp [RegFits] at hf
  rcases hf with ⟨n0, rfl, hn0⟩
  have hcanon : canonRegs #[⟨d, .int, .def, .late, .reg⟩] = #[.x 0] := by
    simp [canonRegs, canonReg, canonBase, List.range_succ]
  have ht : placeUses #[⟨d, .int, .def, .late, .reg⟩] (canonRegs #[⟨d, .int, .def, .late, .reg⟩])
      (useVals #[⟨d, .int, .def, .late, .reg⟩] #[.x n0] s) w = w := by
    simp [placeUses, useVals, hcanon, Operand.isUse]
  rw [ht, hcanon] at hex
  rw [hcanon]
  have hsp : spOf w = spOf s := sw_r_eq hw (by simp [Masked])
  obtain ⟨P, o, hS⟩ := execMInst_loadAddr_slot' ctx env (d := n0) hn0.1 off s
  obtain ⟨Q, oC, hT⟩ := execMInst_loadAddr_slot' ctx env0 (d := 0) (by omega) off w
  change execMInst ctx env0 (.loadAddr (.x 0) (.slotOffset off)) w = some t' at hex
  rw [hT, Option.some.injEq] at hex
  subst hex
  obtain ⟨f1, f2, f3, f4⟩ := ldPost_facts s P (a := n0) ⟨hn0.1, hn0.2.1⟩
    (spOf s + BitVec.ofInt 64 (off + ctx.slotBase)) o
  obtain ⟨-, -, g3, -⟩ := ldPost_facts w Q (a := 0) (by omega)
    (spOf w + BitVec.ofInt 64 (off + ctx.slotBase)) oC
  refine ⟨_, hS, ldPost_sw hw ⟨hn0.1, hn0.2.2.2⟩ (by omega) _ _ _ _, ⟨f1, fun a _ => by rw [f2]⟩,
    ?_, fun r hr hnd => f4 r hr (fun e => hnd ⟨⟨d, .int, .def, .late, .reg⟩, .x n0⟩ (by simp) rfl e.symm)⟩
  simp [defVals, Operand.isDef]
  rw [f3, g3, hsp]

theorem os_loadAddr_slot (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (X : ExtSem) (d : Nat)
    (off : Int) :
    OperandsSound F (execMInst ctx env) (csem F ctx X) (.loadAddr (.vreg d .int) (.slotOffset off)) :=
  os_of_corr rfl _ (by assign_tac) (by fo_tac) rfl rfl (corr_loadAddr_slot F ctx env d off)

end Backend.Proof
