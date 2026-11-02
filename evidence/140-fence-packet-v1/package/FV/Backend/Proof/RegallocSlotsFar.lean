import FV.Backend.Proof.RegallocSlots
import FV.Backend.Proof.RegallocMemAddr

/-!
# Far slots (M6 proof)

A slot at an offset of 32 KiB or more is addressed through x16 (`slotStoreAt`/`slotLoadAt`):
`spAddrX16 off` sets `x16 := sp + off` (`movz`/`movk` of the chunks of `loadConst64`, then
`add x16, sp, x16`; `execAll_spAddrX16`), and `str`/`ldr` at `[x16]` makes the slot access of
`stSt`/`ldIntSt`/`ldFSt` (`exec_store_int_x16` …). Every instruction is one line. The address
sequence changes only the pc and x16 (`pcx s 16`), both outside the world and no location
(`pcx_world`, `pcx_locVal`); at offsets below 32 KiB the access is the single instruction of
`RegallocSlots` (and the state "before" it is `s` itself, `pcx_self`).
`exec_slotStoreAt_int` … combine both cases.
-/

namespace Backend.Proof
open Backend

/-- Run a list of instructions in sequence (at any code position: frame moves do not read
the pc). -/
def ExecAll (ctx : FnCtx) : List MInst → Arm.ArmState → Arm.ArmState → Prop
  | [], s, s' => s' = s
  | i :: is, s, s' => ∃ t, (∀ env, execMInst ctx env i s = some t) ∧
      Arm.r .ERR t = Arm.r .ERR s ∧ t.program = s.program ∧ ExecAll ctx is t s'

theorem ExecAll.append {ctx : FnCtx} :
    ∀ {A B : List MInst} {s s1 s2 : Arm.ArmState}, ExecAll ctx A s s1 → ExecAll ctx B s1 s2 →
      ExecAll ctx (A ++ B) s s2
  | [], _, _, _, _, hA, hB => by simp only [ExecAll] at hA; subst hA; exact hB
  | _ :: _, _, _, _, _, ⟨t, h1, h2, h3, hA⟩, hB => ⟨t, h1, h2, h3, ExecAll.append hA hB⟩

theorem ExecAll.one {ctx : FnCtx} {i : MInst} {s t : Arm.ArmState}
    (h : ∀ env, execMInst ctx env i s = some t) (he : Arm.r .ERR t = Arm.r .ERR s)
    (hp : t.program = s.program) : ExecAll ctx [i] s t :=
  ⟨t, h, he, hp, rfl⟩

/-! ## The state after the address sequence -/

theorem pcx_self (s : Arm.ArmState) : pcx s 16 (Arm.r .PC s) (Arm.r (.GPR 16#5) s) = s := by
  simp only [pcx]
  rw [show (BitVec.ofNat 5 16) = 16#5 from rfl, Arm.w_irrelevant, Arm.w_irrelevant]

theorem pcx_sp (s : Arm.ArmState) (P X : BitVec 64) : spOf (pcx s 16 P X) = spOf s := by
  simp only [spOf, pcx]
  rw [Arm.r_of_w_different (by simp), Arm.r_of_w_different (by decide)]

theorem pcx_mem (s : Arm.ArmState) (P X : BitVec 64) : (pcx s 16 P X).mem = s.mem := by
  simp only [pcx]; rw [Arm.ArmState.mem_w_eq_mem, Arm.ArmState.mem_w_eq_mem]

theorem pcx_world {F : BitVec 64 → Prop} {s w : Arm.ArmState} (h : SameWorld F s w)
    (P X : BitVec 64) : SameWorld F (pcx s 16 P X) w :=
  SameWorld.w_left (by simp [Masked]) (SameWorld.w_left (by simp [Masked]) h)

theorem pcx_align {s : Arm.ArmState} (h : Arm.CheckSPAlignment s) (P X : BitVec 64) :
    Arm.CheckSPAlignment (pcx s 16 P X) := by
  have e : Arm.r (.GPR 31#5) (pcx s 16 P X) = Arm.r (.GPR 31#5) s := pcx_sp s P X
  simp only [Arm.CheckSPAlignment, Arm.read_gpr] at h ⊢
  rw [e]; exact h

/-- x16 is no allocatable register. -/
theorem pcx_regVal {r : Reg} (hr : r.allocatable = true) (s : Arm.ArmState) (P X : BitVec 64) :
    regVal (pcx s 16 P X) r = regVal s r := by
  simp only [pcx]
  rw [regVal_w (by cases r <;> simp [Reg.field]), regVal_w ?_]
  rcases allocatable_cases hr with ⟨k, rfl, hk⟩ | ⟨k, rfl, hk⟩
  · simp only [Reg.field, ne_eq, Option.some.injEq, Arm.StateField.GPR.injEq]
    exact rnum_ne (a := k) (b := 16) (by omega) (by omega) (by omega)
  · simp [Reg.field]

theorem pcx_gpr {n : Nat} (hn : n < 29) (hn16 : n ≠ 16) (s : Arm.ArmState) (P X : BitVec 64) :
    Arm.r (.GPR (rnum n)) (pcx s 16 P X) = Arm.r (.GPR (rnum n)) s := by
  simp only [pcx]
  rw [Arm.r_of_w_different (by simp), Arm.r_of_w_different ?_]
  simp only [ne_eq, Arm.StateField.GPR.injEq]
  exact rnum_ne (a := n) (b := 16) (by omega) (by omega) hn16

theorem pcx_sfp (n : Nat) (s : Arm.ArmState) (P X : BitVec 64) :
    Arm.r (.SFP (rnum n)) (pcx s 16 P X) = Arm.r (.SFP (rnum n)) s := by
  simp only [pcx]
  rw [Arm.r_of_w_different (by simp), Arm.r_of_w_different (by simp)]

theorem pcx_locVal {fr : RAFrame} {l : Loc} (hl : ValidLoc l) (s : Arm.ArmState) (P X : BitVec 64) :
    locVal fr (pcx s 16 P X) l = locVal fr s l := by
  cases l with
  | reg r => exact pcx_regVal (hl r rfl) s P X
  | stack k c => exact locVal_frame_congr (fun r h => Loc.noConfusion h) (pcx_sp s P X) (pcx_mem s P X)
  | save r => exact locVal_frame_congr (fun r h => Loc.noConfusion h) (pcx_sp s P X) (pcx_mem s P X)

theorem pcx_err (s : Arm.ArmState) (P X : BitVec 64) :
    Arm.r .ERR (pcx s 16 P X) = Arm.r .ERR s := (pcx_facts s 16 P X).2.1

theorem pcx_prog (s : Arm.ArmState) (P X : BitVec 64) :
    (pcx s 16 P X).program = s.program := (pcx_facts s 16 P X).2.2.1

theorem pcx_pcx (s : Arm.ArmState) (P X P' X' : BitVec 64) :
    pcx (pcx s 16 P X) 16 P' X' = pcx s 16 P' X' := by
  simp only [pcx]
  rw [Arm.w_of_w_commute (fld1 := .GPR _) (fld2 := .PC) (by simp), Arm.w_of_w_shadow,
    Arm.w_of_w_shadow]

/-! ## `x16 := sp + off` -/

theorem execM_movz (ctx : FnCtx) (env : Env) {c : Nat} (hc : c < 2 ^ 16) (s : Arm.ArmState) :
    execMInst ctx env (.movWide .movZ (.x 16) ⟨c, 0⟩ .size64) s =
      some (pcx s 16 (Arm.r .PC s + 4#64) (BitVec.ofNat 64 c)) := by
  obtain ⟨ai, ha, he⟩ := exec_movz env (n := 16) (by omega) hc s
  have hl : MInst.lines ctx (.movWide .movZ (.x 16) ⟨c, 0⟩ .size64) {} =
      .ok ([.ins (.movWide .movZ true (.x 16) ⟨c, 0⟩) none], {}) := rfl
  simp only [execMInst, hl]
  rw [execLines_one ha (by rw [he, Arm.r_of_w_same]), he]; rfl

theorem execM_movk (ctx : FnCtx) (env : Env) {c i : Nat} (hc : c < 2 ^ 16) (hi : i < 4)
    (s : Arm.ArmState) :
    execMInst ctx env (.movK (.x 16) (.x 16) ⟨c, i⟩ .size64) s =
      some (Arm.w .PC (Arm.r .PC s + 4#64) (Arm.w (.GPR (BitVec.ofNat 5 16))
        (Arm.BitVec.partInstall (16 * i) 16 (BitVec.ofNat 16 c) (Arm.r (.GPR (BitVec.ofNat 5 16)) s)) s)) := by
  obtain ⟨ai, ha, he⟩ := exec_movk env (n := 16) (by omega) hc hi s
  have hl : MInst.lines ctx (.movK (.x 16) (.x 16) ⟨c, i⟩ .size64) {} =
      .ok ([.ins (.movk true (.x 16) ⟨c, i⟩) none], {}) := rfl
  simp only [execMInst, hl]
  rw [execLines_one ha (by rw [he, Arm.r_of_w_same]), he]

theorem execM_add_sp_x16 (ctx : FnCtx) (env : Env) (s : Arm.ArmState) :
    execMInst ctx env (.aluRRRExtend .add .size64 (.x 16) .sp (.x 16) .sxtx) s =
      some (Arm.w (.GPR (BitVec.ofNat 5 16)) (spOf s + Arm.r (.GPR 16#5) s)
        (Arm.w .PC (Arm.r .PC s + 4#64) s)) := by
  have hl : MInst.lines ctx (.aluRRRExtend .add .size64 (.x 16) .sp (.x 16) .sxtx) {} =
      .ok ([.ins (.aluRRRExtend .add true (.x 16) .sp (.x 16) .sxtx) none], {}) := rfl
  simp only [execMInst, hl]
  exact exec_add_sp_x16 env (d := 16) (by omega) s

theorem execAll_movks (ctx : FnCtx) (s : Arm.ArmState) :
    ∀ (ks : List (Nat × Nat)) (P X : BitVec 64), (∀ p ∈ ks, p.1 < 2 ^ 16 ∧ p.2 < 4) →
      ExecAll ctx (ks.map fun p => MInst.movK (.x 16) (.x 16) ⟨p.1, p.2⟩ .size64) (pcx s 16 P X)
        (pcx s 16 (P + BitVec.ofNat 64 (4 * ks.length))
          (ks.foldl (fun X p => Arm.BitVec.partInstall (16 * p.2) 16 (BitVec.ofNat 16 p.1) X) X))
  | [], P, X, _ => by simp [ExecAll]
  | (c, i) :: ks, P, X, hk => by
    obtain ⟨hc, hi⟩ := hk (c, i) (by simp)
    obtain ⟨f1, f2, f3, f4⟩ := pcx_facts s 16 P X
    have he : ∀ env, execMInst ctx env (.movK (.x 16) (.x 16) ⟨c, i⟩ .size64) (pcx s 16 P X) =
        some (pcx s 16 (P + 4#64) (Arm.BitVec.partInstall (16 * i) 16 (BitVec.ofNat 16 c) X)) := by
      intro env
      rw [execM_movk ctx env hc hi, f4, pcx_step]
    refine ⟨_, he, by rw [pcx_err, pcx_err], by rw [pcx_prog, pcx_prog], ?_⟩
    have := execAll_movks ctx s ks (P + 4#64)
      (Arm.BitVec.partInstall (16 * i) 16 (BitVec.ofNat 16 c) X) (fun p hp => hk p (by simp [hp]))
    simp only [List.length_cons, List.foldl_cons] at this ⊢
    have e : P + 4#64 + BitVec.ofNat 64 (4 * ks.length) = P + BitVec.ofNat 64 (4 * (ks.length + 1)) := by
      rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega
    rw [e] at this
    exact this

/-- **The address sequence** sets `x16 := sp + off`; only the pc and x16 change. -/
theorem execAll_spAddrX16 (ctx : FnCtx) (off : Nat) (s : Arm.ArmState) :
    ∃ P, ExecAll ctx (spAddrX16 off) s (pcx s 16 P (spOf s + BitVec.ofNat 64 off)) := by
  let ks := ([1, 2, 3].map fun i => (chunk16 (mask64 off) i, i)).filter (·.1 != 0)
  have hsp : spAddrX16 off = .movWide .movZ (.x 16) ⟨chunk16 (mask64 off) 0, 0⟩ .size64 ::
      (ks.map fun p => MInst.movK (.x 16) (.x 16) ⟨p.1, p.2⟩ .size64) ++
      [.aluRRRExtend .add .size64 (.x 16) .sp (.x 16) .sxtx] := rfl
  have hks : ∀ p ∈ ks, p.1 < 2 ^ 16 ∧ p.2 < 4 := fun p hp => by
    simp only [ks, List.mem_filter, List.mem_map] at hp
    obtain ⟨⟨i, hi, rfl⟩, -⟩ := hp
    simp at hi
    exact ⟨chunk16_lt _ _, by omega⟩
  let P1 := Arm.r .PC s + 4#64
  let X1 := BitVec.ofNat 64 (chunk16 (mask64 off) 0)
  have hM := execAll_movks ctx s ks P1 X1 hks
  rw [loadConst64_fold off] at hM
  let P2 := P1 + BitVec.ofNat 64 (4 * ks.length)
  let u := pcx s 16 P2 (BitVec.ofNat 64 off)
  have hA : ∀ env, execMInst ctx env (.aluRRRExtend .add .size64 (.x 16) .sp (.x 16) .sxtx) u =
      some (pcx s 16 (P2 + 4#64) (spOf s + BitVec.ofNat 64 off)) := by
    intro env
    rw [execM_add_sp_x16, pcx_sp]
    obtain ⟨g1, -, -, g4⟩ := pcx_facts s 16 P2 (BitVec.ofNat 64 off)
    rw [show (16#5 : BitVec 5) = BitVec.ofNat 5 16 from rfl, g4, g1]
    simp only [u, pcx]
    rw [Arm.w_of_w_shadow, Arm.w_of_w_commute (fld1 := .GPR _) (fld2 := .PC) (by simp),
      Arm.w_of_w_shadow]
  refine ⟨P2 + 4#64, ?_⟩
  rw [hsp]
  refine ⟨pcx s 16 P1 X1, fun env => execM_movz ctx env (chunk16_lt _ _) s,
    by rw [pcx_err], by rw [pcx_prog], ?_⟩
  exact ExecAll.append hM (ExecAll.one hA ((pcx_err _ _ _).trans (pcx_err _ _ _).symm)
    ((pcx_prog _ _ _).trans (pcx_prog _ _ _).symm))

/-! ## Slot accesses at `[x16]` -/

theorem exec_store_int_x16 (ctx : FnCtx) (env : Env) {n off : Nat} (hn : n < 29) {s : Arm.ArmState}
    (hx : Arm.r (.GPR 16#5) s = spOf s + BitVec.ofNat 64 off) :
    execMInst ctx env (.store .store64 (.x n) (.unsignedOffset (.x 16) 0) trustedFlags) s =
      some (stSt s off 8 (Arm.r (.GPR (rnum n)) s)) := by
  have hl : MInst.lines ctx (.store .store64 (.x n) (.unsignedOffset (.x 16) 0) trustedFlags) {} =
      .ok ([.ins (.store .store64 (.x n) (.unsignedOffset (.x 16) 0)) trustedFlags.trapCode], {}) := by
    simp [MInst.lines, memFinalize]
  have ha' : Insn.toArmInst env (.store .store64 (.x n) (.unsignedOffset (.x 16) 0)) =
      .ok (.LDST (.Reg_unsigned_imm { size := 3#2, V := 0#1, opc := 0#2, imm12 := 0#12, Rn := 16#5, Rt := rnum n })) := by
    simp [Insn.toArmInst, Insn.armFields, Arm.ArmInst.norm, StoreOp.fields, ldstFields,
      Reg.encZR, Reg.encSP, show n ≤ 30 by omega, rnum, uField, StoreOp.bytes]
  have he : Arm.exec_inst (.LDST (.Reg_unsigned_imm { size := 3#2, V := 0#1, opc := 0#2, imm12 := 0#12, Rn := 16#5, Rt := rnum n })) s =
      stSt s off 8 (Arm.r (.GPR (rnum n)) s) := by
    rw [stSt, ← hx]
    simp [Arm.exec_inst, Arm.LDST.exec_reg_imm_unsigned_offset, Arm.LDST.exec_reg_imm_common,
      Arm.LDST.reg_imm_operation, Arm.LDST.Reg_offset.value,
      Arm.LDST.reg_imm_constrain_unpredictable, Arm.ldst_read, Arm.read_gpr_zr, Arm.read_gpr,
      rnum_ne31 hn, Arm.read_pc, Arm.write_pc, Arm.BitVec.lsb]
    rfl
  simp only [execMInst, hl]
  rw [execLines_one ha' (by rw [he, stSt, Arm.r_of_w_same]), he]

theorem exec_load_int_x16 (ctx : FnCtx) (env : Env) {n off : Nat} (hn : n < 29) {s : Arm.ArmState}
    (hx : Arm.r (.GPR 16#5) s = spOf s + BitVec.ofNat 64 off) :
    execMInst ctx env (.load .uload64 (.x n) (.unsignedOffset (.x 16) 0) trustedFlags) s =
      some (ldIntSt s off n) := by
  have hl : MInst.lines ctx (.load .uload64 (.x n) (.unsignedOffset (.x 16) 0) trustedFlags) {} =
      .ok ([.ins (.load .uload64 (.x n) (.unsignedOffset (.x 16) 0)) trustedFlags.trapCode], {}) := by
    simp [MInst.lines, memFinalize]
  have ha' : Insn.toArmInst env (.load .uload64 (.x n) (.unsignedOffset (.x 16) 0)) =
      .ok (.LDST (.Reg_unsigned_imm { size := 3#2, V := 0#1, opc := 1#2, imm12 := 0#12, Rn := 16#5, Rt := rnum n })) := by
    simp [Insn.toArmInst, Insn.armFields, Arm.ArmInst.norm, LoadOp.fields, ldstFields,
      Reg.encZR, Reg.encSP, show n ≤ 30 by omega, rnum, uField, LoadOp.bytes]
  have he : Arm.exec_inst (.LDST (.Reg_unsigned_imm { size := 3#2, V := 0#1, opc := 1#2, imm12 := 0#12, Rn := 16#5, Rt := rnum n })) s =
      ldIntSt s off n := by
    rw [ldIntSt, ← hx, Arm.w_of_w_commute (by simp)]
    simp [Arm.exec_inst, Arm.LDST.exec_reg_imm_unsigned_offset, Arm.LDST.exec_reg_imm_common,
      Arm.LDST.reg_imm_operation, Arm.LDST.Reg_offset.value,
      Arm.LDST.reg_imm_constrain_unpredictable, Arm.write_gpr_zr, Arm.read_gpr,
      Arm.write_gpr, rnum_ne31 hn, Arm.read_pc, Arm.write_pc, Arm.BitVec.lsb]
    rfl
  simp only [execMInst, hl]
  rw [execLines_one ha' (by rw [he, ldIntSt, Arm.r_of_w_different (by simp), Arm.r_of_w_same]), he]

theorem exec_store_float_x16 (ctx : FnCtx) (env : Env) {n off : Nat} (hn : n < 32) {s : Arm.ArmState}
    (hx : Arm.r (.GPR 16#5) s = spOf s + BitVec.ofNat 64 off) :
    execMInst ctx env (.store .fpuStore128 (.v n) (.unsignedOffset (.x 16) 0) trustedFlags) s =
      some (stSt s off 16 (Arm.r (.SFP (rnum n)) s)) := by
  have hl : MInst.lines ctx (.store .fpuStore128 (.v n) (.unsignedOffset (.x 16) 0) trustedFlags) {} =
      .ok ([.ins (.store .fpuStore128 (.v n) (.unsignedOffset (.x 16) 0)) trustedFlags.trapCode], {}) := by
    simp [MInst.lines, memFinalize]
  have ha' : Insn.toArmInst env (.store .fpuStore128 (.v n) (.unsignedOffset (.x 16) 0)) =
      .ok (.LDST (.Reg_unsigned_imm { size := 0#2, V := 1#1, opc := 2#2, imm12 := 0#12, Rn := 16#5, Rt := rnum n })) := by
    simp [Insn.toArmInst, Insn.armFields, Arm.ArmInst.norm, StoreOp.fields, ldstFields,
      Reg.encV, Reg.encSP, show n ≤ 31 by omega, rnum, uField, StoreOp.bytes]
  have he : Arm.exec_inst (.LDST (.Reg_unsigned_imm { size := 0#2, V := 1#1, opc := 2#2, imm12 := 0#12, Rn := 16#5, Rt := rnum n })) s =
      stSt s off 16 (Arm.r (.SFP (rnum n)) s) := by
    rw [stSt, ← hx]
    simp only [Arm.exec_inst]
    simp only [Arm.LDST.exec_reg_imm_unsigned_offset, Arm.LDST.exec_reg_imm_common,
      decide_true, ite_true, show Arm.LDST.supported_simd_reg_imm 0#2 2#2 = true by decide,
      show Arm.BitVec.lsb (2#2) 1 = 1#1 by decide, show Arm.BitVec.lsb (2#2) 0 = 0#1 by decide,
      show Arm.LDST.reg_imm_constrain_unpredictable false true (16#5) (rnum n) = false by
        simp [Arm.LDST.reg_imm_constrain_unpredictable]]
    simp [Arm.LDST.reg_imm_operation, Arm.LDST.Reg_offset.value, Arm.ldst_read,
      Arm.read_gpr, Arm.read_pc, Arm.write_pc]
    rfl
  simp only [execMInst, hl]
  rw [execLines_one ha' (by rw [he, stSt, Arm.r_of_w_same]), he]

theorem exec_load_float_x16 (ctx : FnCtx) (env : Env) {n off : Nat} (hn : n < 32) {s : Arm.ArmState}
    (hx : Arm.r (.GPR 16#5) s = spOf s + BitVec.ofNat 64 off) :
    execMInst ctx env (.load .fpuLoad128 (.v n) (.unsignedOffset (.x 16) 0) trustedFlags) s =
      some (ldFSt s off n) := by
  have hl : MInst.lines ctx (.load .fpuLoad128 (.v n) (.unsignedOffset (.x 16) 0) trustedFlags) {} =
      .ok ([.ins (.load .fpuLoad128 (.v n) (.unsignedOffset (.x 16) 0)) trustedFlags.trapCode], {}) := by
    simp [MInst.lines, memFinalize]
  have ha' : Insn.toArmInst env (.load .fpuLoad128 (.v n) (.unsignedOffset (.x 16) 0)) =
      .ok (.LDST (.Reg_unsigned_imm { size := 0#2, V := 1#1, opc := 3#2, imm12 := 0#12, Rn := 16#5, Rt := rnum n })) := by
    simp [Insn.toArmInst, Insn.armFields, Arm.ArmInst.norm, LoadOp.fields, ldstFields,
      Reg.encV, Reg.encSP, show n ≤ 31 by omega, rnum, uField, LoadOp.bytes]
  have he : Arm.exec_inst (.LDST (.Reg_unsigned_imm { size := 0#2, V := 1#1, opc := 3#2, imm12 := 0#12, Rn := 16#5, Rt := rnum n })) s =
      ldFSt s off n := by
    rw [ldFSt, ← hx, Arm.w_of_w_commute (by simp)]
    simp only [Arm.exec_inst]
    simp only [Arm.LDST.exec_reg_imm_unsigned_offset, Arm.LDST.exec_reg_imm_common,
      decide_true, ite_true, show Arm.LDST.supported_simd_reg_imm 0#2 3#2 = true by decide,
      show Arm.BitVec.lsb (3#2) 1 = 1#1 by decide, show Arm.BitVec.lsb (3#2) 0 = 1#1 by decide,
      show Arm.LDST.reg_imm_constrain_unpredictable false true (16#5) (rnum n) = false by
        simp [Arm.LDST.reg_imm_constrain_unpredictable]]
    simp [Arm.LDST.reg_imm_operation, Arm.LDST.Reg_offset.value,
      Arm.write_sfp, Arm.read_gpr, Arm.read_pc, Arm.write_pc]
  simp only [execMInst, hl]
  rw [execLines_one ha' (by rw [he, ldFSt, Arm.r_of_w_different (by simp), Arm.r_of_w_same]), he]

/-! ## Slot accesses at any offset -/

theorem stSt_err (s : Arm.ArmState) (o n : Nat) (v : BitVec (n * 8)) :
    Arm.r .ERR (stSt s o n v) = Arm.r .ERR s := by
  rw [stSt, Arm.r_of_w_different (by simp), Arm.r_of_write_mem_bytes]

theorem stSt_prog (s : Arm.ArmState) (o n : Nat) (v : BitVec (n * 8)) :
    (stSt s o n v).program = s.program := by
  rw [stSt, Arm.w_program, Arm.write_mem_bytes_program]

theorem ldIntSt_err (s : Arm.ArmState) (o n : Nat) : Arm.r .ERR (ldIntSt s o n) = Arm.r .ERR s := by
  rw [ldIntSt, Arm.r_of_w_different (by simp), Arm.r_of_w_different (by simp)]
theorem ldIntSt_prog (s : Arm.ArmState) (o n : Nat) : (ldIntSt s o n).program = s.program := by
  rw [ldIntSt, Arm.w_program, Arm.w_program]
theorem ldFSt_err (s : Arm.ArmState) (o n : Nat) : Arm.r .ERR (ldFSt s o n) = Arm.r .ERR s := by
  rw [ldFSt, Arm.r_of_w_different (by simp), Arm.r_of_w_different (by simp)]
theorem ldFSt_prog (s : Arm.ArmState) (o n : Nat) : (ldFSt s o n).program = s.program := by
  rw [ldFSt, Arm.w_program, Arm.w_program]

theorem pcx_x16 (s : Arm.ArmState) (P : BitVec 64) (off : Nat) :
    Arm.r (.GPR 16#5) (pcx s 16 P (spOf s + BitVec.ofNat 64 off)) =
      spOf (pcx s 16 P (spOf s + BitVec.ofNat 64 off)) + BitVec.ofNat 64 off := by
  rw [pcx_sp]; exact (pcx_facts s 16 P _).2.2.2

/-- **An int slot store at any offset** (`slotStoreAt`): the store of `stSt` from a state
`pcx s 16 P X` (the address sequence's, or `s` itself below 32 KiB). -/
theorem exec_slotStoreAt_int (ctx : FnCtx) {n off : Nat} (hn : n < 29) (h8 : off % 8 = 0)
    {s : Arm.ArmState} (halign : Arm.CheckSPAlignment s) :
    ∃ P X, ExecAll ctx (slotStoreAt .int (.x n) off) s
      (stSt (pcx s 16 P X) off 8 (Arm.r (.GPR (rnum n)) (pcx s 16 P X))) := by
  unfold slotStoreAt
  split
  · rename_i ho
    refine ⟨Arm.r .PC s, Arm.r (.GPR 16#5) s, ?_⟩
    rw [pcx_self]
    exact ExecAll.one (fun env => exec_store_int ctx env hn h8 ho halign) (stSt_err _ _ _ _)
      (stSt_prog _ _ _ _)
  · obtain ⟨P, hA⟩ := execAll_spAddrX16 ctx off s
    exact ⟨P, _, ExecAll.append hA (ExecAll.one
      (fun env => exec_store_int_x16 ctx env hn (pcx_x16 s P off)) (stSt_err _ _ _ _) (stSt_prog _ _ _ _))⟩

theorem exec_slotLoadAt_int (ctx : FnCtx) {n off : Nat} (hn : n < 29) (h8 : off % 8 = 0)
    {s : Arm.ArmState} (halign : Arm.CheckSPAlignment s) :
    ∃ P X, ExecAll ctx (slotLoadAt .int (.x n) off) s (ldIntSt (pcx s 16 P X) off n) := by
  unfold slotLoadAt
  split
  · rename_i ho
    refine ⟨Arm.r .PC s, Arm.r (.GPR 16#5) s, ?_⟩
    rw [pcx_self]
    exact ExecAll.one (fun env => exec_load_int ctx env hn h8 ho halign) (ldIntSt_err _ _ _)
      (ldIntSt_prog _ _ _)
  · obtain ⟨P, hA⟩ := execAll_spAddrX16 ctx off s
    exact ⟨P, _, ExecAll.append hA (ExecAll.one
      (fun env => exec_load_int_x16 ctx env hn (pcx_x16 s P off)) (ldIntSt_err _ _ _) (ldIntSt_prog _ _ _))⟩

theorem exec_slotStoreAt_float (ctx : FnCtx) {n off : Nat} (hn : n < 32) (h16 : off % 16 = 0)
    {s : Arm.ArmState} (halign : Arm.CheckSPAlignment s) :
    ∃ P X, ExecAll ctx (slotStoreAt .float (.v n) off) s
      (stSt (pcx s 16 P X) off 16 (Arm.r (.SFP (rnum n)) (pcx s 16 P X))) := by
  unfold slotStoreAt
  split
  · rename_i ho
    refine ⟨Arm.r .PC s, Arm.r (.GPR 16#5) s, ?_⟩
    rw [pcx_self]
    exact ExecAll.one (fun env => exec_store_float ctx env hn h16 ho halign) (stSt_err _ _ _ _)
      (stSt_prog _ _ _ _)
  · obtain ⟨P, hA⟩ := execAll_spAddrX16 ctx off s
    exact ⟨P, _, ExecAll.append hA (ExecAll.one
      (fun env => exec_store_float_x16 ctx env hn (pcx_x16 s P off)) (stSt_err _ _ _ _) (stSt_prog _ _ _ _))⟩

theorem exec_slotLoadAt_float (ctx : FnCtx) {n off : Nat} (hn : n < 32) (h16 : off % 16 = 0)
    {s : Arm.ArmState} (halign : Arm.CheckSPAlignment s) :
    ∃ P X, ExecAll ctx (slotLoadAt .float (.v n) off) s (ldFSt (pcx s 16 P X) off n) := by
  unfold slotLoadAt
  split
  · rename_i ho
    refine ⟨Arm.r .PC s, Arm.r (.GPR 16#5) s, ?_⟩
    rw [pcx_self]
    exact ExecAll.one (fun env => exec_load_float ctx env hn h16 ho halign) (ldFSt_err _ _ _)
      (ldFSt_prog _ _ _)
  · obtain ⟨P, hA⟩ := execAll_spAddrX16 ctx off s
    exact ⟨P, _, ExecAll.append hA (ExecAll.one
      (fun env => exec_load_float_x16 ctx env hn (pcx_x16 s P off)) (ldFSt_err _ _ _) (ldFSt_prog _ _ _))⟩

end Backend.Proof
