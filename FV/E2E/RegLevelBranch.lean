import FV.E2E.RegLevelArgs

/-!
# Branches on the machine (M6)

PC-relative branches (`b`, `b.cond`, `cbz`/`cbnz`, `tbz`/`tbnz`) step to their target label
or to the next line (`step_branch`, from M5's label resolution `Insn.toArmInst_pcRel`); the
branch condition of the decoded instruction is the Arm model's (`brCond_*`). A machine state at
a block's label is related to the entry of that block (`q_entry`, via `emit_block`).
-/

namespace Backend.Proof

open Backend E2E

/-! ## The Arm model on branches -/

/-- The branch condition of a decoded PC-relative branch. -/
def brCond : Arm.ArmInst → Arm.ArmState → Bool
  | .BR (.Uncond_branch_imm _), _ => true
  | .BR (.Cond_branch_imm x), s => Arm.BR.Cond_branch_imm_inst.condition_holds x s
  | .BR (.Compare_branch x), s => Arm.BR.Compare_branch_inst.condition_holds x s
  | .BR (.Test_branch x), s => Arm.BR.Test_branch_inst.condition_holds x s
  | _, _ => false

theorem exec_brInsn {env : Env} {i : Insn} {l : Lbl} {a : Arm.ArmInst}
    (hi : i = .b l ∨ (∃ c, i = .bcond c l) ∨ (∃ nz w r, i = .cbz nz w r l) ∨ (∃ nz r bit, i = .tbz nz r bit l))
    (h : i.toArmInst env = .ok a) (s : Arm.ArmState) :
    ∃ d, a.pcRelOffset? = some d ∧
      Arm.exec_inst a s = Arm.w .PC (if brCond a s then Arm.r .PC s + BitVec.ofInt 64 d
        else Arm.r .PC s + 4#64) s := by
  simp only [Insn.toArmInst, Backend.map_eq_ok] at h
  obtain ⟨b, hb, rfl⟩ := h
  rcases hi with rfl | ⟨c, rfl⟩ | ⟨nz, w, r, rfl⟩ | ⟨nz, r, bit, rfl⟩
  · simp only [Insn.armFields, Backend.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at hb
    obtain ⟨v, hv, rfl⟩ := hb
    refine ⟨_, rfl, ?_⟩
    simp [Arm.ArmInst.norm, Arm.exec_inst, Arm.BR.exec_uncond_branch_imm, Arm.write_pc, Arm.read_pc,
      brCond, Arm.BR.Uncond_branch_imm_inst.branch_taken_pc, Backend.signExtend_append_zero]
  · simp only [Insn.armFields, Backend.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at hb
    obtain ⟨v, hv, rfl⟩ := hb
    refine ⟨_, rfl, ?_⟩
    simp [Arm.ArmInst.norm, Arm.exec_inst, Arm.BR.exec_cond_branch_imm, Arm.write_pc, Arm.read_pc,
      brCond, Arm.BR.Cond_branch_imm_inst.branch_taken_pc, Backend.signExtend_append_zero]
    split <;> simp_all
  · simp only [Insn.armFields, Backend.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at hb
    obtain ⟨v, hv, _, _, rfl⟩ := hb
    refine ⟨_, rfl, ?_⟩
    simp [Arm.ArmInst.norm, Arm.exec_inst, Arm.BR.exec_compare_branch, Arm.write_pc, Arm.read_pc,
      brCond, Arm.BR.Compare_branch_inst.branch_taken_pc, Backend.signExtend_append_zero]
    split <;> simp_all
  · simp only [Insn.armFields] at hb
    split at hb
    · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hb
    · simp only [Backend.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at hb
      obtain ⟨v, hv, _, _, rfl⟩ := hb
      refine ⟨_, rfl, ?_⟩
      simp [Arm.ArmInst.norm, Arm.exec_inst, Arm.BR.exec_test_branch, Arm.write_pc, Arm.read_pc,
        brCond, Arm.BR.Test_branch_inst.branch_taken_pc, Backend.signExtend_append_zero]
      split <;> simp_all
theorem brCond_bcond {env : Env} {c : Cond} {l : Lbl} {a : Arm.ArmInst}
    (h : (Insn.bcond c l).toArmInst env = .ok a) (s : Arm.ArmState) :
    brCond a s = Arm.ConditionHolds c.bits s := by
  simp only [Insn.toArmInst, Backend.map_eq_ok] at h
  obtain ⟨b, hb, rfl⟩ := h
  simp only [Insn.armFields, Backend.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at hb
  obtain ⟨v, hv, rfl⟩ := hb
  rfl

theorem brCond_cbz {env : Env} {nz w : Bool} {n : Nat} (hn : n ≤ 30) {l : Lbl} {a : Arm.ArmInst}
    (h : (Insn.cbz nz w (.x n) l).toArmInst env = .ok a) (s : Arm.ArmState) :
    brCond a s = ((if w then Arm.r (.GPR (rnum n)) s == 0 else (Arm.r (.GPR (rnum n)) s).setWidth 32 == 0) != nz) := by
  simp only [Insn.toArmInst, Backend.map_eq_ok] at h
  obtain ⟨b, hb, rfl⟩ := h
  simp only [Insn.armFields, Backend.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at hb
  obtain ⟨v, hv, R, hR, rfl⟩ := hb
  simp only [Reg.encZR, hn, ite_true, pure, Except.pure, Except.ok.injEq] at hR
  subst hR
  have h31 : BitVec.ofNat 5 n ≠ 31#5 := by
    intro e; have := congrArg BitVec.toNat e; simp at this; omega
  cases w <;> cases nz <;>
    simp [Arm.ArmInst.norm, brCond, Arm.BR.Compare_branch_inst.condition_holds, b1, Arm.read_gpr_zr,
      Arm.read_gpr, h31, rnum] <;> rfl

theorem extract1 (x : BitVec 64) (i : Nat) :
    BitVec.extractLsb' i 1 x = BitVec.ofBool (x.getLsbD i) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have : j = 0 := by omega
  subst this
  simp

theorem brCond_tbz {env : Env} {nz : Bool} {n bit : Nat} (hn : n ≤ 30) {l : Lbl} {a : Arm.ArmInst}
    (h : (Insn.tbz nz (.x n) bit l).toArmInst env = .ok a) (s : Arm.ArmState) :
    brCond a s = ((Arm.r (.GPR (rnum n)) s).getLsbD bit == nz) := by
  simp only [Insn.toArmInst, Backend.map_eq_ok] at h
  obtain ⟨b, hb, rfl⟩ := h
  simp only [Insn.armFields] at hb
  split at hb
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hb
  rename_i hbit
  simp only [Backend.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at hb
  obtain ⟨v, hv, R, hR, rfl⟩ := hb
  simp only [Reg.encZR, hn, ite_true, pure, Except.pure, Except.ok.injEq] at hR
  subst hR
  have h31 : BitVec.ofNat 5 n ≠ 31#5 := by
    intro e; have := congrArg BitVec.toNat e; simp at this; omega
  have hb : (BitVec.ofNat 1 (bit / 32) ++ BitVec.ofNat 5 (bit % 32)).toNat = bit := by
    rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (BitVec.isLt _), Nat.shiftLeft_eq]
    simp only [BitVec.toNat_ofNat]
    omega
  cases nz <;>
    simp [Arm.ArmInst.norm, brCond, Arm.BR.Test_branch_inst.condition_holds, b1, Arm.read_gpr_zr,
      Arm.read_gpr, h31, rnum, hb, Arm.BitVec.lsb, extract1] <;>
    cases (Arm.r (Arm.StateField.GPR (BitVec.ofNat 5 n)) s).getLsbD bit <;> decide

theorem ofNat_add_ofInt_sub (a b : Nat) :
    BitVec.ofNat 64 a + BitVec.ofInt 64 ((b : Int) - a) = BitVec.ofNat 64 b := by
  rw [← BitVec.ofInt_natCast (w := 64) a, ← BitVec.ofInt_add, ← BitVec.ofInt_natCast (w := 64) b]
  congr 1
  omega

/-! ## One branch step -/

theorem RL.pcOf_succ_ins {R : RL} {j : Nat} {i : Insn} {t : Option Clif.TrapCode}
    (hj : R.L[j]? = some (.ins i t)) : R.pcOf (j + 1) = R.pcOf j + 4#64 := by
  simp only [RL.pcOf]
  rw [lineOffset_succ _ _ _ hj, BitVec.add_assoc]
  congr 1
  simp [Line.size, BitVec.ofNat_add]

/-- **A branch step**: the machine goes to (the offset of) a line defining the target label if
the decoded branch's condition holds, else to the next line; nothing else changes. -/
theorem step_branch {R : RL} (hR : R.Wf) {s : Arm.ArmState} {j : Nat} {i : Insn} {l : Lbl}
    (hj : R.L[j]? = some (.ins i none))
    (hi : i = .b l ∨ (∃ c, i = .bcond c l) ∨ (∃ nz w r, i = .cbz nz w r l) ∨
      (∃ nz r bit, i = .tbz nz r bit l))
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j)
    (herr : Arm.r .ERR s = .None) :
    ∃ a jl, i.toArmInst (R.envOf j) = .ok a ∧ R.L[jl]? = some (.label l) ∧
      R.step s = Arm.w .PC (if brCond a s then R.pcOf jl else R.pcOf (j + 1)) s := by
  have hhook : i.hooked = false := by
    rcases hi with rfl | ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;> rfl
  obtain ⟨a, ha, hstep⟩ := armStepX_ins (X := R.X) (H := R.H) hR.layout hR.lm hR.fit hj hhook hprog
    hpc herr
  have hspec : ∃ reach align, i.pcRelSpec? = some (l, reach, align) := by
    rcases hi with rfl | ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;> exact ⟨_, _, rfl⟩
  obtain ⟨reach, align, hs⟩ := hspec
  obtain ⟨o, hlo, hoff, -⟩ := Insn.toArmInst_pcRel ha hs
  obtain ⟨jl, hjl, hoj⟩ := (labelOffsets_spec hR.lm l o).mp hlo
  obtain ⟨d, hd, hex⟩ := exec_brInsn hi ha s
  rw [hoff] at hd
  cases hd
  refine ⟨a, jl, ha, hjl, ?_⟩
  simp only [RL.step]
  rw [hstep, hex, hpc, RL.pcOf_succ_ins hj]
  congr 2
  simp only [RL.pcOf, RL.L, BitVec.add_assoc]
  rw [ofNat_add_ofInt_sub, hoj]

/-! ## States differing only in the pc -/

theorem locVal_w_pc (fr : RAFrame) (s : Arm.ArmState) (v : BitVec 64) (l : Loc) :
    locVal fr (Arm.w .PC v s) l = locVal fr s l := by
  cases l with
  | reg r =>
    cases r <;> simp [locVal, regVal, Arm.r_of_w_different]
  | stack k c =>
    simp only [locVal, spOf, Arm.r_of_w_different (show Arm.StateField.GPR 31#5 ≠ .PC by simp),
      Arm.read_mem_bytes_of_w]
  | save r =>
    simp only [locVal, spOf, Arm.r_of_w_different (show Arm.StateField.GPR 31#5 ≠ .PC by simp),
      Arm.read_mem_bytes_of_w]

theorem StRel.pc {R : RL} {s : Arm.ArmState} {m : Loc → CV} {w : Arm.ArmState} (h : StRel R s m w)
    (v : BitVec 64) : StRel R (Arm.w .PC v s) m w where
  store := fun l hl hL => by rw [locVal_w_pc]; exact h.store l hl hL
  world := ⟨fun f hf => by
      rw [Arm.r_of_w_different (by intro e; subst e; exact hf trivial)]; exact h.world.1 f hf,
    fun a ha => by rw [Arm.mem_w_of_mem_eq rfl]; exact h.world.2.1 a ha,
    by rw [Arm.w_program]; exact h.world.2.2⟩
  err := by rw [Arm.r_of_w_different (by simp)]; exact h.err
  prog := by rw [Arm.w_program]; exact h.prog
  sp := by simp only [spOf]; rw [Arm.r_of_w_different (by simp)]; exact h.sp
  align := align_of_sp (by simp only [spOf]; rw [Arm.r_of_w_different (by simp)]) h.align
  fplr := fun hf => by rw [Arm.read_mem_bytes_of_w]; exact h.fplr hf
  code := fun k w hk => by rw [Arm.read_mem_bytes_of_w]; exact h.code k w hk

/-! ## Entering a block -/

/-- The checker accepts every block's item list from its start. -/
theorem itemsChecked_block {R : RL} (hR : R.Wf) {t : Nat} {vb : VBlock} {items : Array RItem}
    (hvb : R.vc.blocks[t]? = some vb) (hit : R.rf.blocks[t]? = some items) :
    ItemsChecked R vb items.toList := by
  obtain ⟨c, ins, hc⟩ := checked_of_checkAlloc hR.check
  obtain ⟨a, out, -, hrb, -⟩ := verifyBlock_ok (hc.blocks t (Array.getElem?_eq_some_iff.mp hvb).1)
  obtain ⟨vb', items', hvb', hit', hrun⟩ := runBlock_ok hrb
  rw [hc.vc_eq, hvb] at hvb'
  cases hvb'
  rw [hc.rf_eq, hit] at hit'
  cases hit'
  exact ⟨c, 0, a, out, hc.rf_eq, hc.vc_eq, hrun⟩

/-- **Entering a block** (other than the entry block): at the offset of the block's label, the
machine is at the start of the block's items. -/
theorem q_entry {R : RL} (hR : R.Wf) {t : Nat} {vb : VBlock} {items : Array RItem} (ht : t ≠ 0)
    (hvb : R.vc.blocks[t]? = some vb) (hit : R.rf.blocks[t]? = some items)
    {s : Arm.ArmState} {m : Loc → CV} {w : Arm.ArmState} {jl : Nat}
    (hjl : R.L[jl]? = some (.label (.block vb.label))) (hpc : Arm.r .PC s = R.pcOf jl)
    (hst : StRel R s m w) : Q R s (.run ⟨t, items.toList, m, w⟩) := by
  obtain ⟨⟨-, -, -, hbl⟩, -⟩ := lowerRFunc_ok hR.alloc
  obtain ⟨code, hcode, haf⟩ := hbl t vb items hvb hit
  obtain ⟨body, psF, hb, -, hblk⟩ := emit_block hR.emit
  obtain ⟨body', hb'⟩ := hR.psF
  have hk : R.ctx = ⟨R.fa.k, R.af.slotBase⟩ := rfl
  rw [hk, hb] at hb'
  simp only [Except.ok.injEq, Prod.mk.injEq] at hb'
  obtain ⟨-, rfl⟩ := hb'
  obtain ⟨j0, ls, ps1, ps2, T, hj0, hdrop, hls, htr⟩ := hblk t _ _ haf
  simp only [ht, ite_false, List.nil_append, List.toList_toArray] at hls
  refine ⟨j0 + 1, vb, items, [], code, ls, ps1, ps2, T, hvb, hit, rfl,
    itemsChecked_block hR hvb hit, hcode, hls, htr, hdrop, ?_, hst⟩
  rw [hpc]
  simp only [RL.pcOf, RL.L]
  rw [lineOffset_succ _ _ _ hj0]
  have e1 := labelOffsets_label hR.lm hj0
  have e2 := labelOffsets_label hR.lm hjl
  rw [e1] at e2
  simp only [Option.some.injEq] at e2
  simp only [Line.size, Nat.add_zero, RL.L] at e2 ⊢
  rw [e2]

end Backend.Proof
