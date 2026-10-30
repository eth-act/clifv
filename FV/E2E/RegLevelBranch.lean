import FV.E2E.RegLevelFwd
import FV.E2E.RegLevelGoodX

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
      (∃ nz r bit, i = .tbz nz r bit l)) (hl : l ≠ .skip)
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
  rw [Env.target_of_ne hl] at hlo
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

/-- **The inverted short branch of a relaxed branch** (target `.+8`, over the `b` at line
`j + 1`): the machine goes to line `j + 2` if the decoded branch's condition holds, else to
line `j + 1`; nothing else changes. -/
theorem step_skip {R : RL} (hR : R.Wf) {s : Arm.ArmState} {j : Nat} {i x : Insn}
    (hj : R.L[j]? = some (.ins i none)) (hj1 : R.L[j + 1]? = some (.ins x none))
    (hi : (∃ c, i = .bcond c .skip) ∨ (∃ nz w r, i = .cbz nz w r .skip) ∨
      (∃ nz r bit, i = .tbz nz r bit .skip))
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j)
    (herr : Arm.r .ERR s = .None) :
    ∃ a, i.toArmInst (R.envOf j) = .ok a ∧
      R.step s = Arm.w .PC (if brCond a s then R.pcOf (j + 2) else R.pcOf (j + 1)) s := by
  have hhook : i.hooked = false := by
    rcases hi with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;> rfl
  obtain ⟨a, ha, hstep⟩ := armStepX_ins (X := R.X) (H := R.H) hR.layout hR.lm hR.fit hj hhook hprog
    hpc herr
  have hspec : ∃ reach align, i.pcRelSpec? = some (.skip, reach, align) := by
    rcases hi with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;> exact ⟨_, _, rfl⟩
  obtain ⟨reach, align, hs⟩ := hspec
  obtain ⟨o, hlo, hoff, -⟩ := Insn.toArmInst_pcRel ha hs
  simp only [Env.target, Option.some.injEq] at hlo
  obtain ⟨d, hd, hex⟩ := exec_brInsn (.inr hi) ha s
  rw [hoff] at hd
  cases hd
  refine ⟨a, ha, ?_⟩
  simp only [RL.step]
  rw [hstep, hex, hpc, RL.pcOf_succ_ins hj]
  congr 2
  rw [show j + 2 = j + 1 + 1 from rfl, RL.pcOf_succ_ins hj1, RL.pcOf_succ_ins hj, ← hlo]
  simp only [RL.envOf, RL.pcOf, RL.L, BitVec.add_assoc]
  congr 1
  rw [show ((lineOffset R.fa.lines.toList j + 8 : Nat) : Int) - (lineOffset R.fa.lines.toList j : Nat) = 8
    by omega]
  rfl

/-- **A branch line's state** with the body's `sp`: `GoodX` (the step goes to the target label or
the next line). -/
theorem step_branchX {R : RL} (hR : R.Wf) {s : Arm.ArmState} {j : Nat} {i : Insn} {l : Lbl}
    (hj : R.L[j]? = some (.ins i none))
    (hi : i = .b l ∨ (∃ c, i = .bcond c l) ∨ (∃ nz w r, i = .cbz nz w r l) ∨
      (∃ nz r bit, i = .tbz nz r bit l)) (hl : l ≠ .skip)
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j)
    (herr : Arm.r .ERR s = .None) (hsp : spOf s = R.spB) : R.GoodX s := by
  obtain ⟨a, jl, -, hjl, hstep⟩ := step_branch hR hj hi hl hprog hpc herr
  have hh : i.hooked = false ∧ i.tlsTail = false ∧ i.pairFirst = false ∧ i.loads = false := by
    rcases hi with rfl | ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;> exact ⟨rfl, rfl, rfl, rfl⟩
  refine RL.goodX_ofIns hR hj hpc hh.1 hh.2.1 (.inr hsp) herr hprog ?_
    (RL.readsAt_noLoad hR hj hpc hh.2.2.2)
  rw [hstep]
  split
  · exact RL.nextOk_label hjl (Arm.r_of_w_same ..)
  · exact RL.nextOk_succ hj hh.2.2.1 (Arm.r_of_w_same ..)

/-- **The inverted short branch of a relaxed branch** with the body's `sp`: `GoodX` (the step
goes past the next line, which is not the first word of an `adrp` pair, or to it). -/
theorem step_skipX {R : RL} (hR : R.Wf) {s : Arm.ArmState} {j : Nat} {i x : Insn}
    (hj : R.L[j]? = some (.ins i none)) (hj1 : R.L[j + 1]? = some (.ins x none))
    (hi : (∃ c, i = .bcond c .skip) ∨ (∃ nz w r, i = .cbz nz w r .skip) ∨
      (∃ nz r bit, i = .tbz nz r bit .skip)) (hx : x.pairFirst = false)
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j)
    (herr : Arm.r .ERR s = .None) (hsp : spOf s = R.spB) : R.GoodX s := by
  obtain ⟨a, -, hstep⟩ := step_skip hR hj hj1 hi hprog hpc herr
  have hh : i.hooked = false ∧ i.tlsTail = false ∧ i.pairFirst = false ∧ i.loads = false := by
    rcases hi with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;> exact ⟨rfl, rfl, rfl, rfl⟩
  refine RL.goodX_ofIns hR hj hpc hh.1 hh.2.1 (.inr hsp) herr hprog ?_
    (RL.readsAt_noLoad hR hj hpc hh.2.2.2)
  rw [hstep]
  split
  · exact RL.nextOk_succ hj1 hx (Arm.r_of_w_same ..)
  · exact RL.nextOk_succ hj hh.2.2.1 (Arm.r_of_w_same ..)

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
  gkeep := fun a ha => by rw [Arm.mem_w_of_mem_eq rfl]; exact h.gkeep a ha
  fp := fun hf => by simp only [xreg]; rw [Arm.r_of_w_different (by simp)]; exact h.fp hf

/-! ## Entering a block -/

/-- The checker accepts every block's item list from its start. -/
theorem itemsChecked_block {R : RL} (hR : R.Wf) {t : Nat} {vb : VBlock} {items : Array RItem}
    (hvb : R.vc.blocks[t]? = some vb) (hit : R.rf.blocks[t]? = some items) :
    ItemsChecked R vb items.toList := by
  obtain ⟨c, ins, _, hc, -⟩ := hR.check
  obtain ⟨a, out, -, hrb, -⟩ := verifyBlock_ok (hc.blocks t (Array.getElem?_eq_some_iff.mp hvb).1)
  obtain ⟨vb', items', hvb', hit', hrun⟩ := runBlock_ok hrb
  rw [hc.vc_eq, hvb] at hvb'
  cases hvb'
  rw [hc.rf_eq, hit] at hit'
  cases hit'
  exact ⟨c, 0, a, out, hc.rf_eq, hc.vc_eq, hrun⟩

/-- **At the label line of a block** (other than the entry) whose segment was checked (it
forwards nowhere or is trusted, `planOwn`): the machine is at the start of the block's items
(`Qs`). -/
theorem qs_entry {R : RL} (hR : R.Wf) {t : Nat} {vb : VBlock} {items : Array RItem} (ht : t ≠ 0)
    (hvb : R.vc.blocks[t]? = some vb) (hit : R.rf.blocks[t]? = some items)
    (ho : (R.af.fwd? vb.label).isNone = true ∨ planOwn R.fa.k R.af vb.label = true)
    {s : Arm.ArmState} {m : Loc → CV} {w : Arm.ArmState} {jl : Nat}
    (hjl : R.L[jl]? = some (.label (.block vb.label))) (hpc : Arm.r .PC s = R.pcOf jl)
    (hst : StRel R s m w) : Qs R s t items.toList m w := by
  obtain ⟨⟨-, -, -, hbl⟩, -⟩ := lowerRFunc_ok hR.alloc
  obtain ⟨code, hcode, haf⟩ := hbl t vb items hvb hit
  obtain ⟨p, hp, hL, hseg⟩ := emit_seg hR.emit
  obtain ⟨i, sg, o, -, ps1, psm, ps2, hs, ho', hidx, hlab, -, -, -, e1, e2, hpre, -⟩ :=
    hseg t _ _ haf
  simp only [ht, ite_false, List.nil_append, List.toList_toArray] at e1 e2
  obtain ⟨A, hA, hX⟩ := segX_get hp hs ho'
  rw [hidx] at hX
  obtain ⟨p', hp', hps⟩ := hR.psF
  rw [hp] at hp'
  cases hp'
  have hPL : planLines R.fa.k R.af = p.lines := by simp [planLines, hp]
  have hRL : R.L = relaxLines R.far p.lines := hL
  -- the block's label line
  have e : p.lines = (A ++ [Line.label (.block sg.label)] ++ (sg.body ++ o)) ++
      (segLines (p.segs.drop (i + 1)) (p.outs.drop (i + 1)) ++ trapLines p.ps) := by
    rw [hA]; simp
  have hlbl : p.lines[A.length]? = some (.label (.block vb.label)) := by
    rw [hA, ← hlab, List.append_assoc, List.cons_append]; exact getElem?_mid _ _ _
  have r1 := relax_label (F := R.far) hlbl
  rw [← hRL] at r1
  have hj : jl = rix R.far p.lines A.length := labelOffsets_uniq hR.lm hjl r1.1
  subst hj
  refine ⟨rix R.far p.lines (A.length + 1), vb, items, [], code, sg.body, ps1, psm, ps2,
    (sg, o, A.length + 1 + sg.body.length + o.length), hvb, hit, rfl,
    itemsChecked_block hR hvb hit, hcode, e1, e2, by rw [← hps]; exact hpre, ?_, ?_, hst, hX,
    segChecked_of hp hX (by rw [hlab]; exact ho)⟩
  · have d1 : p.lines.drop (A.length + 1) = (sg.body ++ o) ++
        (segLines (p.segs.drop (i + 1)) (p.outs.drop (i + 1)) ++ trapLines p.ps) := by
      rw [e, List.append_assoc]; exact List.drop_left' (by simp)
    have d2 : p.lines.drop (A.length + 1 + sg.body.length + o.length) =
        segLines (p.segs.drop (i + 1)) (p.outs.drop (i + 1)) ++ trapLines p.ps := by
      rw [e]; exact List.drop_left' (by simp; omega)
    rw [hPL, hRL, relax_drop, relax_drop, d1, d2, relaxLines_append]
  · rw [hpc, r1.2]
    simp only [RL.pcOf]
    rw [lineOffset_succ _ _ _ r1.1]
    simp [Line.size]

/-- **Entering a block** (other than the entry) at a line that represents its label (`RepL`:
the label lines from there on include the block's own label, which it may have only if it
forwards nowhere or is trusted, or the block forwards to a block the line represents): `QE`. -/
theorem qe_entry {R : RL} (hR : R.Wf) {s : Arm.ArmState} {m : Loc → CV} {w : Arm.ArmState}
    (hst : StRel R s m w) {l : Label} {jl : Nat}
    (hrep : RepL R.af (planOwn R.fa.k R.af) R.L l jl) (hpc : Arm.r .PC s = R.pcOf jl) :
    ∀ {t : Nat} {vb : VBlock} {items : Array RItem}, t ≠ 0 → R.vc.blocks[t]? = some vb →
      vb.label = l → R.rf.blocks[t]? = some items → QE R s m w t := by
  revert hpc
  induction hrep with
  | here ho hL =>
    intro hpc t vb items ht hvb hl hit
    subst hl
    exact .std hit (qs_entry hR ht hvb hit ho hL hpc hst)
  | @skip l j l' ho hL _ ih =>
    intro hpc
    refine ih ?_
    rw [hpc]
    simp only [RL.pcOf]
    rw [lineOffset_succ _ _ _ hL]
    simp [Line.size]
  | @fwd l x j hx _ ih =>
    intro hpc t vb items ht hvb hl hit
    obtain ⟨b', vb', items', allocs, regs, i, bx, vbx, itx, hvb', hl', hit', -, hil, hal, hins,
      hasg, hsucc, hvbx, hlx, hitx, hbx0⟩ := RL.fwd_block hR hx
    obtain rfl : t = b' := RL.label_inj hR hvb hit hvb' hit' (hl.trans hl'.symm)
    rw [hvb] at hvb'
    cases hvb'
    rw [hit] at hit'
    cases hit'
    exact .fwd hvb (by rw [hl]; exact hx) hit hil hal hins hasg hsucc hvbx hlx
      (ih hpc hbx0 hvbx hlx hitx)

/-- **Entering a block** (other than the entry) at a line that represents its label (`RepL`).
The statement before #553 took the block's own label line; `MachBuffer`'s branch
simplification (#553) removes or aliases a forwarding block's `b`, so a block is entered at a
line representing it, possibly through forwarding blocks (`QE`). -/
theorem q_entry {R : RL} (hR : R.Wf) {t : Nat} {vb : VBlock} {items : Array RItem} (ht : t ≠ 0)
    (hvb : R.vc.blocks[t]? = some vb) (hit : R.rf.blocks[t]? = some items)
    {s : Arm.ArmState} {m : Loc → CV} {w : Arm.ArmState} {jl : Nat}
    (hrep : RepL R.af (planOwn R.fa.k R.af) R.L vb.label jl) (hpc : Arm.r .PC s = R.pcOf jl)
    (hst : StRel R s m w) : Q R s (.run ⟨t, items.toList, m, w⟩) :=
  .inr ⟨items, hit, rfl, qe_entry hR hst hrep hpc ht hvb rfl hit⟩

end Backend.Proof
