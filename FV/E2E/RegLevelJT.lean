import FV.Backend.Proof.RegallocMem
import FV.Backend.Proof.RegallocTac
import FV.Backend.Proof.IselExtern
import FV.E2E.RegLevelNext

/-!
# Jump tables on the machine (M6)

`jtSequence dflt ts ridx t1 t2` is emitted as

```
b.hs dflt; csel t2, xzr, ridx, hs; adr t1, jt; ldrsw t2, [t1, t2, uxtw #2]; add t1, t1, t2;
br t1; jt: .word ts[0] - jt; …
```

`jt_machine`: with `hs` the machine reaches the default block's label; otherwise, for an index
`i < ts.length` (low 32 bits of `ridx`), it reads word `i` of the table from memory (the code
words are readable as data: `StRel.code`) and reaches the label of `ts[i]`, having changed only
the pc and the temporaries. `realizes_jt`: the `Realizes` case (the temporaries' values are
havocked by `MStep`, `HavocOuts`).
-/

namespace Backend.Proof

open Backend E2E

/-! ## Exec lemmas -/

theorem exec_csel_hs (env : Env) {d r : Nat} (hd : d < 29) (hr : r < 29) (s : Arm.ArmState) :
    ∃ a, (Insn.csel (.x d) .xzr (.x r) .hs).toArmInst env = .ok a ∧
      Arm.exec_inst a s = Arm.w (.GPR (rnum d))
        (if Arm.ConditionHolds Cond.hs.bits s then 0#64 else Arm.r (.GPR (rnum r)) s)
        (Arm.w .PC (Arm.r .PC s + 4#64) s) := by
  refine ⟨_, by simp [csimp_rules, show d ≤ 30 by omega, show r ≤ 30 by omega, pure, Except.pure]; rfl, ?_⟩
  simp [csimp_rules, ne31_of hd, ne31_of hr]

theorem exec_add64 (env : Env) {d n m : Nat} (hd : d < 29) (hn : n < 29) (hm : m < 29)
    (s : Arm.ArmState) :
    ∃ a, (Insn.aluRRR .add true (.x d) (.x n) (.x m)).toArmInst env = .ok a ∧
      Arm.exec_inst a s = Arm.w (.GPR (rnum d))
        (Arm.r (.GPR (rnum n)) s + Arm.r (.GPR (rnum m)) s) (Arm.w .PC (Arm.r .PC s + 4#64) s) := by
  refine ⟨_, by simp [csimp_rules, show d ≤ 30 by omega, show n ≤ 30 by omega,
    show m ≤ 30 by omega, pure, Except.pure]; rfl, ?_⟩
  simp [csimp_rules, ne31_of hd, ne31_of hn, ne31_of hm, Arm.fst_AddWithCarry_eq_add]

theorem exec_br (env : Env) {d : Nat} (hd : d < 29) (s : Arm.ArmState) :
    ∃ a, (Insn.br (.x d)).toArmInst env = .ok a ∧
      Arm.exec_inst a s = Arm.w .PC (Arm.r (.GPR (rnum d)) s) s := by
  refine ⟨_, by simp [csimp_rules, show d ≤ 30 by omega, pure, Except.pure]; rfl, ?_⟩
  simp [csimp_rules, ne31_of hd, Arm.BR.exec_uncond_branch_reg]

theorem exec_adr {env : Env} {d : Nat} (hd : d < 29) {l : Lbl} {a : Arm.ArmInst}
    (ha : (Insn.adr (.x d) l).toArmInst env = .ok a) (s : Arm.ArmState) :
    ∃ o, a.pcRelOffset? = some o ∧ Arm.exec_inst a s = Arm.w .PC (Arm.r .PC s + 4#64)
      (Arm.w (.GPR (rnum d)) (Arm.r .PC s + BitVec.ofInt 64 o) s) := by
  simp only [Insn.toArmInst, Backend.map_eq_ok] at ha
  obtain ⟨b, hb, rfl⟩ := ha
  simp only [Insn.armFields, Backend.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at hb
  obtain ⟨v, hv, R, hR, rfl⟩ := hb
  simp [Reg.encZR, show d ≤ 30 by omega, pure, Except.pure] at hR
  subst hR
  refine ⟨_, rfl, ?_⟩
  simp [Arm.ArmInst.norm, Arm.exec_inst, Arm.DPI.exec_pc_rel_addressing, Arm.write_pc, Arm.read_pc,
    Arm.write_gpr_zr, Arm.write_gpr, ne31_of hd, rnum, BitVec.signExtend]

/-! ## The emitted lines -/

/-- The lines of an allocated `jtSequence` (`MInst.lines`). -/
def jtBody (d : Label) (ts : List Label) (r a b : Reg) (jt : Lbl) : List Line :=
  [.ins (.bcond .hs (.block d)), .ins (.csel b .xzr r .hs), .ins (.adr a jt),
   .ins (.load .sload32 b (.regScaledExtended a b .uxtw)), .ins (.aluRRR .add true a a b),
   .ins (.br a), .label jt] ++ ts.map fun l => .word (.block l) jt

/-- The lines of a `jtSequence` after its default branch (which relaxation may rewrite). -/
def jtTail (ts : List Label) (r a b : Reg) (jt : Lbl) : List Line :=
  [.ins (.csel b .xzr r .hs), .ins (.adr a jt),
   .ins (.load .sload32 b (.regScaledExtended a b .uxtw)), .ins (.aluRRR .add true a a b),
   .ins (.br a), .label jt] ++ ts.map fun l => .word (.block l) jt

theorem relaxLines_jtBody (f : Lbl → Bool) (d : Label) (ts : List Label) (r a b : Reg) (jt : Lbl) :
    relaxLines f (jtBody d ts r a b jt) =
      relaxLine f (.ins (.bcond .hs (.block d)) none) ++ jtTail ts r a b jt := by
  show relaxLines f (.ins (.bcond .hs (.block d)) none :: jtTail ts r a b jt) = _
  rw [relaxLines_cons]
  congr 1
  apply relaxLines_of_none
  intro ln hln
  simp only [jtTail, List.cons_append, List.nil_append, List.mem_cons, List.mem_map] at hln
  rcases hln with rfl | rfl | rfl | rfl | rfl | rfl | ⟨l, -, rfl⟩ <;> rfl

/-- The lines of a `jtSequence` after its default branch, before the table words. -/
def jtHead (ts : List Label) (r a b : Reg) (jt : Lbl) : List Line :=
  [.ins (.csel b .xzr r .hs), .ins (.adr a jt),
   .ins (.load .sload32 b (.regScaledExtended a b .uxtw)), .ins (.aluRRR .add true a a b),
   .ins (.br a), .label jt]

theorem jtTail_eq (ts : List Label) (r a b : Reg) (jt : Lbl) :
    jtTail ts r a b jt = jtHead ts r a b jt ++ ts.map (fun l => .word (.block l) jt) := rfl

/-! ## Offsets of the table words -/

theorem lineOffset_words {L : List Line} {j : Nat} {ws T : List Line}
    (hd : L.drop j = ws ++ T) (hw : ∀ ln ∈ ws, ∃ x y, ln = .word x y) :
    ∀ i, i ≤ ws.length → lineOffset L (j + i) = lineOffset L j + 4 * i := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    intro hi
    have hj : L[j + i]? = ws[i]? := by
      have := congrArg (·[i]?) hd
      simp only [List.getElem?_drop] at this
      rw [this, List.getElem?_append_left (by omega)]
    obtain ⟨ln, hln⟩ : ∃ ln, ws[i]? = some ln := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨x, y, rfl⟩ := hw _ (List.mem_of_getElem? hln)
    rw [hln] at hj
    rw [← Nat.add_assoc, lineOffset_succ _ _ _ hj, ih (by omega)]
    simp [Line.size]; omega

/-! ## The machine run -/

theorem getD_ok_encZR {n : Nat} (h : n < 29) : (Reg.x n).encZR.toOption.getD 31#5 = rnum n := by
  simp [Reg.encZR, show n ≤ 30 by omega, pure, Except.pure, Except.toOption, rnum]

theorem extend_uxtw2 (x : BitVec 64) :
    Arm.extend_reg x (Arm.decode_reg_extend ExtendOp.uxtw.bits) (log2 4) =
      BitVec.ofNat 64 (4 * (x.toNat % 2 ^ 32)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Arm.extend_reg, ExtendOp.bits, Arm.decode_reg_extend, Arm.ExtendType.unsigned_len, log2]
  simp [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.shiftLeft_eq]
  omega

/-- **The machine runs a jump table** (its default branch possibly relaxed and retargeted, the
table words possibly retargeted). The conclusions give a `RepL` instead of the target's own
label line: since #553 the branch check requires a representing label for every block-targeted
final line, so the emitted target may be an alias whose line represents the block. -/
theorem jt_machine {R : RL} (hR : R.Wf) {s : Arm.ArmState} {j0 : Nat} {d : Label}
    {ts : List Label} {nr na nb : Nat} (hr : nr < 29) (ha : na < 29) (hb : nb < 29)
    (hab : na ≠ nb) {jt : Lbl} (hjt : jt ≠ .skip) {bc : Line} {W T : List Line}
    (hdrop : R.L.drop j0 = relaxLine R.far bc ++
      (jtHead ts (.x nr) (.x na) (.x nb) jt ++ W ++ T))
    (hbc : ∃ l', bc = .ins (.bcond .hs l') none ∧
      RepLbl (planRep R.fa.k R.af) (blockLabelIdx (planLines R.fa.k R.af)) d l')
    (hW : ∀ (i : Nat) (l : Label), ts[i]? = some l → ∃ l', W[i]? = some (Line.word l' jt) ∧
      RepLbl (planRep R.fa.k R.af) (blockLabelIdx (planLines R.fa.k R.af)) l l')
    (hWl : W.length = ts.length)
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j0)
    (herr : Arm.r .ERR s = .None) (hspB : spOf s = R.spB)
    (hcode : ∀ k w, R.fb.words[k]? = some w →
      Arm.read_mem_bytes 4 (R.base + BitVec.ofNat 64 (4 * k)) s = w) :
    (Arm.ConditionHolds Cond.hs.bits s = true → ∃ n jl, iterN R.step n s = Arm.w .PC (R.pcOf jl) s ∧
      RepL R.af (planOwn R.fa.k R.af) R.L d jl ∧ ∀ i < n, R.GoodX (iterN R.step i s)) ∧
    (Arm.ConditionHolds Cond.hs.bits s = false → ∀ i l,
      (Arm.r (.GPR (rnum nr)) s).toNat % 2 ^ 32 = i → ts[i]? = some l →
      ∃ n jl s', iterN R.step n s = s' ∧ Arm.r .PC s' = R.pcOf jl ∧
        RepL R.af (planOwn R.fa.k R.af) R.L l jl ∧
        (∀ f, f ≠ .PC → f ≠ .GPR (rnum na) → f ≠ .GPR (rnum nb) → Arm.r f s' = Arm.r f s) ∧
        s'.mem = s.mem ∧ s'.program = s.program ∧
        ∀ i < n, R.GoodX (iterN R.step i s)) := by
  obtain ⟨l', rfl, hrepd⟩ := hbc
  have hnskip : l' ≠ .skip := by
    obtain ⟨l0, -, rfl, -, -⟩ := hrepd
    simp
  obtain ⟨n0, j1, hn0, hj1t, hj1f, -, hn1, hgx0⟩ := reach_rcbX hR hdrop (.inl ⟨.hs, rfl⟩) hnskip
    (Arm.ConditionHolds Cond.hs.bits s) (fun env a ha => brCond_bcond ha s)
    (fun _ env a ha => by
      simp only [Insn.invertTo] at ha
      rw [brCond_bcond ha s, condHolds_invert _ (by decide) (by decide)])
    hprog hpc herr hspB
  refine ⟨fun hhs => ?_, fun hhs i l hi hl => ?_⟩
  · obtain ⟨-, jl0, hjl0, hrep0⟩ := repLbl_line hR hrepd
    have hj1 : j1 = jl0 := labelOffsets_uniq hR.lm (hj1t hhs) hjl0
    refine ⟨n0, jl0, ?_, hrep0, hgx0⟩
    rw [hj1] at hn0; exact hn0
  have hdrop1 : R.L.drop j1 = jtHead ts (.x nr) (.x na) (.x nb) jt ++ W ++ T := by
    rw [hj1f hhs, ← List.drop_drop, hdrop, List.drop_left]
  have hL : ∀ t ln, (jtHead ts (.x nr) (.x na) (.x nb) jt ++ W ++ T)[t]? = some ln →
      R.L[j1 + t]? = some ln := by
    intro t ln ht
    have h1 : R.L.drop j1 = jtHead ts (.x nr) (.x na) (.x nb) jt ++ W ++ T := hdrop1
    have h2 := congrArg (·[t]?) h1
    simp only [List.getElem?_drop] at h2
    rw [h2]
    exact ht
  have h1 : R.L[j1]? = some (.ins (.csel (.x nb) .xzr (.x nr) .hs)) := hL 0 _ rfl
  have h2 : R.L[j1 + 1]? = some (.ins (.adr (.x na) jt)) := hL 1 _ rfl
  have h3 : R.L[j1 + 2]? = some (.ins (.load .sload32 (.x nb) (.regScaledExtended (.x na) (.x nb) .uxtw))) :=
    hL 2 _ rfl
  have h4 : R.L[j1 + 3]? = some (.ins (.aluRRR .add true (.x na) (.x na) (.x nb))) := hL 3 _ rfl
  have h5 : R.L[j1 + 4]? = some (.ins (.br (.x na))) := hL 4 _ rfl
  have h6 : R.L[j1 + 5]? = some (.label jt) := hL 5 _ rfl
  -- not taken: five more steps
  have hne : ∀ {x y : Nat}, x < 29 → y < 29 → x ≠ y → Arm.StateField.GPR (rnum x) ≠ .GPR (rnum y) :=
    fun hx hy hxy e => by injection e with e; exact rnum_ne (by omega) (by omega) hxy e
  have hnp : ∀ {x : Nat}, Arm.StateField.GPR (rnum x) ≠ .PC := fun e => by cases e
  have hpe : Arm.StateField.PC ≠ .ERR := by simp
  have hge : ∀ {x : Nat}, Arm.StateField.GPR (rnum x) ≠ .ERR := fun e => by cases e
  let X := Arm.r (.GPR (rnum nr)) s
  -- step 1: `b.hs` not taken
  have e1 : R.step s = Arm.w .PC (R.pcOf j1) s := by
    rw [hn1 hhs] at hn0; exact hn0
  -- step 2: csel
  let s1 := Arm.w .PC (R.pcOf (j1)) s
  have hp1 : s1.program = R.fb.program R.base := by simp [s1, Arm.w_program, hprog]
  have hr1 : Arm.r .ERR s1 = .None := by simp only [s1]; rw [Arm.r_of_w_different (Ne.symm hpe)]; exact herr
  obtain ⟨b1, hb1, hst1⟩ := armStepX_ins (X := R.X) (H := R.H) hR.layout hR.lm hR.fit h1 rfl hp1
    (by simp only [s1, Arm.r_of_w_same]; rfl) hr1
  obtain ⟨b1', hb1', hx1⟩ := exec_csel_hs (⟨lineOffset R.fa.lines.toList (j1), (R.lm[·]?)⟩) hb hr s1
  rw [hb1'] at hb1; cases hb1
  have hc1 : Arm.ConditionHolds Cond.hs.bits s1 = false := by
    rw [← hhs]; exact ConditionHolds_sameWorld (F := fun _ => True)
      (SameWorld.w_left (by simp [Masked]) (SameWorld.refl _ s)) _
  let s2 := Arm.w (.GPR (rnum nb)) X (Arm.w .PC (R.pcOf (j1 + 1)) s1)
  have e2 : R.step s1 = s2 := by
    simp only [RL.step]
    rw [hst1, hx1, hc1]
    simp only [s2, s1, Bool.false_eq_true, ite_false, Arm.r_of_w_same]
    rw [Arm.r_of_w_different hnp, RL.pcOf_succ_ins h1]
  have hp2 : s2.program = R.fb.program R.base := by simp [s2, Arm.w_program, hp1]
  have hr2 : Arm.r .ERR s2 = .None := by
    simp only [s2]; rw [Arm.r_of_w_different (Ne.symm hge), Arm.r_of_w_different (Ne.symm hpe)]; exact hr1
  have hpc2 : Arm.r .PC s2 = R.pcOf (j1 + 1) := by
    simp only [s2]; rw [Arm.r_of_w_different (Ne.symm hnp), Arm.r_of_w_same]
  -- step 3: adr
  obtain ⟨b2, hb2, hst2⟩ := armStepX_ins (X := R.X) (H := R.H) hR.layout hR.lm hR.fit h2 rfl hp2
    hpc2 hr2
  obtain ⟨o, ho, hx2⟩ := exec_adr ha hb2 s2
  obtain ⟨ojt, hojt, hoff, -⟩ := Insn.toArmInst_pcRel hb2 (t := jt) (reach := 2 ^ 20) (align := 1) rfl
  rw [hoff] at ho; cases ho
  have hojt' : ojt = lineOffset R.L (j1 + 5) := by
    have := labelOffsets_label hR.lm h6
    simp only [RL.L] at this ⊢
    rw [Env.target_of_ne hjt] at hojt
    simp only at hojt
    rw [hojt] at this; exact Option.some.inj this
  let A := R.base + BitVec.ofNat 64 ojt
  have hjtaddr : Arm.r .PC s2 + BitVec.ofInt 64 ((ojt : Int) - lineOffset R.fa.lines.toList (j1 + 1)) = A := by
    rw [hpc2]; simp only [RL.pcOf, RL.L, A]; rw [BitVec.add_assoc, ofNat_add_ofInt_sub]
  let s3 := Arm.w .PC (R.pcOf (j1 + 2)) (Arm.w (.GPR (rnum na)) A s2)
  have e3 : R.step s2 = s3 := by
    simp only [RL.step]
    rw [hst2, hx2, hjtaddr, hpc2, ← RL.pcOf_succ_ins h2]
  have hp3 : s3.program = R.fb.program R.base := by simp [s3, Arm.w_program, hp2]
  have hr3 : Arm.r .ERR s3 = .None := by
    simp only [s3]; rw [Arm.r_of_w_different (Ne.symm hpe), Arm.r_of_w_different (Ne.symm hge)]; exact hr2
  have hpc3 : Arm.r .PC s3 = R.pcOf (j1 + 2) := by simp only [s3, Arm.r_of_w_same]
  -- step 4: ldrsw
  obtain ⟨b3, hb3, hst3⟩ := armStepX_ins (X := R.X) (H := R.H) hR.layout hR.lm hR.fit h3 rfl hp3
    hpc3 hr3
  obtain ⟨b3', hb3', hx3⟩ := exec_load_line (⟨lineOffset R.fa.lines.toList (j1 + 2), (R.lm[·]?)⟩)
    R.ctx .sload32 (by simp) nb (by omega) (.regScaledExtended (.x na) (.x nb) .uxtw)
    ⟨show na ≤ 30 by omega, show nb ≤ 30 by omega, .inl rfl⟩ s3 (fun h => by cases h)
  rw [hb3'] at hb3; cases hb3
  have hXa3 : regX s3 (.x na) = A := by
    simp only [regX, s3]; rw [Arm.r_of_w_different hnp, Arm.r_of_w_same]
  have hXb3 : regX s3 (.x nb) = X := by
    simp only [regX, s3, s2]
    rw [Arm.r_of_w_different hnp, Arm.r_of_w_different (hne hb ha (Ne.symm hab)), Arm.r_of_w_same]
  have hmem3 : s3.mem = s.mem := by simp [s3, s2, s1, Arm.ArmState.mem_w_eq_mem]
  have haddr : AMode.addr R.ctx (.regScaledExtended (.x na) (.x nb) .uxtw) LoadOp.sload32.bytes s3 =
      A + BitVec.ofNat 64 (4 * i) := by
    simp only [AMode.addr, hXa3, hXb3, LoadOp.bytes]
    rw [extend_uxtw2, hi]
  -- the table word
  have hil : i < ts.length := (List.getElem?_eq_some_iff.1 hl).1
  obtain ⟨l2, hwiW, hrepw⟩ := hW i l hl
  have hhead : (jtHead ts (.x nr) (.x na) (.x nb) jt).length = 6 := by simp [jtHead]
  have hdW : R.L.drop (j1 + 6) = W ++ T := by
    rw [← List.drop_drop, hdrop1, List.append_assoc, ← hhead, List.drop_left]
  have hWw : ∀ ln ∈ W, ∃ x y, ln = .word x y := by
    intro ln hln
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hln
    have hkW : k < W.length := by
      simpa using (List.getElem?_eq_some_iff.1 hk).1
    rw [hWl] at hkW
    obtain ⟨l3, hl3⟩ : ∃ l3, ts[k]? = some l3 := ⟨_, List.getElem?_eq_getElem hkW⟩
    obtain ⟨l4, hw4, -⟩ := hW k l3 hl3
    rw [hw4] at hk
    exact ⟨_, _, (Option.some.inj hk).symm⟩
  have hwo := lineOffset_words hdW hWw i (by rw [hWl]; omega)
  have h7 : lineOffset R.L (j1 + 6) = lineOffset R.L (j1 + 5) := by
    rw [lineOffset_succ _ _ _ h6]; simp [Line.size]
  have hwi : R.L[j1 + 6 + i]? = some (Line.word l2 jt) := by
    have hcon := congrArg (·[i]?) hdW
    simp only [List.getElem?_drop] at hcon
    rw [hcon, List.getElem?_append_left (by rw [hWl]; omega)]
    exact hwiW
  obtain ⟨wd, hwd, ⟨jtl, jbl, hjtl, -⟩, hwv⟩ := FnAsm.layout_jumpTable hR.layout hR.lm hwi
  have hwv' := hwv jtl (j1 + 5) hjtl h6
  have hal4 := (FnAsm.layout_word hR.layout hR.lm hwi rfl).1
  have hofs : lineOffset R.L (j1 + 6 + i) = ojt + 4 * i := by rw [hwo, h7, hojt']
  have hmem : Arm.read_mem_bytes 4 (A + BitVec.ofNat 64 (4 * i)) s3 = wd := by
    rw [read_mem_bytes_congr (t := s) 4 _ (fun k _ => by rw [hmem3])]
    have := hcode _ wd hwd
    simp only [RL.L] at hofs hal4
    rw [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hal4), hofs] at this
    simp only [A]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact this
  let V := (wd.signExtend 64 : BitVec 64)
  have hV : A + V = R.pcOf jtl := by
    simp only [A, V, RL.pcOf, RL.L]
    simp only [RL.L] at hojt'
    rw [show wd.signExtend 64 = BitVec.ofInt 64 wd.toInt by simp [BitVec.signExtend], hwv',
      ← hojt', BitVec.add_assoc, ofNat_add_ofInt_sub]
  let s4 := Arm.w .PC (R.pcOf (j1 + 3)) (Arm.w (.GPR (rnum nb)) V s3)
  have e4 : R.step s3 = s4 := by
    simp only [RL.step]
    rw [hst3, hx3, haddr, hpc3, ← RL.pcOf_succ_ins h3]
    simp only [ldX, hmem]; rfl
  have hp4 : s4.program = R.fb.program R.base := by simp [s4, Arm.w_program, hp3]
  have hr4 : Arm.r .ERR s4 = .None := by
    simp only [s4]; rw [Arm.r_of_w_different (Ne.symm hpe), Arm.r_of_w_different (Ne.symm hge)]; exact hr3
  have hpc4 : Arm.r .PC s4 = R.pcOf (j1 + 3) := by simp only [s4, Arm.r_of_w_same]
  -- step 5: add
  obtain ⟨b4, hb4, hst4⟩ := armStepX_ins (X := R.X) (H := R.H) hR.layout hR.lm hR.fit h4 rfl hp4
    hpc4 hr4
  obtain ⟨b4', hb4', hx4⟩ := exec_add64 (⟨lineOffset R.fa.lines.toList (j1 + 3), (R.lm[·]?)⟩) ha ha hb s4
  rw [hb4'] at hb4; cases hb4
  have hXa4 : Arm.r (.GPR (rnum na)) s4 = A := by
    simp only [s4, s3]
    rw [Arm.r_of_w_different hnp, Arm.r_of_w_different (hne ha hb hab), Arm.r_of_w_different hnp,
      Arm.r_of_w_same]
  have hXb4 : Arm.r (.GPR (rnum nb)) s4 = V := by
    simp only [s4]; rw [Arm.r_of_w_different hnp, Arm.r_of_w_same]
  let s5 := Arm.w (.GPR (rnum na)) (A + V) (Arm.w .PC (R.pcOf (j1 + 4)) s4)
  have e5 : R.step s4 = s5 := by
    simp only [RL.step]
    rw [hst4, hx4, hXa4, hXb4, hpc4, ← RL.pcOf_succ_ins h4]
  have hp5 : s5.program = R.fb.program R.base := by simp [s5, Arm.w_program, hp4]
  have hr5 : Arm.r .ERR s5 = .None := by
    simp only [s5]; rw [Arm.r_of_w_different (Ne.symm hge), Arm.r_of_w_different (Ne.symm hpe)]; exact hr4
  have hpc5 : Arm.r .PC s5 = R.pcOf (j1 + 4) := by
    simp only [s5]; rw [Arm.r_of_w_different (Ne.symm hnp), Arm.r_of_w_same]
  -- step 6: br
  obtain ⟨b5, hb5, hst5⟩ := armStepX_ins (X := R.X) (H := R.H) hR.layout hR.lm hR.fit h5 rfl hp5
    hpc5 hr5
  obtain ⟨b5', hb5', hx5⟩ := exec_br (⟨lineOffset R.fa.lines.toList (j1 + 4), (R.lm[·]?)⟩) ha s5
  rw [hb5'] at hb5; cases hb5
  let s6 := Arm.w .PC (A + V) s5
  have e6 : R.step s5 = s6 := by
    simp only [RL.step]
    rw [hst5, hx5]
    simp only [s5, s6, Arm.r_of_w_same]
  have hsa : Arm.StateField.GPR 31#5 ≠ .GPR (rnum na) := fun e => by
    injection e with e; exact rnum_ne31 ha e.symm
  have hsb : Arm.StateField.GPR 31#5 ≠ .GPR (rnum nb) := fun e => by
    injection e with e; exact rnum_ne31 hb e.symm
  have hsp : Arm.StateField.GPR 31#5 ≠ .PC := by simp
  obtain ⟨-, jl0, hjl0, hrep0⟩ := repLbl_line hR hrepw
  have hjtl0 : jtl = jl0 := labelOffsets_uniq hR.lm hjtl hjl0
  refine ⟨6, jl0, s6, ?_, ?_, hrep0, ?_, ?_, ?_, fun k hk => ?_⟩
  · simp only [iterN]; rw [e1]; exact (by rw [e2, e3, e4, e5, e6])
  · simp only [s6, Arm.r_of_w_same, hV]; rw [hjtl0]
  rotate_left 3
  · have hg : ∀ {u : Arm.ArmState}, spOf u = spOf s → R.Good u := fun h => .inr (h.trans hspB)
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hgx0 0 (by rw [hn1 hhs]; omega)
    · have e : iterN R.step 1 s = s1 := by simp only [iterN]; rw [e1]
      rw [e]
      exact RL.goodX_ofIns hR h1 (by simp only [s1, Arm.r_of_w_same]) rfl rfl
        (hg (Arm.r_of_w_different hsp)) hr1 hp1 (by rw [e2]; exact RL.nextOk_succ h1 rfl hpc2)
        (RL.readsAt_noLoad hR h1 (by simp only [s1, Arm.r_of_w_same]) rfl)
    · have e : iterN R.step 2 s = s2 := by simp only [iterN]; rw [e1, e2]
      rw [e]
      exact RL.goodX_ofIns hR h2 hpc2 rfl rfl
        (hg (by simp only [spOf, s2, s1, Arm.r_of_w_different hsb, Arm.r_of_w_different hsp]))
        hr2 hp2 (by rw [e3]; exact RL.nextOk_succ h2 rfl hpc3) (RL.readsAt_noLoad hR h2 hpc2 rfl)
    · have e : iterN R.step 3 s = s3 := by simp only [iterN]; rw [e1, e2, e3]
      rw [e]
      exact RL.goodX_ofIns hR h3 hpc3 rfl rfl
        (hg (by simp only [spOf, s3, s2, s1, Arm.r_of_w_different hsa, Arm.r_of_w_different hsb,
          Arm.r_of_w_different hsp])) hr3 hp3 (by rw [e4]; exact RL.nextOk_succ h3 rfl hpc4)
        (RL.readsAt_of_line hR h3 hpc3 fun _ env a hab3 p hp q hq => by
          rw [memReads_load R.ctx (show FinalAM LoadOp.sload32.bytes
              (.regScaledExtended (.x na) (.x nb) .uxtw) from
              ⟨show na ≤ 30 by omega, show nb ≤ 30 by omega, .inl rfl⟩)
            (fun h => by cases h) hab3, List.mem_singleton] at hp
          subst hp
          simp only [LoadOp.bytes] at hq
          refine .inr ⟨j1 + 6 + i, _, _, hwi, q, hq, ?_⟩
          simp only [RL.pcOf]
          rw [haddr, hofs, BitVec.ofNat_add]
          simp only [A, BitVec.add_assoc])
    · have e : iterN R.step 4 s = s4 := by simp only [iterN]; rw [e1, e2, e3, e4]
      rw [e]
      exact RL.goodX_ofIns hR h4 hpc4 rfl rfl
        (hg (by simp only [spOf, s4, s3, s2, s1, Arm.r_of_w_different hsa, Arm.r_of_w_different hsb,
          Arm.r_of_w_different hsp])) hr4 hp4 (by rw [e5]; exact RL.nextOk_succ h4 rfl hpc5) (RL.readsAt_noLoad hR h4 hpc4 rfl)
    · have e : iterN R.step 5 s = s5 := by simp only [iterN]; rw [e1, e2, e3, e4, e5]
      rw [e]
      exact RL.goodX_ofIns hR h5 hpc5 rfl rfl
        (hg (by simp only [spOf, s5, s4, s3, s2, s1, Arm.r_of_w_different hsa,
          Arm.r_of_w_different hsb, Arm.r_of_w_different hsp])) hr5 hp5
        (by rw [e6]; exact RL.nextOk_label hjtl (by simp only [s6, Arm.r_of_w_same, hV]))
        (RL.readsAt_noLoad hR h5 hpc5 rfl)
  · intro f hfp hfa hfb
    simp only [s6, s5, s4, s3, s2, s1]
    rw [Arm.r_of_w_different hfp, Arm.r_of_w_different hfa, Arm.r_of_w_different hfp,
      Arm.r_of_w_different hfp, Arm.r_of_w_different hfb, Arm.r_of_w_different hfp,
      Arm.r_of_w_different hfa, Arm.r_of_w_different hfb, Arm.r_of_w_different hfp,
      Arm.r_of_w_different hfp]
  · simp [s6, s5, s4, s3, s2, s1, Arm.ArmState.mem_w_eq_mem]
  · simp [s6, s5, s4, s3, s2, s1, Arm.w_program]

/-! ## The store after the jump -/

/-- A state that differs from `s` only in the pc and the X registers `na`, `nb` (allocatable),
with the same memory and program, represents the store updated at those registers. -/
theorem stRel_regs {R : RL} {s s' : Arm.ArmState} {m : Loc → CV} {w : Arm.ArmState}
    (hst : StRel R s m w) {na nb : Nat} (ha : na < 29) (hb : nb < 29) (ha18 : na ≠ 18)
    (hb18 : nb ≠ 18) (hf : ∀ f, f ≠ .PC → f ≠ .GPR (rnum na) → f ≠ .GPR (rnum nb) → Arm.r f s' = Arm.r f s)
    (hmem : s'.mem = s.mem) (hprog : s'.program = s.program) :
    StRel R s' (upd (upd m (.reg (.x na)) (regVal s' (.x na))) (.reg (.x nb)) (regVal s' (.x nb))) w := by
  have hsp : spOf s' = spOf s := hf _ (by simp) (fun e => by
      injection e with e; exact rnum_ne31 ha e.symm) (fun e => by
      injection e with e; exact rnum_ne31 hb e.symm)
  have hrd : ∀ n a, Arm.read_mem_bytes n a s' = Arm.read_mem_bytes n a s := fun n a =>
    read_mem_bytes_congr n a (fun k _ => by rw [hmem])
  refine ⟨fun l hl hL => ?_, ⟨fun f hfm => ?_, fun a ha' => ?_, ?_⟩, ?_, ?_, ?_,
    align_of_sp hsp hst.align, fun hfr => ?_, fun k wd hk => ?_, fun a ha => ?_, fun hfr => ?_⟩
  · cases l with
    | reg r =>
      by_cases e2 : r = .x nb
      · subst e2; simp [upd, locVal]
      by_cases e1 : r = .x na
      · subst e1; simp [upd, locVal, e2]
      simp only [upd, Loc.reg.injEq, e1, e2, ite_false]
      rw [hst.store _ hl hL]
      simp only [locVal]
      rcases allocatable_cases (hl r rfl) with ⟨n, rfl, hn, -⟩ | ⟨n, rfl, -⟩
      · simp only [regVal]
        have hna : n ≠ na := fun h => e1 (by rw [h])
        have hnb : n ≠ nb := fun h => e2 (by rw [h])
        have h1 : Arm.StateField.GPR (rnum n) ≠ .GPR (rnum na) := by
          intro e; injection e with e; exact rnum_ne (by omega) (by omega) hna e
        have h2 : Arm.StateField.GPR (rnum n) ≠ .GPR (rnum nb) := by
          intro e; injection e with e; exact rnum_ne (by omega) (by omega) hnb e
        rw [hf (.GPR (rnum n)) (by simp) h1 h2]
      · simp only [regVal]; rw [hf (.SFP (rnum n)) (by simp) (by simp) (by simp)]
    | stack k c =>
      simp only [upd, reduceCtorEq, ite_false]
      rw [hst.store _ hl hL]; simp only [locVal, hsp, hrd]
    | save r =>
      simp only [upd, reduceCtorEq, ite_false]
      rw [hst.store _ hl hL]; simp only [locVal, hsp, hrd]
  · rw [hf f (fun e => hfm (by subst e; trivial))
      (fun e => hfm (by subst e; exact Masked_gpr ha ha18))
      (fun e => hfm (by subst e; exact Masked_gpr hb hb18))]
    exact hst.world.1 f hfm
  · rw [hmem]; exact hst.world.2.1 a ha'
  · rw [hprog]; exact hst.world.2.2
  · rw [hf .ERR (by simp) (by simp) (by simp)]; exact hst.err
  · rw [hprog]; exact hst.prog
  · rw [hsp]; exact hst.sp
  · rw [hrd]; exact hst.fplr hfr
  · rw [hrd]; exact hst.code k wd hk
  · rw [hmem]; exact hst.gkeep a ha
  · have h29a : Arm.StateField.GPR (BitVec.ofNat 5 29) ≠ .GPR (rnum na) := by
      intro e; injection e with e; exact rnum_ne (a := 29) (b := na) (by omega) (by omega) (by omega) e
    have h29b : Arm.StateField.GPR (BitVec.ofNat 5 29) ≠ .GPR (rnum nb) := by
      intro e; injection e with e; exact rnum_ne (a := 29) (b := nb) (by omega) (by omega) (by omega) e
    show Arm.r (.GPR (BitVec.ofNat 5 29)) s' = _
    rw [hf _ (by simp) h29a h29b]
    exact hst.fp hfr

/-! ## The allocation of a `jtSequence` -/

theorem stateT_throw_run {e : String} {s : Nat} {α : Type} :
    StateT.run ((throw e : StateT Nat (Except String) α)) s = .error e := rfl

theorem putOp_vreg_run_eq {regs : Array Reg} {sp : OpSpec} {n : Nat} {cls : RegClass} {k : Nat} :
    StateT.run (putOp regs sp (Reg.vreg n cls)) k =
      match regs[k]? with
      | some p => .ok (p, k + 1)
      | none => .error "fewer allocations than operands" := by
  show StateT.run
    (do let k' ← (get : StateT Nat (Except String) Nat)
        (set (k' + 1) : StateT Nat (Except String) Unit)
        match regs[k']? with
        | some p => (pure p : StateT Nat (Except String) Reg)
        | none => (throw "fewer allocations than operands" : StateT Nat (Except String) Reg)) k = _
  rw [StateT.run_bind, StateT.run_get]
  show StateT.run
    (do (set (k + 1) : StateT Nat (Except String) Unit)
        match regs[k]? with
        | some p => (pure p : StateT Nat (Except String) Reg)
        | none => (throw "fewer allocations than operands" : StateT Nat (Except String) Reg)) k = _
  rw [StateT.run_bind, StateT.run_set]
  show ((match regs[k]? with
        | some p => (pure p : StateT Nat (Except String) Reg)
        | none => (throw "fewer allocations than operands" : StateT Nat (Except String) Reg)).run
      (k + 1)) = _
  simp only [decidableGetElem?, getElem?]
  split
  · rfl
  · rfl

theorem putOp_vreg_ok {regs : Array Reg} {sp : OpSpec} {n : Nat} {cls : RegClass} {k : Nat}
    {q : Reg × Nat} (h : StateT.run (putOp regs sp (Reg.vreg n cls)) k = .ok q) :
    ∃ w : Reg, regs[k]? = some w ∧ q = (w, k + 1) := by
  rw [putOp_vreg_run_eq] at h
  split at h
  · rename_i w heq
    rw [Except.ok.injEq] at h
    exact ⟨w, heq, h.symm⟩
  · simp at h

/-- The assigned form of a `jtSequence` over vreg operands is a `jtSequence` (never a `jump`,
so a `jtSequence` is not the `jump` of a forwarding block). -/
theorem assign_jtVreg {d : Label} {ts : List Label} {vr va vb : Nat} {regs : Array Reg} {y : MInst}
    (h : (MInst.jtSequence d ts (Reg.vreg vr .int) (Reg.vreg va .int) (Reg.vreg vb .int)).assign regs =
      .ok y) :
    ∃ r' a' b', y = .jtSequence d ts r' a' b' := by
  rw [assign_eq] at h
  obtain ⟨p, hrun, hres⟩ := Except.bind_ok h
  obtain ⟨q0, hq0, hgo0⟩ := Except.bind_ok hrun
  have hq0r : StateT.run (putOp regs .use (Reg.vreg vr .int)) 0 = .ok q0 := hq0
  obtain ⟨w0, hw0, hq0e⟩ := putOp_vreg_ok hq0r
  subst hq0e
  simp only [Nat.zero_add] at hgo0
  obtain ⟨q1, hq1, hgo1⟩ := Except.bind_ok hgo0
  have hq1r : StateT.run (putOp regs .earlyDef (Reg.vreg va .int)) 1 = .ok q1 := hq1
  obtain ⟨w1, hw1, hq1e⟩ := putOp_vreg_ok hq1r
  subst hq1e
  simp only [show ((1:Nat) + 1) = 2 from rfl] at hgo1
  obtain ⟨q2, hq2, hgo2⟩ := Except.bind_ok hgo1
  have hq2r : StateT.run (putOp regs .earlyDef (Reg.vreg vb .int)) 2 = .ok q2 := hq2
  obtain ⟨w2, hw2, hq2e⟩ := putOp_vreg_ok hq2r
  subst hq2e
  have hgo2' : Except.ok (MInst.jtSequence d ts w0 w1 w2, (2:Nat) + 1) = Except.ok p := hgo2
  rw [Except.ok.injEq] at hgo2'
  have hgo2a := congrArg Prod.fst hgo2'
  have hres' : ((if (p.2 != regs.size) = true then
      (do let __r ← throw "more allocations than operands"; pure p.1) else pure p.1)) =
      Except.ok y := hres
  cases hb : (p.2 != regs.size)
  · rw [hb] at hres'
    have hres'' : Except.ok p.1 = Except.ok y := hres'
    cases hres''
    exact ⟨w0, w1, w2, hgo2a.symm⟩
  · rw [hb] at hres'
    simp [throw, throwThe, MonadExceptOf.throw] at hres'

/-! ## The `Realizes` case -/

/-- **A jump table on the machine**: from `Q` at a `jtSequence` item, the machine reaches `Q`
at an `MStep` successor (the temporaries havocked to the machine's values). -/
theorem realizes_jt {R : RL} (hR : R.Wf) {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState} {c' : MConf CV Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock} {d : Label}
    {ts : List Label} {ridx t1 t2 : Reg}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some (.jtSequence d ts ridx t1 t2))
    (h : MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c') :
    ∃ n c'', MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c'' ∧
      Q R (iterN R.step n s) c'' ∧ ∀ i < n, R.GoodX (iterN R.step i s) := by
  have hck := (lowerRFunc_ok hR.alloc).2.2
  have hok := ctlCheck_inst hck hvb hi
  simp only [ctlInstOk, Bool.and_eq_true] at hok
  obtain ⟨⟨hr0, ha0⟩, hb0⟩ := hok
  obtain ⟨vr, rfl⟩ := isVregInt_iff hr0
  obtain ⟨va, rfl⟩ := isVregInt_iff ha0
  obtain ⟨vb', rfl⟩ := isVregInt_iff hb0
  cases h with
  | @op b k allocs its m w vb'' i ops outs outs' w' ctl m2 c' hvb' hi' hops' hsz' hsem hlen hho hcl hn =>
  rw [hvb] at hvb'; cases hvb'
  rw [hi] at hi'; cases hi'
  -- the control outcome: a `jtSequence`'s run always goes to a successor block
  have hnc := hn
  have hk1 : k + 1 = vb.insts.size := by
    cases hnc with
    | @goto _ _ _ hk1 _ _ => exact hk1
    | next _ =>
      have h0 := hsem
      simp only [RL.sem, csemV, csem] at h0
      split at h0 <;> (try split at h0) <;> (try split at h0) <;> simp at h0
    | ret hh => simp at hh
    | halt =>
      have h0 := hsem
      simp only [RL.sem, csemV, csem] at h0
      split at h0 <;> (try split at h0) <;> (try split at h0) <;> simp at h0
  -- the forwarding-block case of `Q`: the item's assigned form is a `jump`, which no
  -- `jtSequence` assigns to
  rcases Q.cases hq with hqs | ⟨vbf, allocsf, regsf, if_, xf, bx, hvbf, he, hits, hal, hins,
      hasgf, hsuccf, itx, hitx, hqx⟩
  rotate_left
  · rw [hvb] at hvbf; cases hvbf
    simp only [RItem.op.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    subst hits
    have hi2 := hi
    rw [hins] at hi2
    simp only [List.getElem?_toArray, List.getElem?_cons_zero, Option.some.injEq] at hi2
    subst hi2
    obtain ⟨_, _, _, he2⟩ := assign_jtVreg hasgf
    simp at he2
  obtain ⟨c, ins, _, hc, -⟩ := hR.check
  obtain ⟨preds, hcfg⟩ := hc.cfg
  obtain ⟨t0, tss, hback, hss, hlab⟩ := cfg_block hcfg hvb
  -- the block's own segment: the item is its last instruction
  obtain ⟨_, vb0, _, _, code, _, _, _, _, _, hvb0, -, -, hchk0, hcode, -⟩ := id hqs
  rw [hvb] at hvb0; cases hvb0
  obtain rfl : its = [] := hchk0.tail_nil hk1
  obtain ⟨j0, vb0, items, pre, c1, X, ps1, psm, ps2, x, hvb0, hit, hsplit, hchk, hc1, hX, hT,
    htr, hdrop, hpc, hst, hterm⟩ := qs_term hR hqs
  rw [hvb] at hvb0; cases hvb0
  obtain ⟨regs, i0, i', rfl, hi0, hasg, hc1'⟩ := itemCode_op hc1
  rw [hi] at hi0; cases hi0
  obtain ⟨cc, wh, i2, ops2, hi2, hops2, hstat, -⟩ := op_checked hchk
  rw [hi] at hi2; cases hi2
  rw [hops'] at hops2; cases hops2
  have hopsA : ops = #[⟨vr, .int, .use, .early, .reg⟩, ⟨va, .int, .def, .early, .reg⟩,
      ⟨vb', .int, .def, .early, .reg⟩] := by
    have e : (MInst.jtSequence d ts (.vreg vr .int) (.vreg va .int) (.vreg vb' .int)).operands =
        .ok #[⟨vr, .int, .use, .early, .reg⟩, ⟨va, .int, .def, .early, .reg⟩,
          ⟨vb', .int, .def, .early, .reg⟩] := rfl
    rw [e] at hops'; injection hops' with hh; exact hh.symm
  subst hopsA
  obtain ⟨hsz2, hloc, hnd, -⟩ := checkStatic_facts hstat
  obtain ⟨r0, r1, r2, rfl⟩ := regs3 (by simpa using hsz2.symm)
  have hl0 := (hloc (⟨vr, .int, .use, .early, .reg⟩, .reg r0) (by simp)).1
  have hl1 := (hloc (⟨va, .int, .def, .early, .reg⟩, .reg r1) (by simp)).1
  have hl2 := (hloc (⟨vb', .int, .def, .early, .reg⟩, .reg r2) (by simp)).1
  obtain ⟨nr, rfl, hnr, -, -, hnr18⟩ := locOk_int hl0
  obtain ⟨na, rfl, hna, -, -, hna18⟩ := locOk_int hl1
  obtain ⟨nb, rfl, hnb, -, -, hnb18⟩ := locOk_int hl2
  have hab : na ≠ nb := by
    intro e; subst e
    simp [Operand.isDef] at hnd
  have hasg' : (MInst.jtSequence d ts (.vreg vr .int) (.vreg va .int) (.vreg vb' .int)).assign
      #[.x nr, .x na, .x nb] = .ok (.jtSequence d ts (.x nr) (.x na) (.x nb)) := rfl
  rw [hasg'] at hasg; cases hasg
  obtain rfl : c1 = [.inst (.jtSequence d ts (.x nr) (.x na) (.x nb))] := by
    rcases hc1' with ⟨h, -, -⟩ | ⟨_, h, -⟩ | ⟨_, h, -⟩
    · exact h
    · cases h
    · cases h
  -- the block's last instruction's lines: the jump-table body
  have hdl : ([AInst.inst (.jtSequence d ts (.x nr) (.x na) (.x nb))]).dropLast = [] := by
    simp
  have hgl : ([AInst.inst (.jtSequence d ts (.x nr) (.x na) (.x nb))]).getLast?.toList =
      [AInst.inst (.jtSequence d ts (.x nr) (.x na) (.x nb))] := by
    simp
  rw [hdl] at hX
  rw [hgl] at hT
  have hXe : codeLinesE R.ctx R.af [] ps1 = .ok ([], ps1) := by simp [codeLinesE]
  rw [hXe] at hX
  simp only [Except.ok.injEq, Prod.mk.injEq] at hX
  obtain ⟨hX0, hpsm0⟩ := hX
  subst hX0
  subst hpsm0
  have hl3 := codeLinesE_single hT
  simp only [MInst.lines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl3
  obtain ⟨hls1, -⟩ := hl3
  have htJ : x.1.term = jtBody d ts (.x nr) (.x na) (.x nb) (.jt ps1.jt) := by
    rw [← hls1]; simp [jtBody]
  have hlenT : x.1.term.length = 7 + ts.length := by rw [htJ]; simp [jtBody]; omega
  -- the emitted segment: each line kept or retargeted (`LineOut`; a kept line has no block
  -- target, so the default branch and the table words are retargeted to representing labels)
  obtain ⟨hlenO, hLO⟩ := termOk_kept (by simp) (by simp) (by simp) (by simp) hterm
  have hlen2' : x.2.1.length = 7 + ts.length := by rw [hlenO]; exact hlenT
  have jtBody_cons : jtBody d ts (.x nr) (.x na) (.x nb) (.jt ps1.jt) =
      Line.ins (.bcond .hs (.block d)) :: (jtHead ts (.x nr) (.x na) (.x nb) (.jt ps1.jt) ++
        ts.map (fun l => Line.word (.block l) (.jt ps1.jt))) := rfl
  have hhead : (jtHead ts (.x nr) (.x na) (.x nb) (.jt ps1.jt)).length = 6 := by simp [jtHead]
  have hheadT : ∀ ln ∈ jtHead ts (.x nr) (.x na) (.x nb) (.jt ps1.jt), Line.target? ln = none := by
    intro ln hln
    simp only [jtHead, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hln
    rcases hln with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  -- the raw line at a segment index `k` with `1 ≤ k ≤ 6`
  have htermK : ∀ k, 1 ≤ k → k < 7 → x.1.term[k]? =
      (jtHead ts (.x nr) (.x na) (.x nb) (.jt ps1.jt))[k - 1]? := by
    intro k h1 h2
    obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [hk', htJ, jtBody_cons, List.getElem?_cons_succ,
      List.getElem?_append_left (by rw [hhead]; omega),
      show (k':Nat) + 1 - 1 = k' from by omega]
  have hU : (((#[(⟨vr, .int, .use, .early, .reg⟩ : Operand), ⟨va, .int, .def, .early, .reg⟩,
      ⟨vb', .int, .def, .early, .reg⟩].zip (#[Reg.x nr, .x na, .x nb].map Loc.reg)).toList.filter
      (·.1.isUse)).map (m ·.2)) = [regVal s (.x nr)] := by
    have := hst.store (.reg (.x nr)) (fun r e => by cases e; exact (locOk_int hl0 |> fun ⟨_, e, _⟩ => by
      cases e; simp only [CheckCtx.locOk, Bool.and_eq_true] at hl0; exact hl0.2)) trivial
    simp [Operand.isUse, this, locVal]
  rw [hU] at hsem
  have hhs : Arm.ConditionHolds Cond.hs.bits w = Arm.ConditionHolds Cond.hs.bits s :=
    (ConditionHolds_sameWorld hst.world _).symm
  simp only [RL.sem, csemV, csem] at hsem
  rw [hhs] at hsem
  -- the successor
  have hti : t0 = MInst.jtSequence d ts (.vreg vr .int) (.vreg va .int) (.vreg vb' .int) := by
    rw [Array.back?_eq_getElem?, show vb.insts.size - 1 = k by omega, hi] at hback
    cases hback; rfl
  subst hti
  -- the store the chosen successor gets: the temporaries hold the machine's values
  have hstore : ∀ (o1 o2 : CV),
      writeM (writeM m ((((#[(⟨vr, .int, .use, .early, .reg⟩ : Operand), ⟨va, .int, .def, .early, .reg⟩,
        ⟨vb', .int, .def, .early, .reg⟩].zip (#[Reg.x nr, .x na, .x nb].map Loc.reg)).toList.filter
        (·.1.isDef)).zip [o1, o2]).filter (·.1.1.isEarly)))
        ((((#[(⟨vr, .int, .use, .early, .reg⟩ : Operand), ⟨va, .int, .def, .early, .reg⟩,
        ⟨vb', .int, .def, .early, .reg⟩].zip (#[Reg.x nr, .x na, .x nb].map Loc.reg)).toList.filter
        (·.1.isDef)).zip [o1, o2]).filter (·.1.1.isLate)) =
      upd (upd m (.reg (.x na)) o1) (.reg (.x nb)) o2 := by
    intro o1 o2
    simp [Operand.isDef, Operand.isEarly, Operand.isLate, writeM]
  have hcl0 : ∀ (m' : Loc → CV), Clobbered ckeep
      (MInst.jtSequence d ts (.vreg vr .int) (.vreg va .int) (.vreg vb' .int)).clobbers m' m' :=
    fun m' => ⟨fun _ _ => rfl, fun c hc => by simp [MInst.clobbers] at hc⟩
  -- the default branch's line: retargeted to a label representing `d`
  have hlen1 : 0 < x.2.1.length := by omega
  have ht0 : x.1.term[0]? = some (Line.ins (Insn.bcond Cond.hs (Lbl.block d)) none) := by
    rw [htJ]; simp [jtBody]
  obtain ⟨y0, hy0⟩ : ∃ y, x.2.1[0]? = some y := ⟨_, List.getElem?_eq_getElem hlen1⟩
  rcases hLO 0 _ _ ht0 hy0 with ⟨-, hnb0⟩ | ⟨lb, l2, hxt0, hyt0, hre0, hrep0⟩
  · exact (hnb0 d rfl).elim
  · simp only [Line.target?, Option.some.injEq, Lbl.block.injEq] at hxt0
    subst hxt0
    have hbc0 : y0 = .ins (.bcond .hs l2) none := by
      rw [hre0]; rfl
    have hcons : x.2.1 = y0 :: x.2.1.drop 1 := by
      cases h21 : x.2.1 with
      | nil => rw [h21] at hlen1; simp at hlen1
      | cons a as =>
        rw [h21] at hy0
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hy0
        subst hy0
        simp [h21]
    have hWlJ : (x.2.1.drop 7).length = ts.length := by
      rw [List.length_drop]; omega
    have hWJ : ∀ (i : Nat) (l : Label), ts[i]? = some l → ∃ l', (x.2.1.drop 7)[i]? =
        some (Line.word l' (.jt ps1.jt)) ∧
        RepLbl (planRep R.fa.k R.af) (blockLabelIdx (planLines R.fa.k R.af)) l l' := by
      intro i l hiw
      have hil' : i < ts.length := (List.getElem?_eq_some_iff.1 hiw).1
      have hleni : 7 + i < x.2.1.length := by omega
      obtain ⟨y, hy⟩ : ∃ y, x.2.1[7 + i]? = some y := ⟨_, List.getElem?_eq_getElem hleni⟩
      have htword : x.1.term[7 + i]? = some (Line.word (Lbl.block l) (.jt ps1.jt)) := by
        rw [show (7:Nat) + i = 6 + i + 1 from by omega, htJ, jtBody_cons,
          List.getElem?_cons_succ, List.getElem?_append_right (by rw [hhead]; omega), hhead,
          show (6:Nat) + i - 6 = i from by omega, List.getElem?_map, hiw]
        simp
      rcases hLO (7 + i) _ _ htword hy with ⟨-, hnb⟩ | ⟨l3, l4, hxt, hyt, hre, hrep⟩
      · exact (hnb l rfl).elim
      · simp only [Line.target?, Option.some.injEq, Lbl.block.injEq] at hxt
        subst hxt
        refine ⟨l4, ?_, hrep⟩
        rw [List.getElem?_drop, hy, hre]
        rfl
    have hrelNone : ∀ ln ∈ jtHead ts (.x nr) (.x na) (.x nb) (.jt ps1.jt) ++ x.2.1.drop 7,
        ln.relaxable? = none := by
      intro ln hln
      rcases List.mem_append.1 hln with hln | hln
      · simp only [jtHead, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hln
        rcases hln with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
      · obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hln
        have hkL : k < ts.length := by
          have := (List.getElem?_eq_some_iff.1 hk).1
          rw [hWlJ] at this; exact this
        obtain ⟨l5, hw5, -⟩ := hWJ k _ (List.getElem?_eq_getElem hkL)
        rw [hw5] at hk
        rw [(Option.some.inj hk).symm]
        rfl
    have hrest : x.2.1.drop 1 = jtHead ts (.x nr) (.x na) (.x nb) (.jt ps1.jt) ++ x.2.1.drop 7 := by
      apply List.ext_getElem?
      intro k
      rw [List.getElem?_drop]
      rcases Nat.lt_or_ge (k + 1) 7 with h7 | h7
      · obtain ⟨y, hy⟩ : ∃ y, x.2.1[1 + k]? = some y := ⟨_, List.getElem?_eq_getElem (by omega)⟩
        have htk : x.1.term[1 + k]? =
            (jtHead ts (.x nr) (.x na) (.x nb) (.jt ps1.jt))[k]? := by
          have h0 := htermK (k + 1) (by omega) (by omega)
          rw [show (k:Nat) + 1 = 1 + k from Nat.add_comm k 1,
            show (1:Nat) + k - 1 = k from by omega] at h0
          exact h0
        obtain ⟨xl, hxl⟩ : ∃ xw, x.1.term[1 + k]? = some xw := by
          refine ⟨(jtHead ts (.x nr) (.x na) (.x nb) (.jt ps1.jt))[k], ?_⟩
          rw [htk, List.getElem?_eq_some_iff]
          exact ⟨by rw [hhead]; omega, rfl⟩
        rcases hLO (1 + k) xl y hxl hy with ⟨heq, -⟩ | ⟨l3, l4, hxt, -, -, -⟩
        · rw [hy, heq, List.getElem?_append_left (by rw [hhead]; omega), ← htk, hxl]
        · exfalso
          have hk6 : (k:Nat) < (jtHead ts (.x nr) (.x na) (.x nb) (.jt ps1.jt)).length := by
            rw [hhead]; omega
          have hxe : (jtHead ts (.x nr) (.x na) (.x nb) (.jt ps1.jt))[k]? = some xl := by
            rw [← htk, hxl]
          obtain ⟨hik2, hxe2⟩ := List.getElem?_eq_some_iff.1 hxe
          have hxT0 : Line.target? ((jtHead ts (.x nr) (.x na) (.x nb) (.jt ps1.jt))[k]) = none :=
            hheadT _ (List.getElem_mem (l := jtHead ts (.x nr) (.x na) (.x nb) (.jt ps1.jt)) hk6)
          rw [hxe2] at hxT0
          have hxT : Line.target? xl = none := hxT0
          rw [hxT] at hxt
          simp at hxt
      · rw [List.getElem?_append_right (by rw [hhead]; omega), hhead, List.getElem?_drop,
          show (7:Nat) + (k - 6) = k + 1 from by omega, Nat.add_comm 1 k]
    have hbcJ : ∃ l', y0 = .ins (.bcond .hs l') none ∧
        RepLbl (planRep R.fa.k R.af) (blockLabelIdx (planLines R.fa.k R.af)) d l' :=
      ⟨l2, hbc0, hrep0⟩
    have hdropJT : R.L.drop j0 = relaxLine R.far y0 ++
        (jtHead ts (.x nr) (.x na) (.x nb) (.jt ps1.jt) ++ x.2.1.drop 7 ++
          R.L.drop (rix R.far (planLines R.fa.k R.af) x.2.2)) := by
      rw [hdrop, List.nil_append, hcons, relaxLines_cons, hrest,
        relaxLines_of_none hrelNone]
      have hd7 : List.drop 7 (y0 :: (jtHead ts (.x nr) (.x na) (.x nb) (.jt ps1.jt) ++
          List.drop 7 x.snd.fst)) = List.drop 7 x.snd.fst := by
        rw [List.drop_cons (by omega), List.drop_append,
          List.drop_eq_nil_of_le (by rw [hhead]; omega), List.nil_append,
          show (7:Nat) - 1 - (jtHead ts (.x nr) (.x na) (.x nb) (.jt ps1.jt)).length = 0
            from by omega, List.drop_zero]
      rw [hd7]
      simp only [List.append_assoc]
    obtain ⟨hmTaken, hmNot⟩ := jt_machine hR hnr hna hnb hab (by simp) hdropJT hbcJ hWJ hWlJ
      hst.prog hpc hst.err hst.sp
      hst.code
    cases hn with
    | next _ => split at hsem <;> (try split at hsem) <;> simp at hsem
    | ret h => simp at h
    | halt => split at hsem <;> (try split at hsem) <;> simp at hsem
    | @goto jj st items' hk1 hsucc hitems =>
    have hsucc' := hsucc
    simp only [succOf, hcfg, hss, Option.bind_some] at hsucc'
    have hst0 : st ≠ 0 := ctlCheck_succ hck hsucc
    obtain ⟨vs, hvs, hlj⟩ := hlab _ st hsucc'
    have hw2 : w' = w ∧ outs.length = 2 := by
      split at hsem
      · simp only [Option.some.injEq, Prod.mk.injEq] at hsem; rw [← hsem.1, ← hsem.2.1]; exact ⟨rfl, rfl⟩
      · split at hsem
        · simp only [Option.some.injEq, Prod.mk.injEq] at hsem; rw [← hsem.1, ← hsem.2.1]; exact ⟨rfl, rfl⟩
        · cases hsem
    obtain ⟨hw', hout2⟩ := hw2
    subst w'
    -- the MStep with the machine's temporaries, and `Q` at the successor
    have fin : ∀ (s' : Arm.ArmState) (n jl : Nat), iterN R.step n s = s' →
        Arm.r .PC s' = R.pcOf jl → RepL R.af (planOwn R.fa.k R.af) R.L vs.label jl →
        (∀ f, f ≠ .PC → f ≠ .GPR (rnum na) → f ≠ .GPR (rnum nb) → Arm.r f s' = Arm.r f s) →
        s'.mem = s.mem → s'.program = s.program → (∀ i < n, R.GoodX (iterN R.step i s)) →
        ∃ n c'', MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k (#[Reg.x nr, .x na, .x nb].map Loc.reg) :: [], m, w⟩) c'' ∧
          Q R (iterN R.step n s) c'' ∧ ∀ i < n, R.GoodX (iterN R.step i s) := by
      intro s' n jl hn hpc' hjl hf hmem hprog hsp
      have hsem' : R.sem (.jtSequence d ts (.vreg vr .int) (.vreg va .int) (.vreg vb' .int))
          (((#[(⟨vr, .int, .use, .early, .reg⟩ : Operand), ⟨va, .int, .def, .early, .reg⟩,
            ⟨vb', .int, .def, .early, .reg⟩].zip (#[Reg.x nr, .x na, .x nb].map Loc.reg)).toList.filter
            (·.1.isUse)).map (m ·.2)) w = some (outs, w, .goto jj) := by
        rw [hU]; simp only [RL.sem, csemV, csem, hhs]; exact hsem
      refine ⟨n, _, MStep.op (outs' := [regVal s' (.x na), regVal s' (.x nb)]) (w' := w) hvb hi hops' hsz'
        hsem' hlen ⟨by rw [hout2]; rfl,
          fun h => by simp [havocFrom, MInst.keptDefs, MInst.isBranch] at h,
          fun n h => by simp [havocFrom, MInst.keptDefs, MInst.isBranch] at h; subst h; rfl⟩
        (hcl0 _) (MNext.goto hk1 hsucc hitems), ?_, hsp⟩
      rw [hstore, hn]
      exact q_entry hR hst0 hvs hitems hjl hpc' (stRel_regs hst hna hnb hna18 hnb18 hf hmem hprog)
    -- which successor
    split at hsem
    · rename_i hhs'
      simp only [Option.some.injEq, Prod.mk.injEq] at hsem
      obtain ⟨-, -, hj⟩ := hsem
      injection hj with hj
      subst hj
      obtain ⟨n, jl, hn', hrep, hsp⟩ := hmTaken hhs'
      simp only [MInst.targets, List.getElem?_cons_zero, Option.some.injEq] at hlj
      rw [hlj] at hrep
      exact fin _ n jl hn' (Arm.r_of_w_same ..) hrep
        (fun f hf _ _ => Arm.r_of_w_different hf) (by simp [Arm.ArmState.mem_w_eq_mem])
        (by simp [Arm.w_program]) hsp
    · rename_i hhs'
      split at hsem
      · rename_i hlt
        simp only [Option.some.injEq, Prod.mk.injEq] at hsem
        obtain ⟨-, -, hj⟩ := hsem
        injection hj with hj
        subst hj
        simp only [MInst.targets, List.getElem?_cons_succ] at hlj
        obtain ⟨n, jl, s', hn', hpc', hrep, hf, hmem, hprog, hsp⟩ := hmNot (by simpa using hhs') _ vs.label
          (by simp [lo64, regVal, BitVec.toNat_setWidth]) hlj
        exact fin s' n jl hn' hpc' hrep hf hmem hprog hsp
      · cases hsem

end Backend.Proof
