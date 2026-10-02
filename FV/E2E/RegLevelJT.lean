import FV.E2E.RegLevelCall
import FV.Backend.Proof.RegallocMem
import FV.Backend.Proof.RegallocTac

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

theorem ftStep_nob {ln : Line} {n1 n2 : Option Line} (h1 : ∀ x, ln ≠ .ins (.b x) none)
    (h2 : ∀ c e, ln = .ins c none → n1 ≠ some (.ins (.b e) none)) :
    ftStep ln n1 n2 = ([ln], 1) := by
  unfold ftStep
  repeat' split
  all_goals simp_all

theorem ftList_pass {ln : Line} {Z : List Line} (h : ftStep ln Z[0]? Z[1]? = ([ln], 1)) :
    ftList (ln :: Z) = ln :: ftList Z := by
  rw [ftList_cons, h]; rfl

theorem ftList_noIns : ∀ (P Z : List Line), (∀ ln ∈ P, ∀ c t, ln ≠ .ins c t) →
    ftList (P ++ Z) = P ++ ftList Z
  | [], _, _ => rfl
  | ln :: P, Z, h => by
    rw [List.cons_append, ftList_pass (ftStep_nob (fun x e => h ln (by simp) _ _ e)
      (fun c e' e => absurd e (h ln (by simp) c none))), ftList_noIns P Z (fun x hx => h x (by simp [hx]))]
    rfl

theorem ftList_jt (d : Label) (ts : List Label) (r a b : Reg) (jt : Lbl) (Z : List Line) :
    ftList (jtBody d ts r a b jt ++ Z) = jtBody d ts r a b jt ++ ftList Z := by
  simp only [jtBody, List.cons_append, List.nil_append]
  repeat rw [ftList_pass (ftStep_nob (by simp) (by simp))]
  rw [ftList_noIns _ _ (by simp)]

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

/-- **The machine runs a jump table.** -/
theorem jt_machine {R : RL} (hR : R.Wf) {s : Arm.ArmState} {j0 : Nat} {d : Label}
    {ts : List Label} {nr na nb : Nat} (hr : nr < 29) (ha : na < 29) (hb : nb < 29)
    (hab : na ≠ nb) {jt : Lbl} {T : List Line}
    (hdrop : R.L.drop j0 = jtBody d ts (.x nr) (.x na) (.x nb) jt ++ T)
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j0)
    (herr : Arm.r .ERR s = .None)
    (hcode : ∀ k w, R.fb.words[k]? = some w →
      Arm.read_mem_bytes 4 (R.base + BitVec.ofNat 64 (4 * k)) s = w) :
    (Arm.ConditionHolds Cond.hs.bits s = true → ∃ n jl, iterN R.step n s = Arm.w .PC (R.pcOf jl) s ∧
      R.L[jl]? = some (.label (.block d))) ∧
    (Arm.ConditionHolds Cond.hs.bits s = false → ∀ i l,
      (Arm.r (.GPR (rnum nr)) s).toNat % 2 ^ 32 = i → ts[i]? = some l →
      ∃ n jl s', iterN R.step n s = s' ∧ Arm.r .PC s' = R.pcOf jl ∧
        R.L[jl]? = some (.label (.block l)) ∧
        (∀ f, f ≠ .PC → f ≠ .GPR (rnum na) → f ≠ .GPR (rnum nb) → Arm.r f s' = Arm.r f s) ∧
        s'.mem = s.mem ∧ s'.program = s.program) := by
  have hL : ∀ t ln, (jtBody d ts (.x nr) (.x na) (.x nb) jt)[t]? = some ln → R.L[j0 + t]? = some ln := by
    intro t ln ht
    have := congrArg (·[t]?) hdrop
    simp only [List.getElem?_drop] at this
    rw [this, List.getElem?_append_left (List.getElem?_eq_some_iff.1 ht).1]
    exact ht
  have h0 : R.L[j0]? = some (.ins (.bcond .hs (.block d))) := hL 0 _ rfl
  have h1 : R.L[j0 + 1]? = some (.ins (.csel (.x nb) .xzr (.x nr) .hs)) := hL 1 _ rfl
  have h2 : R.L[j0 + 2]? = some (.ins (.adr (.x na) jt)) := hL 2 _ rfl
  have h3 : R.L[j0 + 3]? = some (.ins (.load .sload32 (.x nb) (.regScaledExtended (.x na) (.x nb) .uxtw))) :=
    hL 3 _ rfl
  have h4 : R.L[j0 + 4]? = some (.ins (.aluRRR .add true (.x na) (.x na) (.x nb))) := hL 4 _ rfl
  have h5 : R.L[j0 + 5]? = some (.ins (.br (.x na))) := hL 5 _ rfl
  have h6 : R.L[j0 + 6]? = some (.label jt) := hL 6 _ rfl
  obtain ⟨a0, jl0, ha0, hjl0, hstep0⟩ := step_branch hR h0 (.inr (.inl ⟨_, rfl⟩)) hprog hpc herr
  rw [brCond_bcond ha0] at hstep0
  refine ⟨fun hhs => ⟨1, jl0, by simp only [iterN, hstep0, hhs, ite_true], hjl0⟩, fun hhs i l hi hl => ?_⟩
  -- not taken: five more steps
  have hne : ∀ {x y : Nat}, x < 29 → y < 29 → x ≠ y → Arm.StateField.GPR (rnum x) ≠ .GPR (rnum y) :=
    fun hx hy hxy e => by injection e with e; exact rnum_ne (by omega) (by omega) hxy e
  have hnp : ∀ {x : Nat}, Arm.StateField.GPR (rnum x) ≠ .PC := fun e => by cases e
  have hpe : Arm.StateField.PC ≠ .ERR := by simp
  have hge : ∀ {x : Nat}, Arm.StateField.GPR (rnum x) ≠ .ERR := fun e => by cases e
  have env := fun (t : Nat) => (⟨lineOffset R.fa.lines.toList (j0 + t), (R.lm[·]?)⟩ : Env)
  let X := Arm.r (.GPR (rnum nr)) s
  -- step 1: `b.hs` not taken
  have e1 : R.step s = Arm.w .PC (R.pcOf (j0 + 1)) s := by rw [hstep0, hhs]; rfl
  -- step 2: csel
  let s1 := Arm.w .PC (R.pcOf (j0 + 1)) s
  have hp1 : s1.program = R.fb.program R.base := by simp [s1, Arm.w_program, hprog]
  have hr1 : Arm.r .ERR s1 = .None := by simp only [s1]; rw [Arm.r_of_w_different (Ne.symm hpe)]; exact herr
  obtain ⟨b1, hb1, hst1⟩ := armStepX_ins (X := R.X) (H := R.H) hR.layout hR.lm hR.fit h1 rfl hp1
    (by simp only [s1, Arm.r_of_w_same]; rfl) hr1
  obtain ⟨b1', hb1', hx1⟩ := exec_csel_hs (⟨lineOffset R.fa.lines.toList (j0 + 1), (R.lm[·]?)⟩) hb hr s1
  rw [hb1'] at hb1; cases hb1
  have hc1 : Arm.ConditionHolds Cond.hs.bits s1 = false := by
    rw [← hhs]; exact ConditionHolds_sameWorld (F := fun _ => True)
      (SameWorld.w_left (by simp [Masked]) (SameWorld.refl _ s)) _
  let s2 := Arm.w (.GPR (rnum nb)) X (Arm.w .PC (R.pcOf (j0 + 2)) s1)
  have e2 : R.step s1 = s2 := by
    simp only [RL.step]
    rw [hst1, hx1, hc1]
    simp only [s2, s1, Bool.false_eq_true, ite_false, Arm.r_of_w_same]
    rw [Arm.r_of_w_different hnp, RL.pcOf_succ_ins h1]
  have hp2 : s2.program = R.fb.program R.base := by simp [s2, Arm.w_program, hp1]
  have hr2 : Arm.r .ERR s2 = .None := by
    simp only [s2]; rw [Arm.r_of_w_different (Ne.symm hge), Arm.r_of_w_different (Ne.symm hpe)]; exact hr1
  have hpc2 : Arm.r .PC s2 = R.pcOf (j0 + 2) := by
    simp only [s2]; rw [Arm.r_of_w_different (Ne.symm hnp), Arm.r_of_w_same]
  -- step 3: adr
  obtain ⟨b2, hb2, hst2⟩ := armStepX_ins (X := R.X) (H := R.H) hR.layout hR.lm hR.fit h2 rfl hp2
    hpc2 hr2
  obtain ⟨o, ho, hx2⟩ := exec_adr ha hb2 s2
  obtain ⟨ojt, hojt, hoff, -⟩ := Insn.toArmInst_pcRel hb2 (t := jt) (reach := 2 ^ 20) (align := 1) rfl
  rw [hoff] at ho; cases ho
  have hojt' : ojt = lineOffset R.L (j0 + 6) := by
    have := labelOffsets_label hR.lm h6
    simp only [RL.L] at this ⊢
    simp only at hojt
    rw [hojt] at this; exact Option.some.inj this
  let A := R.base + BitVec.ofNat 64 ojt
  have hjtaddr : Arm.r .PC s2 + BitVec.ofInt 64 ((ojt : Int) - lineOffset R.fa.lines.toList (j0 + 2)) = A := by
    rw [hpc2]; simp only [RL.pcOf, RL.L, A]; rw [BitVec.add_assoc, ofNat_add_ofInt_sub]
  let s3 := Arm.w .PC (R.pcOf (j0 + 3)) (Arm.w (.GPR (rnum na)) A s2)
  have e3 : R.step s2 = s3 := by
    simp only [RL.step]
    rw [hst2, hx2, hjtaddr, hpc2, ← RL.pcOf_succ_ins h2]
  have hp3 : s3.program = R.fb.program R.base := by simp [s3, Arm.w_program, hp2]
  have hr3 : Arm.r .ERR s3 = .None := by
    simp only [s3]; rw [Arm.r_of_w_different (Ne.symm hpe), Arm.r_of_w_different (Ne.symm hge)]; exact hr2
  have hpc3 : Arm.r .PC s3 = R.pcOf (j0 + 3) := by simp only [s3, Arm.r_of_w_same]
  -- step 4: ldrsw
  obtain ⟨b3, hb3, hst3⟩ := armStepX_ins (X := R.X) (H := R.H) hR.layout hR.lm hR.fit h3 rfl hp3
    hpc3 hr3
  obtain ⟨b3', hb3', hx3⟩ := exec_load_line (⟨lineOffset R.fa.lines.toList (j0 + 3), (R.lm[·]?)⟩)
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
  have hws : R.L.drop (j0 + 7) = ts.map (fun l => Line.word (.block l) jt) ++ T := by
    rw [← List.drop_drop, hdrop]; simp [jtBody]
  have hil : i < ts.length := (List.getElem?_eq_some_iff.1 hl).1
  have hwo := lineOffset_words hws (by simp) i (by simp; omega)
  have h7 : lineOffset R.L (j0 + 7) = lineOffset R.L (j0 + 6) := by
    rw [lineOffset_succ _ _ _ h6]; simp [Line.size]
  have hwi : R.L[j0 + 7 + i]? = some (.word (.block l) jt) := by
    have := congrArg (·[i]?) hws
    simp only [List.getElem?_drop] at this
    rw [this, List.getElem?_append_left (by simpa using hil)]
    simp [hl]
  obtain ⟨wd, hwd, ⟨jtl, jbl, hjtl, -⟩, hwv⟩ := FnAsm.layout_jumpTable hR.layout hR.lm hwi
  have hwv' := hwv jtl (j0 + 6) hjtl h6
  have hal4 := (FnAsm.layout_word hR.layout hR.lm hwi rfl).1
  have hofs : lineOffset R.L (j0 + 7 + i) = ojt + 4 * i := by rw [hwo, h7, hojt']
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
  let s4 := Arm.w .PC (R.pcOf (j0 + 4)) (Arm.w (.GPR (rnum nb)) V s3)
  have e4 : R.step s3 = s4 := by
    simp only [RL.step]
    rw [hst3, hx3, haddr, hpc3, ← RL.pcOf_succ_ins h3]
    simp only [ldX, hmem]; rfl
  have hp4 : s4.program = R.fb.program R.base := by simp [s4, Arm.w_program, hp3]
  have hr4 : Arm.r .ERR s4 = .None := by
    simp only [s4]; rw [Arm.r_of_w_different (Ne.symm hpe), Arm.r_of_w_different (Ne.symm hge)]; exact hr3
  have hpc4 : Arm.r .PC s4 = R.pcOf (j0 + 4) := by simp only [s4, Arm.r_of_w_same]
  -- step 5: add
  obtain ⟨b4, hb4, hst4⟩ := armStepX_ins (X := R.X) (H := R.H) hR.layout hR.lm hR.fit h4 rfl hp4
    hpc4 hr4
  obtain ⟨b4', hb4', hx4⟩ := exec_add64 (⟨lineOffset R.fa.lines.toList (j0 + 4), (R.lm[·]?)⟩) ha ha hb s4
  rw [hb4'] at hb4; cases hb4
  have hXa4 : Arm.r (.GPR (rnum na)) s4 = A := by
    simp only [s4, s3]
    rw [Arm.r_of_w_different hnp, Arm.r_of_w_different (hne ha hb hab), Arm.r_of_w_different hnp,
      Arm.r_of_w_same]
  have hXb4 : Arm.r (.GPR (rnum nb)) s4 = V := by
    simp only [s4]; rw [Arm.r_of_w_different hnp, Arm.r_of_w_same]
  let s5 := Arm.w (.GPR (rnum na)) (A + V) (Arm.w .PC (R.pcOf (j0 + 5)) s4)
  have e5 : R.step s4 = s5 := by
    simp only [RL.step]
    rw [hst4, hx4, hXa4, hXb4, hpc4, ← RL.pcOf_succ_ins h4]
  have hp5 : s5.program = R.fb.program R.base := by simp [s5, Arm.w_program, hp4]
  have hr5 : Arm.r .ERR s5 = .None := by
    simp only [s5]; rw [Arm.r_of_w_different (Ne.symm hge), Arm.r_of_w_different (Ne.symm hpe)]; exact hr4
  have hpc5 : Arm.r .PC s5 = R.pcOf (j0 + 5) := by
    simp only [s5]; rw [Arm.r_of_w_different (Ne.symm hnp), Arm.r_of_w_same]
  -- step 6: br
  obtain ⟨b5, hb5, hst5⟩ := armStepX_ins (X := R.X) (H := R.H) hR.layout hR.lm hR.fit h5 rfl hp5
    hpc5 hr5
  obtain ⟨b5', hb5', hx5⟩ := exec_br (⟨lineOffset R.fa.lines.toList (j0 + 5), (R.lm[·]?)⟩) ha s5
  rw [hb5'] at hb5; cases hb5
  let s6 := Arm.w .PC (A + V) s5
  have e6 : R.step s5 = s6 := by
    simp only [RL.step]
    rw [hst5, hx5]
    simp only [s5, s6, Arm.r_of_w_same]
  refine ⟨6, jtl, s6, ?_, by simp only [s6, Arm.r_of_w_same, hV], hjtl, ?_, ?_, ?_⟩
  · simp only [iterN]; rw [e1]; exact (by rw [e2, e3, e4, e5, e6])
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
    align_of_sp hsp hst.align, fun hfr => ?_, fun k wd hk => ?_⟩
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
      Q R (iterN R.step n s) c'' := by
  have hck := (lowerRFunc_ok hR.alloc).2.2.2
  have hok := ctlCheck_inst hck hvb hi
  simp only [ctlInstOk, Bool.and_eq_true] at hok
  obtain ⟨⟨hr0, ha0⟩, hb0⟩ := hok
  obtain ⟨vr, rfl⟩ := isVregInt_iff hr0
  obtain ⟨va, rfl⟩ := isVregInt_iff ha0
  obtain ⟨vb', rfl⟩ := isVregInt_iff hb0
  obtain ⟨j0, items, pre, regs, i', c1, c2, ls1, ls2, ps1, psm, ps2, T, cc, wh, ops, rfl, hit, hsplit,
    hasg, hc1', hops, hstat, hchk', hc2, h1, h2, htr, hdrop, hpc, hst⟩ := q_op hq hvb hi
  have hops' : ops = #[⟨vr, .int, .use, .early, .reg⟩, ⟨va, .int, .def, .early, .reg⟩,
      ⟨vb', .int, .def, .early, .reg⟩] := by
    have e : (MInst.jtSequence d ts (.vreg vr .int) (.vreg va .int) (.vreg vb' .int)).operands =
        .ok #[⟨vr, .int, .use, .early, .reg⟩, ⟨va, .int, .def, .early, .reg⟩,
          ⟨vb', .int, .def, .early, .reg⟩] := rfl
    rw [e] at hops; injection hops with h; exact h.symm
  subst hops'
  obtain ⟨hsz, hloc, hnd, -⟩ := checkStatic_facts hstat
  obtain ⟨r0, r1, r2, rfl⟩ := regs3 (by simpa using hsz.symm)
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
  have hl1 := codeLinesE_single h1
  simp only [MInst.lines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl1
  obtain ⟨hls1, -⟩ := hl1
  have hdrop' : R.L.drop j0 = jtBody d ts (.x nr) (.x na) (.x nb) (.jt ps1.jt) ++
      (ftList (ls2 ++ nxtOf R.af b) ++ T) := by
    rw [hdrop, ← hls1, show [Line.ins (.bcond .hs (.block d)), .ins (.csel (.x nb) .xzr (.x nr) .hs),
      .ins (.adr (.x na) (.jt ps1.jt)),
      .ins (.load .sload32 (.x nb) (.regScaledExtended (.x na) (.x nb) .uxtw)),
      .ins (.aluRRR .add true (.x na) (.x na) (.x nb)), .ins (.br (.x na)), .label (.jt ps1.jt)] ++
      ts.map (fun l => Line.word (.block l) (.jt ps1.jt)) = jtBody d ts (.x nr) (.x na) (.x nb) (.jt ps1.jt)
      from rfl, ftList_jt, List.append_assoc]
  obtain ⟨hmTaken, hmNot⟩ := jt_machine hR hnr hna hnb hab hdrop' hst.prog hpc hst.err hst.code
  obtain ⟨c, ins, hc⟩ := checked_of_checkAlloc hR.check
  obtain ⟨preds, hcfg⟩ := hc.cfg
  obtain ⟨t0, tss, hback, hss, hlab⟩ := cfg_block hcfg hvb
  cases h with
  | @op b k allocs its m w vb'' i ops outs outs' w' ctl m2 c' hvb' hi' hops' hsz' hsem hlen hho hcl hn =>
  rw [hvb] at hvb'; cases hvb'
  rw [hi] at hi'; cases hi'
  rw [hops] at hops'; cases hops'
  have hU : (((#[(⟨vr, .int, .use, .early, .reg⟩ : Operand), ⟨va, .int, .def, .early, .reg⟩,
      ⟨vb', .int, .def, .early, .reg⟩].zip (#[Reg.x nr, .x na, .x nb].map Loc.reg)).toList.filter
      (·.1.isUse)).map (m ·.2)) = [regVal s (.x nr)] := by
    have := hst.store (.reg (.x nr)) (fun r e => by cases e; exact (locOk_int hl0 |> fun ⟨_, e, _⟩ => by
      cases e; simp only [CheckCtx.locOk, Bool.and_eq_true] at hl0; exact hl0.2)) trivial
    simp [Operand.isUse, this, locVal]
  rw [hU] at hsem
  have hhs : Arm.ConditionHolds Cond.hs.bits w = Arm.ConditionHolds Cond.hs.bits s :=
    (ConditionHolds_sameWorld hst.world _).symm
  simp only [RL.sem, csem] at hsem
  rw [hhs] at hsem
  -- the successor
  have hti : t0 = MInst.jtSequence d ts (.vreg vr .int) (.vreg va .int) (.vreg vb' .int) := by
    cases hn with
    | goto hk1 _ _ =>
      rw [Array.back?_eq_getElem?, show vb.insts.size - 1 = k by omega, hi] at hback
      cases hback; rfl
    | next _ => split at hsem <;> (try split at hsem) <;> simp at hsem
    | ret h => cases h
    | halt => split at hsem <;> (try split at hsem) <;> simp at hsem
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
  cases hn with
  | next _ => split at hsem <;> (try split at hsem) <;> simp at hsem
  | ret h => cases h
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
      Arm.r .PC s' = R.pcOf jl → R.L[jl]? = some (.label (.block vs.label)) →
      (∀ f, f ≠ .PC → f ≠ .GPR (rnum na) → f ≠ .GPR (rnum nb) → Arm.r f s' = Arm.r f s) →
      s'.mem = s.mem → s'.program = s.program →
      ∃ n c'', MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k (#[Reg.x nr, .x na, .x nb].map Loc.reg) :: its, m, w⟩) c'' ∧
        Q R (iterN R.step n s) c'' := by
    intro s' n jl hn hpc' hjl hf hmem hprog
    have hsem' : R.sem (.jtSequence d ts (.vreg vr .int) (.vreg va .int) (.vreg vb' .int))
        (((#[(⟨vr, .int, .use, .early, .reg⟩ : Operand), ⟨va, .int, .def, .early, .reg⟩,
          ⟨vb', .int, .def, .early, .reg⟩].zip (#[Reg.x nr, .x na, .x nb].map Loc.reg)).toList.filter
          (·.1.isUse)).map (m ·.2)) w = some (outs, w, .goto jj) := by
      rw [hU]; simp only [RL.sem, csem, hhs]; exact hsem
    refine ⟨n, _, MStep.op (outs' := [regVal s' (.x na), regVal s' (.x nb)]) (w' := w) hvb hi hops hsz'
      hsem' hlen ⟨by rw [hout2]; rfl,
        fun h => by simp [havocFrom, MInst.keptDefs, MInst.isBranch] at h,
        fun n h => by simp [havocFrom, MInst.keptDefs, MInst.isBranch] at h; subst h; rfl⟩
      (hcl0 _) (MNext.goto hk1 hsucc hitems), ?_⟩
    rw [hstore, hn]
    exact q_entry hR hst0 hvs hitems hjl hpc' (stRel_regs hst hna hnb hna18 hnb18 hf hmem hprog)
  -- which successor
  split at hsem
  · rename_i hhs'
    simp only [Option.some.injEq, Prod.mk.injEq] at hsem
    obtain ⟨-, -, hj⟩ := hsem
    injection hj with hj
    subst hj
    obtain ⟨n, jl, hn', hjl⟩ := hmTaken hhs'
    simp only [MInst.targets, List.getElem?_cons_zero, Option.some.injEq] at hlj
    rw [hlj] at hjl
    exact fin _ n jl hn' (Arm.r_of_w_same ..) hjl
      (fun f hf _ _ => Arm.r_of_w_different hf) (by simp [Arm.ArmState.mem_w_eq_mem])
      (by simp [Arm.w_program])
  · rename_i hhs'
    split at hsem
    · rename_i hlt
      simp only [Option.some.injEq, Prod.mk.injEq] at hsem
      obtain ⟨-, -, hj⟩ := hsem
      injection hj with hj
      subst hj
      simp only [MInst.targets, List.getElem?_cons_succ] at hlj
      obtain ⟨n, jl, s', hn', hpc', hjl, hf, hmem, hprog⟩ := hmNot (by simpa using hhs') _ vs.label
        (by simp [lo64, regVal, BitVec.toNat_setWidth]) hlj
      exact fin s' n jl hn' hpc' hjl hf hmem hprog
    · cases hsem

end Backend.Proof
