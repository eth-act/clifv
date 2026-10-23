import FV.E2E.RegLevelFrame
import FV.E2E.RegLevelWrites
import FV.E2E.ExecWritesFrame

/-!
# The prologue and the return on the machine with their writes (A3, #412, slice F8b)

`RegLevelFrame`'s `iterN_steps`, `q_init` and `ret_machine` with `RL.GoodXW` (`GoodX` and the
writes `RL.WritesAt` of the unhooked instruction at the pc, which avoids the kept addresses
`R.G`): the prologue's `stp` writes the fp/lr slot (which `G` avoids, `hR.gfree`), the epilogue
has no stores.
-/

namespace Backend.Proof

open Backend E2E E2E.ExecBytes E2E.ExecFrame

/-! ## The writes of the push lines -/

/-- The single push's pre-indexed store writes 8 bytes at `sp - 16`. -/
theorem memWrites_push1 {env : Env} {int : Bool} {r : Reg} (hr : PushReg int r) {a : Arm.ArmInst}
    (h : (if int then Insn.store .store64 r (.spPreIndexed (-16))
        else Insn.fpuStore .size64 r (.spPreIndexed (-16))).toArmInst env = .ok a) (s : Arm.ArmState) :
    E2E.ExecBytes.MemWrites a s = [(spOf s - 16#64, 8)] := by
  cases r with
  | x n =>
    obtain ⟨rfl, hn⟩ := hr
    simp [Insn.toArmInst, Insn.armFields, Arm.ArmInst.norm, StoreOp.fields, ldstFields,
      Reg.encZR, show n ≤ 30 by omega, sField] at h
    subst h
    simp (config := {decide := true}) [E2E.ExecBytes.MemWrites, E2E.ExecFrame.RegImm.writes,
      E2E.ExecFrame.RegImm.ofPre, E2E.ExecFrame.RegImm.memop, E2E.ExecFrame.RegImm.addr,
      E2E.ExecFrame.RegImm.scale, Arm.BitVec.lsb, spOf, Arm.read_gpr] <;> bv_omega
  | v n =>
    obtain ⟨rfl, hn⟩ := hr
    simp [Insn.toArmInst, Insn.armFields, Arm.ArmInst.norm, ldstFields, Insn.armFields.fpLdstSize,
      Reg.encV, show n ≤ 31 by omega, sField] at h
    subst h
    simp (config := {decide := true}) [E2E.ExecBytes.MemWrites, E2E.ExecFrame.RegImm.writes,
      E2E.ExecFrame.RegImm.ofPre, E2E.ExecFrame.RegImm.memop, E2E.ExecFrame.RegImm.addr,
      E2E.ExecFrame.RegImm.scale, Arm.BitVec.lsb, spOf, Arm.read_gpr] <;> bv_omega
  | _ => exact hr.elim

/-- The pair push's pre-indexed `stp` writes 16 bytes at `sp - 16`. -/
theorem memWrites_push2 {env : Env} {int : Bool} {a b : Reg} (ha : PushReg int a) (hb : PushReg int b)
    {i : Arm.ArmInst}
    (h : (if int then Insn.stp a b (.spPreIndexed (-16))
        else Insn.fpuStoreP .size64 a b (.spPreIndexed (-16))).toArmInst env = .ok i)
    (s : Arm.ArmState) :
    E2E.ExecBytes.MemWrites i s = [(spOf s - 16#64, 16)] := by
  cases a with
  | x n =>
    cases b with
    | x m =>
      obtain ⟨rfl, hn⟩ := ha
      have hm := hb.2
      simp [Insn.toArmInst, Insn.armFields, Arm.ArmInst.norm, Reg.encZR, show n ≤ 30 by omega,
        show m ≤ 30 by omega, sField] at h
      subst h
      simp (config := {decide := true}) [E2E.ExecBytes.MemWrites, E2E.ExecFrame.RegPair.writes,
        E2E.ExecFrame.RegPair.mk, E2E.ExecFrame.RegPair.addr, E2E.ExecFrame.RegPair.scale,
        Arm.BitVec.lsb, spOf, Arm.read_gpr] <;> bv_omega
    | v m => obtain ⟨rfl, -⟩ := ha; exact absurd hb.1 (by simp)
    | _ => exact hb.elim
  | v n =>
    cases b with
    | x m => obtain ⟨rfl, -⟩ := ha; exact absurd hb.1 (by simp)
    | v m =>
      obtain ⟨rfl, hn⟩ := ha
      have hm := hb.2
      simp [Insn.toArmInst, Insn.armFields, Arm.ArmInst.norm, Insn.armFields.fpOpc,
        ScalarSize.bytes, Reg.encV, show n ≤ 31 by omega, show m ≤ 31 by omega, sField] at h
      subst h
      simp (config := {decide := true}) [E2E.ExecBytes.MemWrites, E2E.ExecFrame.RegPair.writes,
        E2E.ExecFrame.RegPair.mk, E2E.ExecFrame.RegPair.addr, E2E.ExecFrame.RegPair.scale,
        Arm.BitVec.lsb, spOf, Arm.read_gpr] <;> bv_omega
    | _ => exact hb.elim
  | _ => exact ha.elim

/-- Combining the writes of two straight-line blocks (the second runs from wherever the first
ends). -/
theorem linesWrites_app {env : Env} {A B : List Line} {s : Arm.ArmState} {P : BitVec 64 → Prop}
    (hA : LinesWrites env A s P)
    (hB : ∀ s1, execLines env A s = some s1 →
      LinesWrites { env with pc := env.pc + 4 * A.length } B s1 P) :
    LinesWrites env (A ++ B) s P := by
  intro k x t hk s1 hs1 env' a ha p hp i hi
  rcases Nat.lt_or_ge k A.length with hlt | hge
  · rw [List.getElem?_append_left hlt] at hk
    rw [List.take_append_of_le_length (by omega)] at hs1
    exact hA k x t hk s1 hs1 env' a ha p hp i hi
  · rw [List.getElem?_append_right hge] at hk
    rw [List.take_append, List.take_of_length_le hge, execLines_append] at hs1
    cases h1 : execLines env A s with
    | none => rw [h1] at hs1; cases hs1
    | some sA =>
      rw [h1] at hs1
      exact hB sA h1 _ x t hk s1 hs1 env' a ha p hp i hi

/-- The pair pushes write only `[B, B + 16 * len)`, the last pushed pair at the bottom. -/
theorem pushPairs_writes (env : Env) (int : Bool) {P : BitVec 64 → Prop} :
    ∀ (ps : List (Reg × Reg)) (s : Arm.ArmState) (B : BitVec 64),
    (∀ p ∈ ps, PushReg int p.1 ∧ PushReg int p.2) → 16 * ps.length < 2 ^ 64 →
    B.toNat % 16 = 0 → spOf s = B + BitVec.ofNat 64 (16 * ps.length) →
    (∀ k < 16 * ps.length, P (B + BitVec.ofNat 64 k)) →
    LinesWrites env (ps.reverse.map (pushLine2 int)) s P
  | [], _, _, _, _, _, _, _ => fun k _ _ hk => by simp at hk
  | p :: ps, s, B, hps, hlen, hB, hsp, hP => by
    have hsp' : spOf s = (B + 16#64) + BitVec.ofNat 64 (16 * ps.length) := by
      rw [hsp, show 16 * (ps.length + 1) = 16 + 16 * ps.length by omega, BitVec.ofNat_add,
        BitVec.add_assoc]
    obtain ⟨s1, h1, hsp1, hr1, he1, hp1, hm1, hv1⟩ :=
      pushPairs_ok env int ps s (B + 16#64) (fun q hq => hps q (List.mem_cons_of_mem _ hq)) (by omega)
        (by simpa using aligned_add hB 1) hsp'
    have hB1 : spOf s1 - 16#64 = B := by rw [hsp1]; exact BitVec.add_sub_cancel _ _
    have hal1 : Arm.CheckSPAlignment s1 := checkSP_of (by rw [hsp1]; simpa using aligned_add hB 1)
    obtain ⟨i, hi, he⟩ := exec_push2 env (hps p (by simp)).1 (hps p (by simp)).2 s1 hal1
    have hpcE : Arm.r .PC (Arm.exec_inst i s1) = Arm.r .PC s1 + 4#64 := by
      rw [he]; exact (pushSt_facts s1 16 (slotVal s1 p.2 ++ slotVal s1 p.1)).1
    have hmap : (p :: ps).reverse.map (pushLine2 int) =
        ps.reverse.map (pushLine2 int) ++ [pushLine2 int p] := by
      simp [List.reverse_cons, List.map_append]
    rw [hmap]
    refine linesWrites_app
      (pushPairs_writes env int ps s (B + 16#64)
        (fun q hq => hps q (List.mem_cons_of_mem _ hq)) (by omega)
        (by simpa using aligned_add hB 1) hsp'
        (fun k hk => by
          rw [show (B + 16#64) + BitVec.ofNat 64 k = B + BitVec.ofNat 64 (16 + k) from by
            rw [show (16#64) = BitVec.ofNat 64 16 from rfl, add_ofNat_add]
          ; congr 2; omega]
          exact hP (16 + k) (by omega)))
      fun s1' hs1' => ?_
    obtain rfl := execLines_steps h1 hs1'
    simp only [pushLine2]
    refine linesWrites_cons (fun _ _ h => by simp at h) fun env' a' ha' q hq k hk => ?_
    rw [memWrites_push2 (hps p (by simp)).1 (hps p (by simp)).2 ha' s1] at hq
    simp only [List.mem_singleton] at hq
    subst hq
    rw [hB1]
    exact hP k (by have := hk; omega)

/-- The pushes of one register class write only `[B, B + pushBytes)`. -/
theorem pushLines_writes (env : Env) (int : Bool) (rs : List Reg) (s : Arm.ArmState) (B : BitVec 64)
    (hrs : ∀ r ∈ rs, PushReg int r) (hlen : rs.length ≤ 64) (hB : B.toNat % 16 = 0)
    (hsp : spOf s = B + BitVec.ofNat 64 (pushBytes rs.length)) {P : BitVec 64 → Prop}
    (hP : ∀ k < pushBytes rs.length, P (B + BitVec.ofNat 64 k)) :
    LinesWrites env (pushLines int rs) s P := by
  have hpb := pushBytes_eq rs
  have hpbm := pushBytes_mod rs.length
  have hpb16 : pushBytes rs.length = 16 * (pushBytes rs.length / 16) := by omega
  have hpbI : pushBytes rs.length ≤ 1000 := by unfold pushBytes; omega
  obtain ⟨hmP, hmO⟩ := pairsOf_mem rs
  have hpv : ∀ p ∈ (pairsOf rs).1, PushReg int p.1 ∧ PushReg int p.2 :=
    fun p hp => ⟨hrs _ (hmP p hp).1, hrs _ (hmP p hp).2⟩
  have hPl : 16 * (pairsOf rs).1.length < 2 ^ 64 := by split at hpb <;> omega
  have hal0 : (spOf s).toNat % 16 = 0 := by
    rw [hsp, show BitVec.ofNat 64 (pushBytes rs.length)
      = BitVec.ofNat 64 (16 * (pushBytes rs.length / 16)) from by rw [hpb16]]
    simpa using aligned_add hB (pushBytes rs.length / 16)
  rw [pushLines_eq]
  rcases ho : (pairsOf rs).2 with _ | r0
  · rw [ho]
    simp only [ite_false, Bool.false_eq_true, if_true, List.nil_append]
    exact pushPairs_writes env int _ s B hpv hPl hB (by rw [hsp] at *; exact hsp) hP
  · rw [ho]
    simp only [ite_true, Bool.false_eq_true, if_true]
    have hspE : spOf s = B + BitVec.ofNat 64 (16 * (pairsOf rs).1.length + 16) := by
      rw [hsp, ← hpb]; rw [hpb] at *; omega
    obtain ⟨a, ha, he⟩ := exec_push1 env (hrs _ (hmO r0 ho)) s (checkSP_of hal0)
    have hpcE : Arm.r .PC (Arm.exec_inst a s) = Arm.r .PC s + 4#64 := by
      rw [he]; exact (pushSt_facts s 8 (slotVal s r0)).1
    have hsp1 : spOf (Arm.exec_inst a s) = spOf s - 16#64 := by
      rw [he]; exact (pushSt_facts s 8 (slotVal s r0)).2.2.2.1
    have hrun : execLines env [Line.ins (if int then Insn.store .store64 r0 (.spPreIndexed (-16))
        else Insn.fpuStore .size64 r0 (.spPreIndexed (-16))) none] s = some (Arm.exec_inst a s) :=
      execLines_one ha hpcE
    refine linesWrites_app (linesWrites_cons (fun _ _ h => by simp at h) fun env' a' ha' q hq k hk => ?_)
      fun s1' hs1' => ?_
    · rw [memWrites_push1 (hrs _ (hmO r0 ho)) ha'] at hq
      simp only [List.mem_singleton] at hq
      subst hq
      rw [show spOf s - 16#64 + BitVec.ofNat 64 k
        = B + BitVec.ofNat 64 (16 * (pairsOf rs).1.length + k) from by rw [hspE]; bv_omega]
      exact hP _ (by have := hk; simp only [pushBytes, pairsOf, ho, Option.isSome_some,
        ite_true] at hpb; omega)
    · have e : s1' = Arm.exec_inst a s := by rw [hrun] at hs1'; exact (Option.some.inj hs1').symm
      subst e
      refine pushPairs_writes { env with pc := env.pc + 4 } int _ s1' B hpv hPl hB ?_ hP
      rw [hsp1, hspE, show B + BitVec.ofNat 64 (16 * (pairsOf rs).1.length + 16) - 16#64
        = B + BitVec.ofNat 64 (16 * (pairsOf rs).1.length) from by bv_omega]

/-- The prologue writes only the frame top `[sp - 16 - clobberBytes, sp)`. -/
theorem prologue_writes (env : Env) {saves : List Reg} {size : Nat} (hs : size < 2 ^ 64)
    (hsv : SavesOk saves) (hcb : clobberBytes saves ≤ size) (s : Arm.ArmState)
    (hal : (spOf s).toNat % 16 = 0) {P : BitVec 64 → Prop}
    (hP : ∀ k < 16 + clobberBytes saves,
      P (spOf s - BitVec.ofNat 64 (16 + clobberBytes saves) + BitVec.ofNat 64 k)) :
    LinesWrites env (prologueLines saves size) s P := by
  have hcbm := clobberBytes_mod saves
  have hcbe : clobberBytes saves = pushBytes (savesInt saves).length +
      pushBytes (savesFloat saves).length := rfl
  have hpIm := pushBytes_mod (savesInt saves).length
  have hpFm := pushBytes_mod (savesFloat saves).length
  have hpIl : pushBytes (savesInt saves).length ≤ 1000 := by unfold pushBytes; omega
  have hpFl : pushBytes (savesFloat saves).length ≤ 1000 := by unfold pushBytes; omega
  generalize hBF : spOf s - BitVec.ofNat 64 (16 + clobberBytes saves) = BF
  have hBFa : BF.toNat % 16 = 0 := by rw [← hBF]; exact aligned_sub hal (by omega) (by omega)
  have hBIa : (BF + BitVec.ofNat 64 (pushBytes (savesFloat saves).length)).toNat % 16 = 0 := by
    rw [show pushBytes (savesFloat saves).length = 16 * (pushBytes (savesFloat saves).length / 16) by omega]
    exact aligned_add hBFa _
  have hBFc : BF + BitVec.ofNat 64 (clobberBytes saves) = spOf s - 16#64 := by
    rw [← hBF, hcbe, show 16 + (pushBytes (savesInt saves).length +
      pushBytes (savesFloat saves).length) =
      16 + pushBytes (savesInt saves).length + pushBytes (savesFloat saves).length by omega,
      BitVec.ofNat_add]
    bv_omega
  have hT16 : spOf s - 16#64 = BF + BitVec.ofNat 64 (pushBytes (savesFloat saves).length) +
      BitVec.ofNat 64 (pushBytes (savesInt saves).length) := by
    rw [← hBF, hcbe, show 16 + (pushBytes (savesInt saves).length + pushBytes (savesFloat saves).length)
      = 16 + pushBytes (savesInt saves).length + pushBytes (savesFloat saves).length by omega,
      BitVec.ofNat_add, BitVec.ofNat_add]
    bv_omega
  -- the runs of the first two lines
  have hal0 : Arm.CheckSPAlignment s := checkSP_of hal
  obtain ⟨a1, ha1, he1⟩ := exec_stp_fplr env s hal0
  obtain ⟨a2, ha2, he2⟩ := exec_mov_fp_sp { env with pc := env.pc + 4 } (Arm.exec_inst a1 s)
  have hpc1 : Arm.r .PC (Arm.exec_inst a1 s) = Arm.r .PC s + 4#64 := by
    rw [he1]; simp [Arm.r_of_w_same, Arm.r_of_w_different]
  have hsp1 : spOf (Arm.exec_inst a1 s) = spOf s - 16#64 := by
    rw [he1]; simp [spOf, Arm.r_of_w_same, Arm.r_of_w_different]
  have hrun1 : execLines env [Line.ins (.stp Reg.fp Reg.lr (.spPreIndexed (-16))) none] s =
      some (Arm.exec_inst a1 s) := execLines_one ha1 hpc1
  have hpc2 : Arm.r .PC (Arm.exec_inst a2 (Arm.exec_inst a1 s)) =
      Arm.r .PC (Arm.exec_inst a1 s) + 4#64 := by
    rw [he2]; simp [Arm.r_of_w_same, Arm.r_of_w_different]
  have hsp2 : spOf (Arm.exec_inst a2 (Arm.exec_inst a1 s)) = spOf s - 16#64 := by
    rw [he2]; simp only [spOf] at hsp1 ⊢; simp [Arm.r_of_w_different, hsp1]
  have hrun2 : execLines env [Line.ins (.stp Reg.fp Reg.lr (.spPreIndexed (-16))) none,
      Line.ins (.mov true Reg.fp .sp) none] s =
      some (Arm.exec_inst a2 (Arm.exec_inst a1 s)) := by
    rw [execLines_cons_of hrun1 [Line.ins (.mov true Reg.fp .sp) none]]
    exact execLines_one ha2 hpc2
  simp only [prologueLines]
  refine linesWrites_app
    (linesWrites_app
      (linesWrites_cons (fun _ _ h => by simp at h) fun env' a' ha' q hq k hk => ?_)
      (fun s1 hs1 => linesWrites_noStores fun x t hx => by
        rcases List.mem_cons.1 hx with hEq | h'
        · injection hEq with hEq1 hEq2 <;> subst hEq1 <;> subst hEq2 <;> rfl
        · cases h'))
    ?_
  · rw [memWrites_stp_pre ha' s] at hq
    simp only [List.mem_singleton] at hq
    subst hq
    rw [← hBFc, ← BitVec.add_assoc, add_ofNat_add]
    exact hP (clobberBytes saves + k) (by have := hk; omega)
  · -- the int pushes
    intro s1 hs1'
    obtain rfl : s1 = Arm.exec_inst a2 (Arm.exec_inst a1 s) := by
      rw [hrun2] at hs1'; exact (Option.some.inj hs1').symm
    refine pushLines_writes { env with pc := env.pc + 8 } true (savesInt saves) s1
      (BF + BitVec.ofNat 64 (pushBytes (savesFloat saves).length)) hsv.int
      (by have := hsv.intLen; omega) hBIa ?_ (fun k hk => ?_)
    · rw [hsp2, hT16]
    · rw [add_ofNat_add]
      exact hP (pushBytes (savesFloat saves).length + k) (by omega)
  · -- the float pushes and the `sub sp`
    intro s2 hs2'
    obtain ⟨s3, h3, hsp3, -, -, -, -, -⟩ := pushLines_ok
      { env with pc := env.pc + 8 + 4 * (pushLines true (savesInt saves)).length } false
      (savesFloat saves) s1 BF hsv.float (by have := hsv.floatLen; omega) hBFa
      (by rw [hsp2, hT16])
    obtain rfl := execLines_steps h3 hs2'
    refine linesWrites_app (pushLines_writes
      { env with pc := env.pc + 8 + 4 * (pushLines true (savesInt saves)).length } false
      (savesFloat saves) s3 BF hsv.float (by have := hsv.floatLen; omega) hBFa hsp3
      (fun k hk => hP k (by omega))) fun s4 hs4 => ?_
    obtain ⟨s5, h5, hsp5, ho5, hm5⟩ := spAdj_ok
      { env with pc := env.pc + 8 + 4 * (pushLines true (savesInt saves)).length +
        4 * (pushLines false (savesFloat saves)).length } true
      (size := size - clobberBytes saves) (by omega) s3
    obtain rfl := execLines_steps h5 hs4
    exact linesWrites_noStores (fun x t hx => by
      rcases List.mem_append.1 hx with h | h
      · simp only [spAdjLines, List.mem_append] at h
        split at h
        · cases h
        · split at h
          · rcases List.mem_cons.1 h with hEq | h'
            · injection hEq with hEq1 hEq2 <;> subst hEq1 <;> subst hEq2 <;> rfl
            · cases h'
          · rcases List.mem_append.1 h with h | h
            · exact loadConst64_noStores _ _ x t h
            · rcases List.mem_cons.1 h with hEq | h'
              · injection hEq with hEq1 hEq2 <;> subst hEq1 <;> subst hEq2 <;> rfl
              · cases h'
      · simp only [List.mem_singleton, Line.ins.injEq] at h
        obtain rfl := h; rfl)

/-- Straight-line lines at line `j` of the final code run as machine steps. -/
theorem iterN_stepsW {R : RL} (hR : R.Wf) {ls T : List Line} {j : Nat} {s s' : Arm.ArmState}
    (hdrop : R.L.drop j = ls ++ T)
    (hins : ∀ ln ∈ ls, ∃ x, ln = .ins x none ∧ x.hooked = false)
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j)
    (herr : Arm.r .ERR s = .None) (h : StepsOk (R.envOf j) ls s s') :
    iterN R.step ls.length s = s' ∧ Arm.r .PC s' = R.pcOf (j + ls.length) ∧
      (∀ i, 0 < i → i ≤ ls.length → R.Good (iterN R.step i s)) ∧
      ((∀ i t, Line.ins i t ∈ ls → i.tlsTail = false) → R.Good s →
        LinesReads (R.envOf j) ls s R.ReadOk →
        LinesWrites (R.envOf j) ls s (fun a => ¬ R.G a) →
          ∀ i < ls.length, R.GoodXW (iterN R.step i s)) := by
  have hat : ∀ k ln, ls[k]? = some ln → R.fa.lines.toList[j + k]? = some ln := by
    intro k ln hk
    have := congrArg (·[k]?) hdrop
    simp only [List.getElem?_drop, RL.L] at this
    rw [this, List.getElem?_append_left (List.getElem?_eq_some_iff.1 hk).1]
    exact hk
  have hins' : ∀ ln ∈ ls, ∃ i t, ln = .ins i t := fun ln h => by
    obtain ⟨x, e, -⟩ := hins ln h; exact ⟨x, none, e⟩
  have hhook : ∀ i t, Line.ins i t ∈ ls → i.hooked = false := fun i t hm => by
    obtain ⟨x, e, hh⟩ := hins _ hm; cases e; exact hh
  have hrun := h.exec
  refine ⟨iterN_execLines hR.layout hR.lm hR.fit ls j s s' hat hhook
      hprog (by rw [hpc]; rfl) herr (stepsOk_interOk h herr) hrun, ?_,
    R.good_execLines hR hat hhook hprog hpc herr (stepsOk_interOk h herr) hrun,
    fun htail h0 hrd hwr => R.goodXW_execLinesG hR hat hhook htail hprog hpc herr h0
      (stepsOk_interOk h herr) hrun hrd hwr⟩
  rw [execLines_pc hrun, hpc]
  simp only [RL.pcOf, RL.L]
  rw [lineOffset_drop_ins (by simpa [RL.L] using hdrop) hins', BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add]

/-- **After the prologue**: the machine is at the entry configuration of the allocated code
(store = the machine's locations, world = any body-entry world `w₀`), `AInv` holds, and every
field but the pc, x16, x29 and `sp` is as at entry. -/
theorem q_initW {R : RL} (hR : R.Wf) {ra : BitVec 64} (hent : AbiCall R.fb R.base ra R.s0)
    {w₀ : Arm.ArmState} (hbe : BodyEntryW R.F R.vc.EntryArg R.af R.s0 w₀) :
    ∃ n, (∀ i < n, R.GoodXW (iterN R.step i R.s0)) ∧
      Q R (iterN R.step n R.s0) (MConf.init R.rf (locVal R.fr (iterN R.step n R.s0)) w₀) ∧
      AInv R (MConf.init R.rf (locVal R.fr (iterN R.step n R.s0)) w₀) ∧
      ∀ f, f ≠ .PC → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 → f ≠ .GPR 16#5 →
        Arm.r f (iterN R.step n R.s0) = Arm.r f R.s0 := by
  obtain ⟨hframe, hfs, -, hsv, -, hcb, -, -, hdrop0⟩ := RL.frame_facts hR
  have hst0 := hR.stack.frame
  have hsp0 := (spv R.s0).isLt
  have hs : R.af.frameSize < 2 ^ 64 := by have := hst0.1; omega
  obtain ⟨vb, items, code, ls, ps1, ps2, T, hvb, hit, hcode, hls, htr, hj0, hdrop⟩ := entry_block hR
  obtain ⟨s', hsteps, hsp', hfp', ho', hm', -, -⟩ :=
    prologue_ok (R.envOf 1) hs hsv (by rw [hfs]; exact hcb) R.s0 hent.spAligned
  have hpc1 : Arm.r .PC R.s0 = R.pcOf 1 := by
    rw [hent.pc]
    simp only [RL.pcOf, RL.L] at hj0 ⊢
    rw [lineOffset_succ _ _ _ hj0]
    simp [lineOffset, Line.size]
  obtain ⟨hiter, hpc', -, hgx⟩ := iterN_stepsW hR hdrop
    (fun ln h => by obtain ⟨x, e, hh, -⟩ := prologueLines_ins _ _ ln h; exact ⟨x, e, hh⟩)
    hent.program hpc1 hent.err hsteps
  obtain ⟨herr', hprog'⟩ := hsteps.err
  -- the prologue's writes: the frame top, which `G` avoids
  have hwrP : LinesWrites (R.envOf 1) (prologueLines R.af.saves R.af.frameSize) R.s0 (fun a => ¬ R.G a) := by
    refine prologue_writes _ hs hsv (by rw [hfs]; exact hcb) R.s0 hent.spAligned ?_
    intro k hk
    show ¬ R.G (spv R.s0 - BitVec.ofNat 64 (16 + clobberBytes R.af.saves) + BitVec.ofNat 64 k)
    have hkN : k < R.topN := by simp only [RL.topN]; exact hk
    rw [show (spv R.s0 - BitVec.ofNat 64 (16 + clobberBytes R.af.saves) + BitVec.ofNat 64 k)
      = R.topB + BitVec.ofNat 64 k from by simp only [RL.topB, RL.topN]]
    exact fun hG => hR.gfree _ hG (RL.top_notG hR k hkN)
  refine ⟨(prologueLines R.af.saves R.af.frameSize).length,
    hgx (prologueLines_tail R.af.saves) (.inl (by rw [hent.pc]; exact RL.not_postCall_base hR hent.fits))
      (linesReads_noLoads (prologueLines_noLoads R.af.saves)) hwrP, ?_⟩
  have hsP : R.sP = s' := hiter
  rw [hiter]
  have hspB : spOf s' = R.spB := by
    rw [hsp', RL.spB, hdrop0, ← hfs]; exact sp_sub16 _ _
  have htopB : R.topB.toNat = (spv R.s0).toNat - R.topN := by
    simp only [RL.topB, RL.topN]
    have := hst0.1
    rw [BitVec.toNat_sub_of_le] <;>
      simp only [BitVec.le_def, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show 16 + clobberBytes R.af.saves < 2 ^ 64 by omega)]
    omega
  have hk64 : ∀ k < R.topN, (R.topB + BitVec.ofNat 64 k).toNat = (spv R.s0).toNat - R.topN + k := by
    intro k hk
    simp only [RL.topN] at hk
    have := hst0.1
    have hkl : k < 2 ^ 64 := by rw [hfs] at this; omega
    rw [BitVec.toNat_add, htopB, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) hkl]
    simp only [RL.topN]
    rw [hfs] at this
    omega
  -- the frame top
  have hslot : ∀ a, (∀ k < R.topN, a ≠ R.topB + BitVec.ofNat 64 k) → s'.mem a = R.s0.mem a :=
    fun a ha => hm' a ha
  have hmemF : ∀ a, ¬ R.F a → s'.mem a = w₀.mem a := by
    intro a ha
    rw [hslot a (fun k hk e => ha (e ▸ RL.FK_F (fplr_inF hR hframe k hk))), hbe.mem a ha]
  have hcode' : ∀ a, CodeAddr R.s0 a → s'.mem a = R.s0.mem a := by
    intro a ha
    apply hslot
    intro k hk e
    have h2 := hst0.2 a ha
    rw [e] at h2
    have hk' := hk64 k hk
    have := hst0.1
    simp only [RL.topN] at hk hk'
    have hin : (spv R.s0 - BitVec.ofNat 64 (R.af.frameSize + 16)).toNat =
        (spv R.s0).toNat - (R.af.frameSize + 16) := by
      have hm : (R.af.frameSize + 16) % 2 ^ 64 = R.af.frameSize + 16 := Nat.mod_eq_of_lt (by omega)
      rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat, hm]; omega),
        BitVec.toNat_ofNat, hm]
    rw [BitVec.toNat_sub, hk', hin] at h2
    have e2 : (2 ^ 64 - ((spv R.s0).toNat - (R.af.frameSize + 16)) +
        ((spv R.s0).toNat - (16 + clobberBytes R.af.saves) + k)) % 2 ^ 64 =
        (spv R.s0).toNat - (16 + clobberBytes R.af.saves) + k -
          ((spv R.s0).toNat - (R.af.frameSize + 16)) := by
      rw [show 2 ^ 64 - ((spv R.s0).toNat - (R.af.frameSize + 16)) +
          ((spv R.s0).toNat - (16 + clobberBytes R.af.saves) + k) =
        ((spv R.s0).toNat - (16 + clobberBytes R.af.saves) + k -
          ((spv R.s0).toNat - (R.af.frameSize + 16))) + 2 ^ 64 by rw [hfs] at this ⊢; omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by rw [hfs] at this ⊢; omega)]
    rw [e2] at h2
    rw [hfs] at this h2
    omega
  have hfield : ∀ f, f ≠ .PC → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 → f ≠ .GPR 16#5 →
      Arm.r f s' = Arm.r f R.s0 := ho'
  -- the kept addresses are not the frame top
  have hgk : ∀ a, R.G a → s'.mem a = R.s0.mem a := by
    intro a ha
    apply hslot
    intro k hk e
    apply hR.gfree a ha
    rw [e, hdrop0]
    have := hst0.1
    have hk' := hk64 k hk
    simp only [RL.topN] at hk hk'
    simp only [StackBelow, hk']
    rw [hfs] at this
    constructor <;> omega
  refine ⟨?_, ?_, hfield⟩
  · have hitems : R.rf.blocks[0]! = items := by simp [getElem!_def, hit]
    simp only [MConf.init, hitems]
    refine ⟨1 + (prologueLines R.af.saves R.af.frameSize).length, vb, items, [], code, ls, ps1, ps2, T, hvb,
      hit, rfl, itemsChecked_block hR hvb hit, hcode, hls, htr, ?_, hpc', ?_⟩
    · rw [← List.drop_drop, hdrop, List.drop_left]
    · refine ⟨fun l _ _ => rfl, ⟨fun f hf => ?_, hmemF, ?_⟩, by rw [herr', hent.err], by rw [hprog', hent.program],
        hspB, ?_, fun _ => ?_, code_keep hR.prog0 hent.code hcode', hgk⟩
      · by_cases h29 : f = .GPR 29#5
        · subst h29
          have := hbe.fp
          simp only [hframe, ite_true, xreg] at this hfp'
          rw [hfp', this]; rfl
        by_cases h31 : f = .GPR 31#5
        · subst h31
          have := hbe.sp
          simp only [spv] at this
          rw [this]; exact hspB
        have h16 : f ≠ .GPR 16#5 := by rintro rfl; exact hf (by simp [Masked])
        have hpc : f ≠ .PC := by rintro rfl; exact hf trivial
        rw [hfield f hpc h29 h31 h16, hbe.other f hf h29 h31]
      · rw [hprog', hbe.program]
      · rw [checkSP_iff, hspB]
        simp only [RL.spB, hdrop0]
        have := hst0.1
        have ha := hent.spAligned
        rw [hfs] at this
        have hm : (R.fr.total + 16) % 2 ^ 64 = R.fr.total + 16 := Nat.mod_eq_of_lt (by omega)
        rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat, hm]; simp only [spv] at *; omega),
          BitVec.toNat_ofNat, hm]
        have : R.fr.total % 16 = 0 := (RL.frame_facts hR).2.2.2.2.2.2.1
        simp only [spv, spOf] at *
        omega
      · simp only [RL.topImg, hsP]
  · intro _ _ r hr
    show regVal s' r = regVal w₀ r
    rw [hbe.args r hr]
    obtain ⟨vb', ds, hvb', hi', v, hv⟩ := hr
    have hr := ((ctlCheck_args (lowerRFunc_ok hR.alloc).2.2 hvb' hi').2.2 _ hv).2
    cases r with
    | x n =>
      simp only [Reg.isArgReg, decide_eq_true_eq] at hr
      have hne : ∀ m, 8 < m → m < 32 → Arm.StateField.GPR (rnum n) ≠ .GPR (BitVec.ofNat 5 m) :=
        fun m h1 h2 e => rnum_ne (a := n) (b := m) (by omega) h2 (by omega) (Arm.StateField.GPR.inj e)
      simp only [regVal]
      rw [hfield _ (by simp) (hne 29 (by omega) (by omega)) (hne 31 (by omega) (by omega))
        (hne 16 (by omega) (by omega))]
    | v n =>
      simp only [regVal]
      rw [hfield _ (by simp) (by simp) (by simp) (by simp)]
    | _ => simp [Reg.isArgReg] at hr

/-- **The return on the machine**: from `Q` at a `Rets` item, the epilogue and `ret` reach the
return address with `sp` and x29 as at entry, the allocatable registers and the memory as at
the item, and the returned values in their fixed registers. -/
theorem ret_machineW {R : RL} (hR : R.Wf) {ra : BitVec 64} (hent : AbiCall R.fb R.base ra R.s0)
    {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc} {its : List RItem} {m : Loc → CV}
    {w : Arm.ArmState} (hqa : QA R s (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock}
    {us : List (Reg × Reg)} (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some (.rets us)) :
    ∃ n, (∀ i < n, R.GoodXW (iterN R.step i s)) ∧
      Arm.r .PC (iterN R.step n s) = ra ∧ Arm.r .ERR (iterN R.step n s) = .None ∧
      spv (iterN R.step n s) = spv R.s0 ∧ xreg 29 (iterN R.step n s) = xreg 29 R.s0 ∧
      (∀ r, r.allocatable = true → r ∉ R.af.saves → regVal (iterN R.step n s) r = m (.reg r)) ∧
      (∀ r ∈ R.af.saves, slotVal (iterN R.step n s) r = slotVal R.s0 r) ∧
      (iterN R.step n s).mem = s.mem ∧
      (∀ f, ¬ Masked f → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 → Arm.r f (iterN R.step n s) = Arm.r f s) ∧
      (iterN R.step n s).program = s.program ∧
      ∀ ops, (MInst.rets us).operands = .ok ops → ∀ (j : Nat) (v p : Reg) (x : CV), us[j]? = some (v, p) →
        ((((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)))[j]? = some x →
        regVal (iterN R.step n s) p = x := by
  have hframe := lowerRFunc_frame hR.alloc
  have hck := (lowerRFunc_ok hR.alloc).2.2
  obtain ⟨-, hfs, hsav, hsv, -, hcb, -, -, -⟩ := RL.frame_facts hR
  have hst0 := hR.stack.frame
  have hsp0 := (spv R.s0).isLt
  have hs : R.af.frameSize < 2 ^ 64 := by have := hst0.1; omega
  have hcb' : clobberBytes R.af.saves ≤ R.af.frameSize := by rw [hfs]; exact hcb
  -- the machine's store `mt`: `m` but at the restored registers `D`
  obtain ⟨mt, D, hq, hmD, hDs⟩ : ∃ (mt : Loc → CV) (D : List Reg), Q R s (.run ⟨b, .op k allocs :: its, mt, w⟩) ∧
      (∀ l, (∀ r ∈ D, l ≠ .reg r) → m l = mt l) ∧ ∀ r ∈ D, r ∈ R.af.saves := by
    unfold QA at hqa
    rcases hqa with ⟨hq, -⟩ | h
    · refine ⟨m, [], hq, fun _ _ => rfl, ?_⟩
      simp
    · simp only [RetTail, TailOk] at h
      obtain ⟨mt, D, hq, hm, _, _, _, _, _, _, -, -, -, htl⟩ := h
      exact ⟨mt, D, hq, hm, fun r hr => by rw [hsav]; exact (retTailOk_prefix htl).subset hr⟩
  obtain ⟨j0, items, pre, regs, i', c1, c2, ls1, ls2, ps1, psm, ps2, T, cc, wh, ops, rfl, hit, hsplit,
    hasg, hc1', hops, hstat, hchk', hc2, h1, h2, htr, hdrop, hpc, hst⟩ := q_op hq hvb hi
  obtain ⟨us', rfl⟩ := assign_rets hasg
  obtain rfl : c1 = [.epilogueRet] := by
    rcases hc1' with ⟨-, -, h⟩ | ⟨_, h, -⟩ | ⟨_, -, h⟩
    · exact absurd rfl (h us')
    · cases h
    · exact h
  simp only [codeLinesE, ainstLines, hframe, ite_true, bind, Except.bind, pure, Except.pure,
    List.append_nil, Except.ok.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  rw [epilogueLines_epi] at hdrop
  have hpl : ∀ ln ∈ epiLines R.af.saves R.af.frameSize ++ [Line.ins .ret none], ln.plain = true := by
    intro ln hln
    rcases List.mem_append.1 hln with hln | hln
    · obtain ⟨_, _, _, hp, -⟩ := epiLines_ins _ _ ln hln; exact hp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hln
      rcases hln with rfl | rfl <;> rfl
  rw [ftR_plain_append _ _ _ hpl (noTrap_next h2)] at hdrop
  have hdrop' : R.L.drop j0 = epiLines R.af.saves R.af.frameSize ++
      (.ins .ret none :: (relaxLines R.far (ftList (ls2 ++ nxtOf R.af b)) ++ T)) := by
    rw [hdrop]; simp
  -- `sp + size - clobberBytes` is the bottom of the clobber area, `sp + size` the fp/lr slot
  have hdrop0 : frameDrop R.af = R.af.frameSize + 16 := by simp [frameDrop, hframe]
  have hslot : spOf s + BitVec.ofNat 64 R.af.frameSize = spv R.s0 - 16#64 := by
    rw [hst.sp, RL.spB, hdrop0, BitVec.ofNat_add]; bv_omega
  have hB : spOf s + BitVec.ofNat 64 (R.af.frameSize - clobberBytes R.af.saves) = R.topB := by
    obtain ⟨d, hd⟩ : ∃ d, R.af.frameSize = d + clobberBytes R.af.saves :=
      ⟨_, (Nat.sub_add_cancel hcb').symm⟩
    rw [hst.sp, RL.spB, RL.topB, RL.topN, hdrop0, hd, Nat.add_sub_cancel,
      show d + clobberBytes R.af.saves + 16 = d + (16 + clobberBytes R.af.saves) by omega,
      BitVec.ofNat_add, BitVec.ofNat_add]
    bv_omega
  have htopcb : R.topB + BitVec.ofNat 64 (clobberBytes R.af.saves) = spv R.s0 - 16#64 := by
    rw [RL.topB, RL.topN, BitVec.ofNat_add]; bv_omega
  have hal : (spOf s + BitVec.ofNat 64 (R.af.frameSize - clobberBytes R.af.saves)).toNat % 16 = 0 := by
    rw [hB]
    have := hent.spAligned
    have := clobberBytes_mod R.af.saves
    have h16 : 16 + clobberBytes R.af.saves ≤ (spv R.s0).toNat := by have := hst0.1; omega
    have hm : (16 + clobberBytes R.af.saves) % 2 ^ 64 = 16 + clobberBytes R.af.saves :=
      Nat.mod_eq_of_lt (by omega)
    simp only [RL.topB, RL.topN] at this ⊢
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat, hm]; exact h16),
      BitVec.toNat_ofNat, hm]
    omega
  obtain ⟨s1, hsteps, hsp1, hx29, hx30, ho1, hm1, hpop⟩ :=
    epilogue_ok (R.envOf j0) hs hsv hcb' s hal
  -- the reads: the `ldp` reads the fp/lr slot, which is not kept
  have hrdE : LinesReads (R.envOf j0) (epiLines R.af.saves R.af.frameSize) s R.ReadOk := by
    refine linesReads_append_last (spAdjLines_noLoads false _) fun s1' hs1' env' a ha p hp k hk => ?_
    obtain ⟨s2, h2, hsp2, -, -⟩ := spAdj_ok (R.envOf j0) false hs s
    rw [h2.exec] at hs1'
    cases hs1'
    rw [memReads_ldp_fplr ha] at hp
    simp only [List.mem_singleton] at hp
    subst hp
    simp only [Bool.false_eq_true, ite_false] at hsp2
    simp only at hk ⊢
    rw [hsp2, hslot]
    refine .inl fun hG => hR.gfree _ hG ?_
    rw [hdrop0]
    have := hst0.1
    have hk64 : (spv R.s0 - 16#64 + BitVec.ofNat 64 k).toNat = (spv R.s0).toNat - 16 + k := by
      simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
      have := (spv R.s0).isLt
      rw [Nat.mod_eq_of_lt (a := k) (by omega)]
      simp only [spv] at *
      omega
    simp only [StackBelow, hk64]
    constructor <;> omega
  obtain ⟨hiter, hpc1, hgood, hgx⟩ := iterN_stepsW hR hdrop'
    (fun ln h => by
      rcases List.mem_append.1 h with h | h
      · obtain ⟨x, e, hh, -⟩ := spAdjLines_ins false _ ln h; exact ⟨x, e, hh⟩
      · simp only [List.mem_singleton] at h; exact ⟨_, h, rfl⟩)
    hst.prog hpc hst.err hsteps
  obtain ⟨herr1, hprog1⟩ := hsteps.err
  -- the epilogue's writes: no stores
  have hwrE : LinesWrites (R.envOf j0) (epiLines R.af.saves R.af.frameSize) s (fun a => ¬ R.G a) :=
    linesWrites_noStores (fun x t hx => by
      rcases List.mem_append.1 hx with h | h
      · simp only [spAdjLines, List.mem_append] at h
        split at h
        · cases h
        · split at h
          · rcases List.mem_cons.1 h with hEq | h'
            · injection hEq with hEq1 hEq2 <;> subst hEq1 <;> subst hEq2 <;> rfl
            · cases h'
          · rcases List.mem_append.1 h with h | h
            · exact loadConst64_noStores _ _ x t h
            · rcases List.mem_cons.1 h with hEq | h'
              · injection hEq with hEq1 hEq2 <;> subst hEq1 <;> subst hEq2 <;> rfl
              · cases h'
      · simp only [List.mem_singleton, Line.ins.injEq] at h
        obtain ⟨rfl, -⟩ := h; rfl)
  -- the `ret`
  have hj : R.fa.lines.toList[j0 + (epiLines R.af.saves R.af.frameSize).length]? = some (Line.ins .ret none) := by
    have := congrArg (·[(epiLines R.af.saves R.af.frameSize).length]?) hdrop'
    simpa [List.getElem?_drop, RL.L] using this
  obtain ⟨a, ha, hstep⟩ := armStepX_ins (X := R.X) (H := R.H) hR.layout hR.lm hR.fit hj rfl
    (by rw [hprog1, hst.prog]) hpc1 (by rw [herr1, hst.err])
  obtain ⟨a', ha', he'⟩ := exec_ret ⟨lineOffset R.fa.lines.toList (j0 + (epiLines R.af.saves R.af.frameSize).length), (R.lm[·]?)⟩ s1
  rw [ha] at ha'; cases ha'
  have hfin : iterN R.step ((epiLines R.af.saves R.af.frameSize).length + 1) s = Arm.w .PC (xreg 30 s1) s1 := by
    rw [iterN_one_succ, hiter]; exact hstep.trans he'
  have hfplr := hst.fplr hframe
  rw [← hslot] at hfplr
  have hregs : ∀ r, r.allocatable = true → regVal (Arm.w .PC (xreg 30 s1) s1) r = regVal s r := by
    intro r hr
    rw [regVal_w (by rcases allocatable_cases hr with ⟨n, rfl, _⟩ | ⟨n, rfl, _⟩ <;> simp [Reg.field])]
    rcases allocatable_cases hr with ⟨n, rfl, hn⟩ | ⟨n, rfl, hn⟩
    · have hne : ∀ q, q < 32 → q ≠ n → Arm.StateField.GPR (rnum n) ≠ .GPR (BitVec.ofNat 5 q) :=
        fun q h1 h2 e => rnum_ne (a := n) (b := q) (by omega) h1 (Ne.symm h2) (Arm.StateField.GPR.inj e)
      simp only [regVal]
      rw [ho1 _ (by simp) (hne 29 (by omega) (by omega)) (hne 30 (by omega) (by omega))
        (hne 31 (by omega) (by omega)) (hne 16 (by omega) (by omega))]
    · simp only [regVal]
      rw [ho1 _ (by simp) (by simp) (by simp) (by simp) (by simp)]
  refine ⟨(epiLines R.af.saves R.af.frameSize).length + 1,
    fun i hi => ?_, ?_⟩
  · rcases Nat.lt_or_ge i (epiLines R.af.saves R.af.frameSize).length with hi1 | hi1
    · refine hgx (fun x t h => ?_) (RL.good_of_sp hst.sp) hrdE hwrE i hi1
      rcases List.mem_append.1 h with h | h
      · exact spAdjLines_tail false _ x t h
      · simp only [List.mem_singleton, Line.ins.injEq] at h
        obtain ⟨rfl, -⟩ := h; rfl
    · obtain rfl : i = (spAdjLines false R.af.frameSize ++
          [Line.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16)) none]).length := by omega
      rw [hiter]
      refine ⟨RL.goodX_ofIns hR hj hpc1 rfl rfl ?_ (by rw [herr1, hst.err]) (by rw [hprog1, hst.prog])
        (by
          rw [show R.step s1 = Arm.w .PC (xreg 30 s1) s1 from hstep.trans he']
          exact RL.nextOk_ret (by
            rw [Arm.r_of_w_same, hx30, hfplr, BitVec.extractLsb'_append_eq_left]))
        (RL.readsAt_noLoad hR hj hpc1 rfl),
        RL.writesAt_noStore hR hj hpc1 rfl⟩
      rw [← hiter]
      exact hgood _ (by simp) (Nat.le_refl _)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hfin]
  · rw [Arm.r_of_w_same, hx30, hfplr, BitVec.extractLsb'_append_eq_left, hent.lr]
  · rw [Arm.r_of_w_different (by simp), herr1, hst.err]
  · simp only [spv]
    rw [Arm.r_of_w_different (by simp)]
    show spOf s1 = spv R.s0
    rw [hsp1, hslot, BitVec.sub_add_cancel]
  · simp only [xreg]
    rw [Arm.r_of_w_different (by simp)]
    have := hx29
    simp only [xreg] at this
    rw [this, hfplr, BitVec.extractLsb'_append_eq_right]
    rfl
  · exact hregs
  · rw [Arm.ArmState.mem_w_eq_mem, hm1]
  · intro f hf h29 h31
    have hpc : f ≠ .PC := by rintro rfl; exact hf trivial
    rw [Arm.r_of_w_different hpc]
    exact ho1 f hpc h29 (by rintro rfl; exact hf (by simp [Masked])) h31
      (by rintro rfl; exact hf (by simp [Masked]))
  · rw [Arm.w_program, hprog1]
  · intro ops' hops' j v p x hj hx
    obtain ⟨ns, rfl⟩ := ctlCheck_rets hck hvb hi
    rw [operands_retsC] at hops' hops
    cases hops'
    cases hops
    obtain ⟨hsz, hloc, -, -⟩ := checkStatic_facts hstat
    obtain ⟨rfl, q, hq, hq2⟩ := rets_usesC (fun q hq r hr => (hloc q hq).2 r hr) hsz j v p x hj hx
    have hal : p.allocatable = true := by
      have := (hloc q hq).1
      rw [hq2] at this
      simp only [CheckCtx.locOk, Bool.and_eq_true] at this
      exact this.2
    rw [hregs p hal, hst.store (.reg p) (fun r e => by cases e; exact hal) trivial]
    rfl


end Backend.Proof
