import FV.E2E.RegLevelMove
import FV.E2E.ExecWritesFrame

/-!
# The memory writes of the prologue's pushes (#549)

Cranelift's prologue (`prologueLines saves size`: `stp x29, x30, [sp, #-16]!`, `mov x29, sp`, the
pre-indexed pushes of the saved registers, `sub sp`) writes only the bytes just below the entry
`sp`: fp/lr and the clobber area `[sp - 16 - clobberBytes saves, sp)` (`prologue_writes`). The
pushes of one register class write `[B, B + pushBytes)` when they start at `sp = B + pushBytes`
(`pushLines_writes`, by induction over the pairs, `pushPairs_writes`: each push lowers `sp` by 16
and writes at the new `sp`).
-/

namespace Backend.Proof

open Backend E2E E2E.ExecBytes E2E.ExecFrame

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
      E2E.ExecFrame.RegImm.scale, Arm.LDST.Reg_offset.value, Arm.BitVec.lsb, spOf,
      Arm.read_gpr] <;> bv_omega
  | v n =>
    obtain ⟨rfl, hn⟩ := hr
    simp [Insn.toArmInst, Insn.armFields, Arm.ArmInst.norm, ldstFields, Insn.armFields.fpLdstSize,
      Reg.encV, show n ≤ 31 by omega, sField] at h
    subst h
    simp (config := {decide := true}) [E2E.ExecBytes.MemWrites, E2E.ExecFrame.RegImm.writes,
      E2E.ExecFrame.RegImm.ofPre, E2E.ExecFrame.RegImm.memop, E2E.ExecFrame.RegImm.addr,
      E2E.ExecFrame.RegImm.scale, Arm.LDST.Reg_offset.value, Arm.BitVec.lsb, spOf,
      Arm.read_gpr] <;> bv_omega
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
    have hlen' : 16 * ps.length < 2 ^ 64 := by simp only [List.length_cons] at hlen; omega
    have hB16 : (B + 16#64).toNat % 16 = 0 := aligned_add hB 1
    have hsp' : spOf s = (B + 16#64) + BitVec.ofNat 64 (16 * ps.length) := by
      rw [hsp]; simp only [List.length_cons]; bv_omega
    have hps' : ∀ q ∈ ps, PushReg int q.1 ∧ PushReg int q.2 :=
      fun q hq => hps q (List.mem_cons_of_mem _ hq)
    obtain ⟨s1, h1, hsp1, -, -, -, -, -⟩ := pushPairs_ok env int ps s (B + 16#64) hps' hlen' hB16 hsp'
    have hmap : (p :: ps).reverse.map (pushLine2 int) =
        ps.reverse.map (pushLine2 int) ++ [pushLine2 int p] := by simp
    rw [hmap]
    refine linesWrites_app (pushPairs_writes env int ps s (B + 16#64) hps' hlen' hB16 hsp'
      (fun k hk => ?_)) (fun s1' hs1' => ?_)
    · have h := hP (16 + k) (by simp only [List.length_cons]; omega)
      rwa [← add_ofNat_add] at h
    · rw [execLines_steps h1 hs1']
      simp only [pushLine2]
      refine linesWrites_cons (fun _ _ h => by simp at h) fun env' a' ha' q hq k hk => ?_
      rw [memWrites_push2 (hps p (by simp)).1 (hps p (by simp)).2 ha' s1] at hq
      simp only [List.mem_singleton] at hq
      subst hq
      simp only at hk ⊢
      rw [hsp1, BitVec.add_sub_cancel]
      exact hP k (by simp only [List.length_cons]; omega)

/-- The pushes of one register class write only `[B, B + pushBytes)`. -/
theorem pushLines_writes (env : Env) (int : Bool) (rs : List Reg) (s : Arm.ArmState) (B : BitVec 64)
    (hrs : ∀ r ∈ rs, PushReg int r) (hlen : rs.length ≤ 64) (hB : B.toNat % 16 = 0)
    (hsp : spOf s = B + BitVec.ofNat 64 (pushBytes rs.length)) {P : BitVec 64 → Prop}
    (hP : ∀ k < pushBytes rs.length, P (B + BitVec.ofNat 64 k)) :
    LinesWrites env (pushLines int rs) s P := by
  have hpb := pushBytes_eq rs
  have hpbI : pushBytes rs.length ≤ 1040 := by unfold pushBytes; omega
  obtain ⟨hmP, hmO⟩ := pairsOf_mem rs
  have hpv : ∀ p ∈ (pairsOf rs).1, PushReg int p.1 ∧ PushReg int p.2 :=
    fun p hp => ⟨hrs _ (hmP p hp).1, hrs _ (hmP p hp).2⟩
  have hPl : 16 * (pairsOf rs).1.length < 2 ^ 64 := by omega
  rw [pushLines_eq]
  rcases ho : (pairsOf rs).2 with _ | r0
  · simp only [ho, Option.isSome_none, Bool.false_eq_true, ite_false, Nat.add_zero] at hpb
    show LinesWrites env ([] ++ _) s P
    rw [List.nil_append]
    exact pushPairs_writes env int _ s B hpv hPl hB (by rw [hsp, hpb])
      (fun k hk => hP k (by omega))
  · simp only [ho, Option.isSome_some, ite_true] at hpb
    have hspE : spOf s = B + BitVec.ofNat 64 (16 * (pairsOf rs).1.length) + 16#64 := by
      rw [hsp, hpb, ← add_ofNat_add]
    have hal0 : (spOf s).toNat % 16 = 0 := by
      rw [hspE]; exact aligned_add (aligned_add hB _) 1
    have hr0 := hrs _ (hmO r0 ho)
    obtain ⟨a, ha, he⟩ := exec_push1 env hr0 s (checkSP_of hal0)
    obtain ⟨hpc1, -, -, hsp1, -⟩ := pushSt_facts s 8 (slotVal s r0)
    rw [← he] at hpc1 hsp1
    have hrun := execLines_one (t := none) ha hpc1
    show LinesWrites env ([_] ++ _) s P
    refine linesWrites_app (linesWrites_cons (fun _ _ h => by simp at h)
      fun env' a' ha' q hq k hk => ?_) fun s1 hs1 => ?_
    · rw [memWrites_push1 hr0 ha' s] at hq
      simp only [List.mem_singleton] at hq
      subst hq
      simp only at hk ⊢
      rw [hspE, BitVec.add_sub_cancel, add_ofNat_add]
      exact hP _ (by omega)
    · rw [hrun, Option.some.injEq] at hs1
      rw [← hs1]
      exact pushPairs_writes _ int _ _ B hpv hPl hB (by rw [hsp1, hspE, BitVec.add_sub_cancel])
        (fun k hk => hP k (by omega))

/-- The `sp` adjustment stores nothing. -/
theorem spAdjLines_noStores (sub : Bool) (size : Nat) :
    ∀ x t, Line.ins x t ∈ spAdjLines sub size → x.stores = false := by
  intro x t h
  unfold spAdjLines at h
  split at h
  · cases h
  · split at h
    · simp only [List.mem_singleton, Line.ins.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      cases sub <;> rfl
    · rcases List.mem_append.1 h with h | h
      · exact loadConst64_noStores _ _ x t h
      · simp only [List.mem_singleton, Line.ins.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        cases sub <;> rfl

/-- **The prologue writes only the frame top** `[sp - 16 - clobberBytes, sp)`: fp/lr at
`sp - 16`, the int pushes below it, the float pushes at the bottom; `mov x29, sp` and the `sp`
adjustment store nothing. -/
theorem prologue_writes (env : Env) {saves : List Reg} {size : Nat}
    (hsv : SavesOk saves) (s : Arm.ArmState)
    (hal : (spOf s).toNat % 16 = 0) {P : BitVec 64 → Prop}
    (hP : ∀ k < 16 + clobberBytes saves,
      P (spOf s - BitVec.ofNat 64 (16 + clobberBytes saves) + BitVec.ofNat 64 k)) :
    LinesWrites env (prologueLines saves size) s P := by
  have hcbl := hsv.clobber_le
  have hcbe : clobberBytes saves = pushBytes (savesInt saves).length +
      pushBytes (savesFloat saves).length := rfl
  have hpIm := pushBytes_mod (savesInt saves).length
  have hpFm := pushBytes_mod (savesFloat saves).length
  generalize hBF : spOf s - BitVec.ofNat 64 (16 + clobberBytes saves) = BF at hP
  have hS : spOf s = BF + BitVec.ofNat 64 (16 + clobberBytes saves) := by
    rw [← hBF]; exact (BitVec.sub_add_cancel _ _).symm
  have hBFa : BF.toNat % 16 = 0 := by rw [← hBF]; exact aligned_sub hal (by omega) (by omega)
  have hBIa : (BF + BitVec.ofNat 64 (pushBytes (savesFloat saves).length)).toNat % 16 = 0 := by
    rw [show pushBytes (savesFloat saves).length = 16 * (pushBytes (savesFloat saves).length / 16)
      by omega]
    exact aligned_add hBFa _
  have hT16 : spOf s - 16#64 = BF + BitVec.ofNat 64 (pushBytes (savesFloat saves).length) +
      BitVec.ofNat 64 (pushBytes (savesInt saves).length) := by
    rw [hS, show 16 + clobberBytes saves = pushBytes (savesFloat saves).length +
      pushBytes (savesInt saves).length + 16 by omega, ← add_ofNat_add, ← add_ofNat_add,
      BitVec.add_sub_cancel]
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
  rw [prologueLines_eq]
  refine linesWrites_app
    (linesWrites_cons (fun y t' h => by
        simp only [List.mem_singleton, Line.ins.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rfl)
      fun env' a' ha' q hq k hk => ?_) fun s2 hs2 => ?_
  · rw [memWrites_stp_pre ha' s] at hq
    simp only [List.mem_singleton] at hq
    subst hq
    simp only at hk ⊢
    rw [hT16, add_ofNat_add, add_ofNat_add]
    exact hP _ (by omega)
  · -- the int pushes
    rw [hrun2, Option.some.injEq] at hs2
    subst hs2
    obtain ⟨s3, h3, hsp3, -⟩ := pushLines_ok { env with pc := env.pc + 8 } true (savesInt saves)
      (Arm.exec_inst a2 (Arm.exec_inst a1 s)) (BF + BitVec.ofNat 64 (pushBytes (savesFloat saves).length))
      hsv.int (by have := hsv.intLen; omega) hBIa (by rw [hsp2, hT16])
    refine linesWrites_app (pushLines_writes { env with pc := env.pc + 8 } true (savesInt saves) _
      (BF + BitVec.ofNat 64 (pushBytes (savesFloat saves).length)) hsv.int
      (by have := hsv.intLen; omega) hBIa (by rw [hsp2, hT16]) (fun k hk => ?_)) fun s3' hs3 => ?_
    · rw [add_ofNat_add]
      exact hP _ (by omega)
    · -- the float pushes, then the `sp` adjustment
      rw [execLines_steps h3 hs3]
      exact linesWrites_app (pushLines_writes _ false (savesFloat saves) s3 BF hsv.float
        (by have := hsv.floatLen; omega) hBFa hsp3 (fun k hk => hP k (by omega)))
        fun _ _ => linesWrites_noStores (spAdjLines_noStores _ _)

end Backend.Proof
