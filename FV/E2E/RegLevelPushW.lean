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

/-- A stack probe's `stur wzr, [sp]` writes 4 bytes at `sp` (#581). -/
theorem memWrites_stur {env : Env} {a : Arm.ArmInst}
    (h : (Insn.store .store32 .xzr (.unscaled .sp 0)).toArmInst env = .ok a) (s : Arm.ArmState) :
    MemWrites a s = [(spOf s, 4)] := by
  have e : (Insn.store .store32 .xzr (.unscaled .sp 0)).toArmInst env = .ok
      (.LDST (.Reg_unscaled_imm
        { size := 2#2, VR := 0#1, opc := 0#2, imm9 := 0#9, Rn := 31#5, Rt := 31#5 })) := by
    simp [csimp_rules, pure, Except.pure]; rfl
  rw [e, Except.ok.injEq] at h
  subst h
  simp (config := {decide := true}) [MemWrites, RegImm.writes, RegImm.ofUnscaled, RegImm.memop,
    RegImm.addr, RegImm.scale, Arm.LDST.Reg_offset.value, Arm.BitVec.lsb, spOf, Arm.read_gpr]

/-- `k` unrolled probes write only the probed bytes (`probeHitB`). -/
theorem probeSteps_writes (env : Env) {P : BitVec 64 → Prop} : ∀ (k : Nat) (s : Arm.ArmState),
    (spOf s).toNat % 16 = 0 → (∀ a, probeHitB k (spOf s) a = true → P a) →
    LinesWrites env (probeSteps k) s P
  | 0, _, _, _ => fun k _ _ hk => by simp [probeSteps] at hk
  | k + 1, s, hal, hP => by
    obtain ⟨a1, ha1, he1⟩ := exec_sub_sp_imm env ⟨1, true⟩ (by decide) s
    have hpc1 : Arm.r .PC (Arm.exec_inst a1 s) = Arm.r .PC s + 4#64 := by
      rw [he1]; simp [Arm.r_of_w_same, Arm.r_of_w_different]
    have hsp1 : spOf (Arm.exec_inst a1 s) = spOf s - 4096#64 := by
      rw [he1]; simp [spOf, Arm.r_of_w_same, Arm.r_of_w_different, Imm12.value]
    have hrun1 : execLines env [Line.ins (.aluImm12 .sub true .sp .sp ⟨1, true⟩) none] s =
        some (Arm.exec_inst a1 s) := execLines_one ha1 hpc1
    have hal1 : (spOf (Arm.exec_inst a1 s)).toNat % 16 = 0 := by
      rw [hsp1]; exact aligned_sub hal (n := 4096) (by decide) (by decide)
    obtain ⟨a2, ha2, he2⟩ := exec_stur_wzr_sp { env with pc := env.pc + 4 } (Arm.exec_inst a1 s)
      (checkSP_of hal1)
    have hpc2 : Arm.r .PC (Arm.exec_inst a2 (Arm.exec_inst a1 s)) =
        Arm.r .PC (Arm.exec_inst a1 s) + 4#64 := by
      rw [he2]; simp [Arm.r_of_w_same, Arm.r_of_w_different, Arm.r_of_write_mem_bytes]
    have hsp2 : spOf (Arm.exec_inst a2 (Arm.exec_inst a1 s)) = spOf s - 4096#64 := by
      rw [he2, ← hsp1]; simp [spOf, Arm.r_of_w_different, Arm.r_of_write_mem_bytes]
    have hrun2 : execLines env [Line.ins (.aluImm12 .sub true .sp .sp ⟨1, true⟩) none,
        Line.ins (.store .store32 .xzr (.unscaled .sp 0)) none] s =
        some (Arm.exec_inst a2 (Arm.exec_inst a1 s)) := by
      rw [execLines_cons_of hrun1 [Line.ins (.store .store32 .xzr (.unscaled .sp 0)) none]]
      exact execLines_one ha2 hpc2
    show LinesWrites env ([Line.ins (.aluImm12 .sub true .sp .sp ⟨1, true⟩) none] ++
      [Line.ins (.store .store32 .xzr (.unscaled .sp 0)) none] ++ probeSteps k) s P
    refine linesWrites_app (linesWrites_append_last (fun y t h => by
        simp only [List.mem_singleton, Line.ins.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rfl) fun s1 hs1 env' a ha p hp i hi => ?_) fun s2 hs2 => ?_
    · rw [hrun1, Option.some.injEq] at hs1
      subst hs1
      rw [memWrites_stur ha, hsp1] at hp
      simp only [List.mem_singleton] at hp
      subst hp
      apply hP
      rw [probeHitB_succ]
      simp only at hi ⊢
      have e : (spOf s - 4096#64 + BitVec.ofNat 64 i - (spOf s - 4096#64)).toNat = i := by
        rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat]
        exact Nat.mod_eq_of_lt (by omega)
      simp [e, hi]
    · have hs2' : execLines env [Line.ins (.aluImm12 .sub true .sp .sp ⟨1, true⟩) none,
          Line.ins (.store .store32 .xzr (.unscaled .sp 0)) none] s = some s2 := hs2
      rw [hrun2, Option.some.injEq] at hs2'
      subst hs2'
      exact probeSteps_writes { env with pc := env.pc + 4 * 2 } k _
        (by rw [hsp2, ← hsp1]; exact hal1)
        (fun a h => hP a (by rw [probeHitB_succ, ← hsp2, h, Bool.or_true]))

/-- The stack probes write only the probed bytes (#581). -/
theorem probeLines_writes (env : Env) (total : Nat) (s : Arm.ArmState)
    (hal : (spOf s).toNat % 16 = 0) {P : BitVec 64 → Prop}
    (hP : ∀ a, probeHitB (probeCount total) (spOf s) a = true → P a) :
    LinesWrites env (probeLines total) s P := by
  unfold probeLines
  simp only
  split
  · exact fun k _ _ hk => by simp at hk
  · exact linesWrites_app (probeSteps_writes env _ s hal hP) fun _ _ =>
      linesWrites_noStores fun x t h => by
        simp only [List.mem_singleton, Line.ins.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rfl

/-- The stack-probe loop's `str wzr, [sp, x16]` writes 4 bytes at `sp + x16` (#581). -/
theorem memWrites_str_sp_x16 {env : Env} {a : Arm.ArmInst}
    (h : (Insn.store .store32 .xzr (.regReg .sp (.x 16))).toArmInst env = .ok a) (s : Arm.ArmState) :
    MemWrites a s = [(spOf s + xreg 16 s, 4)] := by
  rw [memWrites_store (default : FnCtx) (by simp [FinalAM, BaseOk, IdxOk]) (fun e => by cases e) h s]
  rfl

/-- An iteration's straight-line part (`sub`, `str`, `cmn`) of the stack-probe loop from
`sp = S`, `x16 = -4096·m` writes only the 4 bytes at `S - 4096·(m + 1)` (#581). -/
theorem loopBody_writes (env : Env) {P : BitVec 64 → Prop} {S : BitVec 64} {m : Nat}
    (s : Arm.ArmState) (hsp : spOf s = S) (h16 : xreg 16 s = loopOff m)
    (hP : ∀ b < 4, P (S - BitVec.ofNat 64 (4096 * (m + 1)) + BitVec.ofNat 64 b)) :
    LinesWrites env (probeLoopBody.take 3) s P := by
  obtain ⟨a1, ha1, he1⟩ := exec_sub_x16_4096 env s
  have hpc1 : Arm.r .PC (Arm.exec_inst a1 s) = Arm.r .PC s + 4#64 := by
    rw [he1]; simp [Arm.r_of_w_same, Arm.r_of_w_different]
  have hrun1 : execLines env [Line.ins (.aluImm12 .sub true (.x 16) (.x 16) ⟨1, true⟩) none] s =
      some (Arm.exec_inst a1 s) := execLines_one ha1 hpc1
  have hsp1 : spOf (Arm.exec_inst a1 s) = S := by
    rw [he1, ← hsp]; simp [spOf, Arm.r_of_w_different]
  have h161 : xreg 16 (Arm.exec_inst a1 s) = loopOff (m + 1) := by
    rw [he1]; simp only [xreg, Arm.r_of_w_same]
    simp only [xreg] at h16; rw [h16]
    rw [show 4096 * (m + 1) = 4096 * m + 4096 by omega, BitVec.ofNat_add]; bv_omega
  show LinesWrites env ([Line.ins (.aluImm12 .sub true (.x 16) (.x 16) ⟨1, true⟩) none] ++
    [Line.ins (.store .store32 .xzr (.regReg .sp (.x 16))) none] ++
    [Line.ins (.aluRRR .addS true .xzr (.x 16) (.x 17)) none]) s P
  refine linesWrites_app (linesWrites_append_last (fun y t h => by
      simp only [List.mem_singleton, Line.ins.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl) fun s1 hs1 env' a ha p hp i hi => ?_) fun _ _ => linesWrites_noStores fun x t h => by
        simp only [List.mem_singleton, Line.ins.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rfl
  rw [hrun1, Option.some.injEq] at hs1
  subst hs1
  rw [memWrites_str_sp_x16 ha, hsp1, h161] at hp
  simp only [List.mem_singleton] at hp
  subst hp
  simp only at hi ⊢
  rw [show S + loopOff (m + 1) = S - BitVec.ofNat 64 (4096 * (m + 1)) by simp only [loopOff]; bv_omega]
  exact hP i hi

/-- **The prologue's lines after the stack probes** (`prologueTail`: the pushes and the `sp`
adjustment), from `sp = BF + clobberBytes`, write only the clobber area `[BF, BF + clobberBytes)`:
the int pushes at its top, the float pushes at its bottom. -/
theorem prologueTail_writes (env : Env) {saves : List Reg} (size : Nat) (hsv : SavesOk saves)
    (BF : BitVec 64) (hBFa : BF.toNat % 16 = 0) (sP : Arm.ArmState)
    (hspP : spOf sP = BF + BitVec.ofNat 64 (pushBytes (savesFloat saves).length) +
      BitVec.ofNat 64 (pushBytes (savesInt saves).length)) {P : BitVec 64 → Prop}
    (hP : ∀ k < clobberBytes saves, P (BF + BitVec.ofNat 64 k)) :
    LinesWrites env (prologueTail saves size) sP P := by
  have hcbl := hsv.clobber_le
  have hcbe : clobberBytes saves = pushBytes (savesInt saves).length +
      pushBytes (savesFloat saves).length := rfl
  have hpFm := pushBytes_mod (savesFloat saves).length
  have hBIa : (BF + BitVec.ofNat 64 (pushBytes (savesFloat saves).length)).toNat % 16 = 0 := by
    rw [show pushBytes (savesFloat saves).length = 16 * (pushBytes (savesFloat saves).length / 16)
      by omega]
    exact aligned_add hBFa _
  -- the int pushes
  obtain ⟨s3, h3, hsp3, -⟩ := pushLines_ok env true (savesInt saves) sP
    (BF + BitVec.ofNat 64 (pushBytes (savesFloat saves).length))
    hsv.int (by have := hsv.intLen; omega) hBIa hspP
  refine linesWrites_app (pushLines_writes env true (savesInt saves) _
    (BF + BitVec.ofNat 64 (pushBytes (savesFloat saves).length)) hsv.int
    (by have := hsv.intLen; omega) hBIa hspP (fun k hk => ?_)) fun s3' hs3 => ?_
  · rw [add_ofNat_add]
    exact hP _ (by omega)
  · -- the float pushes, then the `sp` adjustment
    rw [execLines_steps h3 hs3]
    exact linesWrites_app (pushLines_writes _ false (savesFloat saves) s3 BF hsv.float
      (by have := hsv.floatLen; omega) hBFa hsp3 (fun k hk => hP k (by omega)))
      fun _ _ => linesWrites_noStores (spAdjLines_noStores _ _)

/-- `prologueTail_writes` for an entry `sp` `X`: from `sp = X - 16` (after fp/lr), the tail writes
only `[X - 16 - clobberBytes, X - 16)`. -/
theorem prologueTail_writesX (env : Env) {saves : List Reg} (size : Nat) (hsv : SavesOk saves)
    (X : BitVec 64) (hal : X.toNat % 16 = 0) (sP : Arm.ArmState) (hspP : spOf sP = X - 16#64)
    {P : BitVec 64 → Prop}
    (hP : ∀ k < 16 + clobberBytes saves,
      P (X - BitVec.ofNat 64 (16 + clobberBytes saves) + BitVec.ofNat 64 k)) :
    LinesWrites env (prologueTail saves size) sP P := by
  have hcbl := hsv.clobber_le
  have hcbe : clobberBytes saves = pushBytes (savesInt saves).length +
      pushBytes (savesFloat saves).length := rfl
  generalize hBF : X - BitVec.ofNat 64 (16 + clobberBytes saves) = BF at hP
  have hS : X = BF + BitVec.ofNat 64 (16 + clobberBytes saves) := by
    rw [← hBF]; exact (BitVec.sub_add_cancel _ _).symm
  have hBFa : BF.toNat % 16 = 0 := by rw [← hBF]; exact aligned_sub hal (by omega) (by omega)
  have hT16 : X - 16#64 = BF + BitVec.ofNat 64 (pushBytes (savesFloat saves).length) +
      BitVec.ofNat 64 (pushBytes (savesInt saves).length) := by
    rw [hS, show 16 + clobberBytes saves = pushBytes (savesFloat saves).length +
      pushBytes (savesInt saves).length + 16 by omega, ← add_ofNat_add, ← add_ofNat_add,
      BitVec.add_sub_cancel]
  exact prologueTail_writes env size hsv BF hBFa sP (by rw [hspP, hT16]) fun k hk => hP k (by omega)

/-- **The stack-probe loop and the lines after it, run straight-line** from the loop's start
(`LoopRuns` from iteration 0 at `sp = S`, at least two iterations): only the first iteration's
`str` writes (4 bytes at `S - 4096`); its `b.gt` jumps back, so no later line is reached (#581). -/
theorem loopRest_writes (env : Env) {S : BitVec 64} {r : Nat} (hr : 2 ≤ r) {T : List Line}
    (s : Arm.ArmState) {s' : Arm.ArmState} (hL : LoopRuns env S 0 r s s') {P : BitVec 64 → Prop}
    (hP : ∀ b < 4, P (S - 4096#64 + BitVec.ofNat 64 b)) :
    LinesWrites env (probeLoopBody ++ T) s P := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  obtain ⟨hsp, h16, s3, ab, h3, hab, -, -, hpcB, -⟩ := hL
  rw [if_neg (by omega)] at hpcB
  have hl3 : (probeLoopBody.take 3).length = 3 := rfl
  rw [show probeLoopBody ++ T = probeLoopBody.take 3 ++ (.ins (.bcondRel .gt (-12)) none :: T) from rfl]
  refine linesWrites_app (loopBody_writes env s hsp h16 fun b hb => ?_) fun s3' hs3 => ?_
  · simpa using hP b hb
  · rw [execLines_steps h3 hs3]
    intro k x t hk s1 hs1 env' a ha p hp i hi
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Line.ins.injEq] at hk
      obtain ⟨rfl, -⟩ := hk
      rw [Insn.memWrites_nil rfl ha] at hp
      cases hp
    | succ k =>
      -- the `b.gt` jumps back: the straight-line run stops there
      change execLines { env with pc := env.pc + 12 }
        (List.take (k + 1) (.ins (.bcondRel .gt (-12)) none :: T)) s3 = some s1 at hs1
      rw [List.take_succ_cons] at hs1
      simp only [execLines, hab] at hs1
      split at hs1
      · rename_i hpc
        rw [hpcB, h3.pc, hl3] at hpc
        have e : BitVec.ofNat 64 (4 * 3) = 12#64 := rfl
        rw [e] at hpc
        bv_omega
      · cases hs1

/-- **The prologue writes only the frame top** `[sp - 16 - clobberBytes, sp)` **and the probed
bytes**: fp/lr at `sp - 16`, the stack probes (`probeHitN`, #581), the int pushes below fp/lr,
the float pushes at the bottom; `mov x29, sp` and the `sp` adjustment store nothing. -/
theorem prologue_writes (env : Env) {saves : List Reg} {size : Nat} {calls : Bool}
    (hsv : SavesOk saves) (s : Arm.ArmState)
    (hal : (spOf s).toNat % 16 = 0) {P : BitVec 64 → Prop}
    (hP : ∀ k < 16 + clobberBytes saves,
      P (spOf s - BitVec.ofNat 64 (16 + clobberBytes saves) + BitVec.ofNat 64 k))
    (hPp : ∀ a, probeHitN (probeCount (probeTotal size calls)) (spOf s) a = true → P a) :
    LinesWrites env (prologueLines saves size calls) s P := by
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
  have hal2 : (spOf (Arm.exec_inst a2 (Arm.exec_inst a1 s))).toNat % 16 = 0 := by
    rw [hsp2]; exact aligned_sub hal (by decide) (by decide)
  rw [prologueLines_eq]
  refine linesWrites_app
    (linesWrites_cons (fun y t h => by
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
  · -- the stack probes
    rw [hrun2, Option.some.injEq] at hs2
    subst hs2
    by_cases hl : probeLoop (probeTotal size calls) = true
    · -- the loop form: straight-line, only its first iteration's `str` is reached
      have hH : probeHead (probeTotal size calls) =
          loadConst64 (.x 16) 0 ++ loadConst64 (.x 17) (probeTotal size calls) := by
        simp [probeHead, hl]
      have hLL : probeLoopL (probeTotal size calls) = probeLoopBody := by simp [probeLoopL, hl]
      have hI : loopIters (probeTotal size calls) = probeCount (probeTotal size calls) := by
        simp [loopIters, hl]
      have hn4 : 3 < probeCount (probeTotal size calls) := by simpa [probeLoop] using hl
      obtain ⟨sP, ⟨s1, hH1, -, hL, -⟩, -⟩ := probeRun_ok { env with pc := env.pc + 8 }
        (probeTotal size calls) _ hal2
      rw [hI] at hL
      rw [probeLines_split, hLL, List.append_assoc]
      refine linesWrites_app (linesWrites_noStores fun x t h => ?_) fun s1' hs1 => ?_
      · rw [hH] at h
        rcases List.mem_append.1 h with h | h <;> exact loadConst64_noStores _ _ x t h
      · rw [execLines_steps hH1 hs1]
        refine loopRest_writes _ (by omega) _ hL fun b hb => hPp _ ?_
        simp only [probeHitN, probeHitB, List.any_eq_true, List.mem_range]
        refine ⟨0, by omega, ?_⟩
        rw [hsp2, show spOf s - 16#64 - 4096#64 + BitVec.ofNat 64 b -
          (spOf s - 16#64 - BitVec.ofNat 64 (4096 * (0 + 1))) = BitVec.ofNat 64 b by bv_omega]
        simp only [BitVec.toNat_ofNat, decide_eq_true_eq]
        omega
    · -- the unrolled form
      have hl' : probeLoop (probeTotal size calls) = false := by simpa using hl
      have h3 : probeCount (probeTotal size calls) ≤ 3 := by simpa [probeLoop] using hl'
      obtain ⟨sP, hPs, hspP, -⟩ := probeLines_ok { env with pc := env.pc + 8 } (probeTotal size calls) h3
        (Arm.exec_inst a2 (Arm.exec_inst a1 s)) hal2
      refine linesWrites_app (probeLines_writes { env with pc := env.pc + 8 } (probeTotal size calls) _ hal2
        (fun a h => hPp a (by rw [← probeHitB_sub16, ← hsp2]; exact h))) fun sP' hsP => ?_
      rw [execLines_steps hPs hsP]
      exact prologueTail_writes _ size hsv BF hBFa sP (by rw [hspP, hsp2, hT16])
        (fun k hk => hP k (by omega))

end Backend.Proof
