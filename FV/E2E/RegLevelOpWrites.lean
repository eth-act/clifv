import FV.Backend.Proof.RegallocCover
import FV.E2E.ExecWrites

/-!
# The memory writes of the covered straight-line forms (A3, #412, slice F8b)

`formOk_writes` (as `formOk_reads`, `FV/E2E/RegLevelOpReads.lean`): the lines of an allocated
covered form (`FormOk`), run from a state `s` whose world `w` gives `csem` a result, write only
bytes outside the frame addresses `F`. The forms other than the stores write nothing
(`lines_noStores`); a store writes `op.bytes` bytes at its address (`mstore_writes`), which is the
canonical instance's address (`AccW`, per addressing mode), and `csem` (`straightSem`) is defined
only when that access avoids `F` (`AccessOk`); `stlr` likewise, and the `s`/`d` stores `fpuStore`
(`memWrites_fpuStore`, `fstore_writes`, `accW_fpuStore*`).
-/

set_option linter.unusedSimpArgs false

namespace Backend.Proof

open Backend E2E

/-- **The writes obligation of a form**: the allocated instruction's lines, run from `s`, write
only outside `F`, when the canonical instance's accesses on the canonical state avoid `F`. -/
def AccW (F : BitVec 64 → Prop) (ctx : FnCtx) (ops : Array Operand) (mk : Array Reg → MInst) :
    Prop :=
  ∀ (regs : Array Reg) (s w : Arm.ArmState), AllocOk ops regs → SameWorld F s w →
    AccessOk F ctx (mk (canonRegs ops)) (placeUses ops (canonRegs ops) (useVals ops regs s) w) →
    ∀ ls ps ps', (mk regs).lines ctx ps = .ok (ls, ps') → ∀ env,
      LinesWrites env ls s (fun a => ¬ F a)

/-- `AccW` gives the writes of the allocated instruction from `csem`'s result. -/
theorem writes_of_accW {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {i : MInst}
    {ops : Array Operand} (hops : i.operands = .ok ops) (mk : Array Reg → MInst)
    (hmk : ∀ regs : Array Reg, regs.size = ops.size → i.assign regs = .ok (mk regs))
    (hfo : FormOk ctx i = true) (hctl : i.isCtl = false) (hc : AccW F ctx ops mk)
    {ops' : Array Operand} (hops' : i.operands = .ok ops') {regs : Array Reg} {i' : MInst}
    {s w : Arm.ArmState} {r : List CV × Arm.ArmState × Ctl} {ls : List Line} {ps ps' : PState}
    (ha : AllocOk ops' regs) (hasg : i.assign regs = .ok i') (hl : i'.lines ctx ps = .ok (ls, ps'))
    (hw : SameWorld F s w) (he : Arm.r .ERR w = .None) (hal : Arm.CheckSPAlignment w)
    (hsem : csem F ctx X i (useVals ops' regs s) w = some r) (env : Env) :
    LinesWrites env ls s (fun a => ¬ F a) := by
  rw [hops] at hops'
  cases hops'
  rw [hmk regs ha.size] at hasg
  cases hasg
  rw [csem_of_wf hctl (by simp [csemWF, hfo, hops, useVals_length ops regs ha.size]) he hal] at hsem
  simp only [straightSem, hops, hmk _ (canonRegs_size ops)] at hsem
  split at hsem
  · exact hc regs s w ha hw ‹_› ls ps ps' hl env
  · cases hsem

/-! ## `AccW` of the stores -/

section
variable (F : BitVec 64 → Prop) (ctx : FnCtx)

theorem accW_store0g (op : StoreOp) (hop : op ≠ .fpuStore128) (d : Nat) (am : AMode)
    (fl : Clif.MemFlags) (hmm : MemMode op.bytes am)
    (hA : ∀ (s w : Arm.ArmState) (v : BitVec 64), SameWorld F s w →
      am.addr ctx op.bytes (Arm.w (.GPR 0#5) v w) = am.addr ctx op.bytes s) :
    AccW F ctx #[⟨d, .int, .use, .early, .reg⟩] (fun r => .store op (r.getD 0 .xzr) am fl) := by
  intro regs s w ha hw hacc ls ps ps' hl env
  have hsz := ha.size
  simp only [List.size_toArray, List.length_cons, List.length_nil] at hsz
  have hf := ha.fits
  obtain ⟨r0, rfl⟩ := regs1 hsz
  simp [RegFits] at hf
  rcases hf with ⟨n0, rfl, hn0⟩
  have hcanon : canonRegs #[⟨d, .int, .use, .early, .reg⟩] = #[.x 0] := by
    simp [canonRegs, canonReg, canonBase, List.range_succ]
  have ht : placeUses #[⟨d, .int, .use, .early, .reg⟩] (canonRegs #[⟨d, .int, .use, .early, .reg⟩])
      (useVals #[⟨d, .int, .use, .early, .reg⟩] #[.x n0] s) w =
      Arm.w (.GPR 0#5) (Arm.r (.GPR (rnum n0)) s) w := by
    simp [placeUses, useVals, hcanon, Operand.isUse, lo64, regVal, rnum]
  rw [ht, hcanon] at hacc
  have hav : Avoids F op.bytes (am.addr ctx op.bytes (Arm.w (.GPR 0#5) (Arm.r (.GPR (rnum n0)) s) w)) :=
    hacc _ (List.mem_singleton_self _)
  rw [hA s w _ hw] at hav
  refine (mstore_writes ctx hmm (fun e => absurd e hop) hl env s).mono ?_
  rintro a ⟨k, hk, rfl⟩
  exact hav k hk

theorem accW_store1 (op : StoreOp) (hop : op ≠ .fpuStore128) (d n : Nat) (fl : Clif.MemFlags)
    (A : Reg → AMode) (g : BitVec 64 → BitVec 64)
    (hA : ∀ a : Nat, a < 29 → MemMode op.bytes (A (.x a)))
    (hg : ∀ (a : Nat) s, (A (.x a)).addr ctx op.bytes s = g (Arm.r (.GPR (rnum a)) s)) :
    AccW F ctx #[⟨d, .int, .use, .early, .reg⟩, ⟨n, .int, .use, .early, .reg⟩]
      (fun r => .store op (r.getD 0 .xzr) (A (r.getD 1 .xzr)) fl) := by
  intro regs s w ha hw hacc ls ps ps' hl env
  have hsz := ha.size
  simp only [List.size_toArray, List.length_cons, List.length_nil] at hsz
  have hf := ha.fits
  obtain ⟨r0, r1, rfl⟩ := regs2 hsz
  simp [RegFits] at hf
  rcases hf with ⟨⟨n0, rfl, hn0⟩, ⟨n1, rfl, hn1⟩⟩
  have hcanon : canonRegs #[⟨d, .int, .use, .early, .reg⟩, ⟨n, .int, .use, .early, .reg⟩] =
      #[.x 0, .x 1] := by
    simp [canonRegs, canonReg, canonBase, List.range_succ]
  have ht : placeUses #[⟨d, .int, .use, .early, .reg⟩, ⟨n, .int, .use, .early, .reg⟩]
      (canonRegs #[⟨d, .int, .use, .early, .reg⟩, ⟨n, .int, .use, .early, .reg⟩])
      (useVals #[⟨d, .int, .use, .early, .reg⟩, ⟨n, .int, .use, .early, .reg⟩] #[.x n0, .x n1] s) w =
      Arm.w (.GPR 1#5) (Arm.r (.GPR (rnum n1)) s) (Arm.w (.GPR 0#5) (Arm.r (.GPR (rnum n0)) s) w) := by
    simp [placeUses, useVals, hcanon, Operand.isUse, lo64, regVal, rnum]
  rw [ht, hcanon] at hacc
  have hav : Avoids F op.bytes ((A (.x 1)).addr ctx op.bytes
      (Arm.w (.GPR 1#5) (Arm.r (.GPR (rnum n1)) s) (Arm.w (.GPR 0#5) (Arm.r (.GPR (rnum n0)) s) w))) :=
    hacc _ (List.mem_singleton_self _)
  rw [hg, show rnum 1 = 1#5 from rfl, Arm.r_of_w_same, ← hg] at hav
  refine (mstore_writes ctx (hA n1 hn1.1) (fun e => absurd e hop) hl env s).mono ?_
  rintro a ⟨k, hk, rfl⟩
  exact hav k hk

theorem accW_store2 (op : StoreOp) (hop : op ≠ .fpuStore128) (d n m : Nat) (fl : Clif.MemFlags)
    (A : Reg → Reg → AMode) (g : BitVec 64 → BitVec 64 → BitVec 64)
    (hA : ∀ a b : Nat, a < 29 → b < 29 → MemMode op.bytes (A (.x a) (.x b)))
    (hg : ∀ (a b : Nat) s, (A (.x a) (.x b)).addr ctx op.bytes s =
      g (Arm.r (.GPR (rnum a)) s) (Arm.r (.GPR (rnum b)) s)) :
    AccW F ctx #[⟨d, .int, .use, .early, .reg⟩, ⟨n, .int, .use, .early, .reg⟩,
      ⟨m, .int, .use, .early, .reg⟩]
      (fun r => .store op (r.getD 0 .xzr) (A (r.getD 1 .xzr) (r.getD 2 .xzr)) fl) := by
  intro regs s w ha hw hacc ls ps ps' hl env
  have hsz := ha.size
  simp only [List.size_toArray, List.length_cons, List.length_nil] at hsz
  have hf := ha.fits
  obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz
  simp [RegFits] at hf
  rcases hf with ⟨⟨n0, rfl, hn0⟩, ⟨n1, rfl, hn1⟩, ⟨n2, rfl, hn2⟩⟩
  have hcanon : canonRegs #[⟨d, .int, .use, .early, .reg⟩, ⟨n, .int, .use, .early, .reg⟩,
      ⟨m, .int, .use, .early, .reg⟩] = #[.x 0, .x 1, .x 2] := by
    simp [canonRegs, canonReg, canonBase, List.range_succ]
  have ht : placeUses #[⟨d, .int, .use, .early, .reg⟩, ⟨n, .int, .use, .early, .reg⟩,
      ⟨m, .int, .use, .early, .reg⟩]
      (canonRegs #[⟨d, .int, .use, .early, .reg⟩, ⟨n, .int, .use, .early, .reg⟩,
        ⟨m, .int, .use, .early, .reg⟩])
      (useVals #[⟨d, .int, .use, .early, .reg⟩, ⟨n, .int, .use, .early, .reg⟩,
        ⟨m, .int, .use, .early, .reg⟩] #[.x n0, .x n1, .x n2] s) w =
      Arm.w (.GPR 2#5) (Arm.r (.GPR (rnum n2)) s) (Arm.w (.GPR 1#5) (Arm.r (.GPR (rnum n1)) s)
        (Arm.w (.GPR 0#5) (Arm.r (.GPR (rnum n0)) s) w)) := by
    simp [placeUses, useVals, hcanon, Operand.isUse, lo64, regVal, rnum]
  rw [ht, hcanon] at hacc
  have hav : Avoids F op.bytes ((A (.x 1) (.x 2)).addr ctx op.bytes
      (Arm.w (.GPR 2#5) (Arm.r (.GPR (rnum n2)) s) (Arm.w (.GPR 1#5) (Arm.r (.GPR (rnum n1)) s)
        (Arm.w (.GPR 0#5) (Arm.r (.GPR (rnum n0)) s) w)))) :=
    hacc _ (List.mem_singleton_self _)
  rw [hg, show rnum 1 = 1#5 from rfl, show rnum 2 = 2#5 from rfl, Arm.r_of_w_same,
    Arm.r_of_w_different (by simp), Arm.r_of_w_same, ← hg] at hav
  refine (mstore_writes ctx (hA n1 n2 hn1.1 hn2.1) (fun e => absurd e hop) hl env s).mono ?_
  rintro a ⟨k, hk, rfl⟩
  exact hav k hk

theorem accW_storeRelease (ty : CTy) (hty : AtomTy ty) (fl : Clif.MemFlags) (x a : Nat) :
    AccW F ctx #[⟨a, .int, .use, .early, .reg⟩, ⟨x, .int, .use, .early, .reg⟩]
      (fun r => .storeRelease ty (r.getD 1 .xzr) (r.getD 0 .xzr) fl) := by
  intro regs s w ha hw hacc ls ps ps' hl env
  have hsz := ha.size
  simp only [List.size_toArray, List.length_cons, List.length_nil] at hsz
  have hf := ha.fits
  obtain ⟨r0, r1, rfl⟩ := regs2 hsz
  simp [RegFits] at hf
  rcases hf with ⟨⟨n0, rfl, hn0⟩, ⟨n1, rfl, hn1⟩⟩
  have hcanon : canonRegs #[⟨a, .int, .use, .early, .reg⟩, ⟨x, .int, .use, .early, .reg⟩] =
      #[.x 0, .x 1] := by
    simp [canonRegs, canonReg, canonBase, List.range_succ]
  have ht : placeUses #[⟨a, .int, .use, .early, .reg⟩, ⟨x, .int, .use, .early, .reg⟩]
      (canonRegs #[⟨a, .int, .use, .early, .reg⟩, ⟨x, .int, .use, .early, .reg⟩])
      (useVals #[⟨a, .int, .use, .early, .reg⟩, ⟨x, .int, .use, .early, .reg⟩] #[.x n0, .x n1] s) w =
      Arm.w (.GPR 1#5) (Arm.r (.GPR (rnum n1)) s) (Arm.w (.GPR 0#5) (Arm.r (.GPR (rnum n0)) s) w) := by
    simp [placeUses, useVals, hcanon, Operand.isUse, lo64, regVal, rnum]
  rw [ht, hcanon] at hacc
  have hav : Avoids F ty.bytes (regX (Arm.w (.GPR 1#5) (Arm.r (.GPR (rnum n1)) s)
      (Arm.w (.GPR 0#5) (Arm.r (.GPR (rnum n0)) s) w)) (.x 0)) :=
    hacc _ (List.mem_singleton_self _)
  simp only [regX] at hav
  rw [show rnum 0 = 0#5 from rfl, Arm.r_of_w_different (by simp), Arm.r_of_w_same] at hav
  simp only [MInst.lines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl
  obtain ⟨rfl, -⟩ := hl
  refine linesWrites_cons (by simp) fun env' y hy p hp k hk => ?_
  rw [memWrites_excl (rs := .xzr) (show BaseOk (.x n0) from by simp [BaseOk]; omega) (.inl hy),
    List.mem_singleton] at hp
  subst hp
  have hb : ty.bits / 8 = ty.bytes := by rcases hty with rfl | rfl | rfl | rfl <;> rfl
  exact hav k (by simpa [hb] using hk)

end

open E2E.ExecBytes E2E.ExecFrame in
/-- **An `str`/`stur` of an `s`/`d` register with a final addressing mode writes `sz.bytes`
bytes at its address.** -/
theorem memWrites_fpuStore (ctx : FnCtx) {sz : ScalarSize} (hsz : FpSz sz) {rt : Reg} {m : AMode}
    (hm : FinalAM sz.bytes m) {env : Env} {a : Arm.ArmInst}
    (h : (Insn.fpuStore sz rt m).toArmInst env = .ok a) (s : Arm.ArmState) :
    MemWrites a s = [(m.addr ctx sz.bytes s, sz.bytes)] := by
  simp only [Insn.toArmInst, Functor.map, Except.map] at h
  split at h
  · cases h
  rename_i a0 h0
  simp only [Except.ok.injEq] at h
  subst h
  rw [memWrites_norm]
  obtain ⟨Rt, h0⟩ : ∃ Rt, ldstFields (fpSizeF sz) 1 0 sz.bytes Rt m = .ok a0 := by
    rcases hsz with rfl | rfl <;>
      simp only [Insn.armFields, Insn.armFields.fpLdstSize, bind, Except.bind, pure,
        Except.pure] at h0 <;>
      (repeat' split at h0) <;> first | cases h0 | exact ⟨_, h0⟩
  cases m with
  | unsignedOffset rn off =>
    obtain ⟨hb, h1, h2⟩ := hm
    obtain ⟨Rn, hRn, hr, -⟩ := enc_base hb s
    simp only [ldstFields, h1, uField, h2, hRn, bne_iff_ne, ne_eq, not_true_eq_false, ite_false,
      ite_true, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at h0
    subst h0
    have hv := uimm_value sz.bytes (by rcases fpSz_bytes hsz with e | e <;> omega) off h1 h2
    rcases hsz with rfl | rfl <;> simp (config := {decide := true}) [MemWrites, RegImm.writes,
      RegImm.memop, RegImm.ofUnsigned, RegImm.addr, RegImm.scale, fpSizeF, Arm.BitVec.lsb, hr,
      AMode.addr, Arm.LDST.Reg_offset.value, ScalarSize.bytes, log2] at h1 h2 hv ⊢
    all_goals exact hv
  | unscaled rn off =>
    obtain ⟨hb, h1, h2⟩ := hm
    obtain ⟨Rn, hRn, hr, -⟩ := enc_base hb s
    simp only [ldstFields, sField, hRn, show -(2 ^ (9 - 1) : Int) ≤ off ∧ off < 2 ^ (9 - 1) by omega,
      and_self, ite_true, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at h0
    subst h0
    have hv := simm9_value off h1 h2
    rcases hsz with rfl | rfl <;> simp (config := {decide := true}) [MemWrites, ldsturWrites,
      fpSizeF, hr, AMode.addr, ScalarSize.bytes, hv]
  | regReg rn rm =>
    obtain ⟨hb, hi⟩ := hm
    obtain ⟨Rn, hRn, hr, -⟩ := enc_base hb s
    obtain ⟨Rm, hRm, hrm⟩ := enc_idx hi s
    simp only [ldstFields, hRn, hRm, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at h0
    subst h0
    rcases hsz with rfl | rfl <;> simp (config := {decide := true}) [MemWrites, RegImm.writes,
      RegImm.memop, RegImm.ofRegOffset, RegImm.addr, RegImm.scale, fpSizeF, Arm.BitVec.lsb, hr,
      AMode.addr, Arm.LDST.Reg_offset.value, ScalarSize.bytes, log2, hrm, extend_reg_uxtx0]
  | regScaled rn rm =>
    obtain ⟨hb, hi⟩ := hm
    obtain ⟨Rn, hRn, hr, -⟩ := enc_base hb s
    obtain ⟨Rm, hRm, hrm⟩ := enc_idx hi s
    simp only [ldstFields, hRn, hRm, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at h0
    subst h0
    rcases hsz with rfl | rfl <;> simp (config := {decide := true}) [MemWrites, RegImm.writes,
      RegImm.memop, RegImm.ofRegOffset, RegImm.addr, RegImm.scale, fpSizeF, Arm.BitVec.lsb, hr,
      AMode.addr, Arm.LDST.Reg_offset.value, ScalarSize.bytes, log2, hrm, extend_reg_uxtx]
  | regScaledExtended rn rm e =>
    obtain ⟨hb, hi, he⟩ := hm
    obtain ⟨Rn, hRn, hr, -⟩ := enc_base hb s
    obtain ⟨Rm, hRm, hrm⟩ := enc_idx hi s
    rcases he with rfl | rfl | rfl | rfl <;>
    simp only [ldstFields, hRn, hRm, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at h0 <;>
    (simp (config := {decide := true}) only [ite_false, Bool.not_true, Bool.false_eq_true,
      Bool.true_or, Bool.or_true, beq_self_eq_true, pure, Except.pure, Except.ok.injEq] at h0) <;>
    subst h0 <;>
    rcases hsz with rfl | rfl <;> simp (config := {decide := true}) [MemWrites, RegImm.writes,
      RegImm.memop, RegImm.ofRegOffset, RegImm.addr, RegImm.scale, fpSizeF, Arm.BitVec.lsb, hr,
      AMode.addr, Arm.LDST.Reg_offset.value, ScalarSize.bytes, log2, hrm, ExtendOp.bits]
    all_goals done
  | regExtended rn rm e =>
    obtain ⟨hb, hi, he⟩ := hm
    obtain ⟨Rn, hRn, hr, -⟩ := enc_base hb s
    obtain ⟨Rm, hRm, hrm⟩ := enc_idx hi s
    rcases he with rfl | rfl | rfl | rfl <;>
    simp only [ldstFields, hRn, hRm, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at h0 <;>
    (simp (config := {decide := true}) only [ite_false, Bool.not_true, Bool.false_eq_true,
      Bool.true_or, Bool.or_true, beq_self_eq_true, pure, Except.pure, Except.ok.injEq] at h0) <;>
    subst h0 <;>
    rcases hsz with rfl | rfl <;> simp (config := {decide := true}) [MemWrites, RegImm.writes,
      RegImm.memop, RegImm.ofRegOffset, RegImm.addr, RegImm.scale, fpSizeF, Arm.BitVec.lsb, hr,
      AMode.addr, Arm.LDST.Reg_offset.value, ScalarSize.bytes, log2, hrm, ExtendOp.bits]
    all_goals done
  | _ => simp [FinalAM] at hm

/-- **The writes of an `fpuStore`'s lines**: only the access itself. -/
theorem fstore_writes (ctx : FnCtx) {sz : ScalarSize} (hsz : FpSz sz) {rt : Reg} {m : AMode}
    {fl : Clif.MemFlags} (hm : MemMode sz.bytes m) {ps : PState} {ls : List Line} {ps' : PState}
    (hl : (MInst.fpuStore sz rt m fl).lines ctx ps = .ok (ls, ps')) (env : Env) (s : Arm.ArmState) :
    LinesWrites env ls s (fun a => ∃ k < sz.bytes, a = m.addr ctx sz.bytes s + BitVec.ofNat 64 k) := by
  simp only [MInst.lines, bind, Except.bind] at hl
  split at hl
  · cases hl
  rename_i r hr
  obtain ⟨pre, m'⟩ := r
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl
  obtain ⟨rfl, -⟩ := hl
  obtain ⟨-, h2, h3⟩ := memFinalize_addr ctx (by rcases fpSz_bytes hsz with e | e <;> omega)
    hm hr env s
  refine linesWrites_append_last (memFinalize_noStores hr) fun s1 hs1 env' a ha p hp i hi => ?_
  rw [memWrites_fpuStore ctx hsz h2 ha, List.mem_singleton] at hp
  subst hp
  exact ⟨i, hi, by rw [h3 s1 hs1]⟩


section
variable (F : BitVec 64 → Prop) (ctx : FnCtx)

theorem accW_fpuStore0g (sz : ScalarSize) (hsz : FpSz sz) (d : Nat) (am : AMode)
    (fl : Clif.MemFlags) (hmm : MemMode sz.bytes am)
    (hA : ∀ (s w : Arm.ArmState) (v : CV), SameWorld F s w →
      am.addr ctx sz.bytes (Arm.w (.SFP 0#5) v w) = am.addr ctx sz.bytes s) :
    AccW F ctx #[⟨d, .float, .use, .early, .reg⟩] (fun r => .fpuStore sz (r.getD 0 .xzr) am fl) := by
  intro regs s w ha hw hacc ls ps ps' hl env
  have hsz' := ha.size
  simp only [List.size_toArray, List.length_cons, List.length_nil] at hsz'
  have hf := ha.fits
  obtain ⟨r0, rfl⟩ := regs1 hsz'
  simp [RegFits] at hf
  rcases hf with ⟨n0, rfl, hn0⟩
  have hcanon : canonRegs #[⟨d, .float, .use, .early, .reg⟩] = #[.v 0] := by
    simp [canonRegs, canonReg, canonBase, List.range_succ]
  have ht : placeUses #[⟨d, .float, .use, .early, .reg⟩] (canonRegs #[⟨d, .float, .use, .early, .reg⟩])
      (useVals #[⟨d, .float, .use, .early, .reg⟩] #[.v n0] s) w =
      Arm.w (.SFP 0#5) (Arm.r (.SFP (rnum n0)) s) w := by
    simp [placeUses, useVals, hcanon, Operand.isUse, regVal, rnum]
  rw [ht, hcanon] at hacc
  have hav : Avoids F sz.bytes (am.addr ctx sz.bytes (Arm.w (.SFP 0#5) (Arm.r (.SFP (rnum n0)) s) w)) :=
    hacc _ (List.mem_singleton_self _)
  rw [hA s w _ hw] at hav
  refine (fstore_writes ctx hsz hmm hl env s).mono ?_
  rintro a ⟨k, hk, rfl⟩
  exact hav k hk

theorem accW_fpuStore1 (sz : ScalarSize) (hsz : FpSz sz) (d n : Nat) (fl : Clif.MemFlags)
    (A : Reg → AMode) (g : BitVec 64 → BitVec 64)
    (hA : ∀ a : Nat, a < 29 → MemMode sz.bytes (A (.x a)))
    (hg : ∀ (a : Nat) s, (A (.x a)).addr ctx sz.bytes s = g (Arm.r (.GPR (rnum a)) s)) :
    AccW F ctx #[⟨d, .float, .use, .early, .reg⟩, ⟨n, .int, .use, .early, .reg⟩]
      (fun r => .fpuStore sz (r.getD 0 .xzr) (A (r.getD 1 .xzr)) fl) := by
  intro regs s w ha hw hacc ls ps ps' hl env
  have hsz' := ha.size
  simp only [List.size_toArray, List.length_cons, List.length_nil] at hsz'
  have hf := ha.fits
  obtain ⟨r0, r1, rfl⟩ := regs2 hsz'
  simp [RegFits] at hf
  rcases hf with ⟨⟨n0, rfl, hn0⟩, ⟨n1, rfl, hn1⟩⟩
  have hcanon : canonRegs #[⟨d, .float, .use, .early, .reg⟩, ⟨n, .int, .use, .early, .reg⟩] =
      #[.v 0, .x 1] := by
    simp [canonRegs, canonReg, canonBase, List.range_succ]
  have ht : placeUses #[⟨d, .float, .use, .early, .reg⟩, ⟨n, .int, .use, .early, .reg⟩]
      (canonRegs #[⟨d, .float, .use, .early, .reg⟩, ⟨n, .int, .use, .early, .reg⟩])
      (useVals #[⟨d, .float, .use, .early, .reg⟩, ⟨n, .int, .use, .early, .reg⟩] #[.v n0, .x n1] s) w =
      Arm.w (.GPR 1#5) (Arm.r (.GPR (rnum n1)) s) (Arm.w (.SFP 0#5) (Arm.r (.SFP (rnum n0)) s) w) := by
    simp [placeUses, useVals, hcanon, Operand.isUse, lo64, regVal, rnum]
  rw [ht, hcanon] at hacc
  have hav : Avoids F sz.bytes ((A (.x 1)).addr ctx sz.bytes
      (Arm.w (.GPR 1#5) (Arm.r (.GPR (rnum n1)) s) (Arm.w (.SFP 0#5) (Arm.r (.SFP (rnum n0)) s) w))) :=
    hacc _ (List.mem_singleton_self _)
  rw [hg, show rnum 1 = 1#5 from rfl, Arm.r_of_w_same, ← hg] at hav
  refine (fstore_writes ctx hsz (hA n1 hn1.1) hl env s).mono ?_
  rintro a ⟨k, hk, rfl⟩
  exact hav k hk

theorem accW_fpuStore2 (sz : ScalarSize) (hsz : FpSz sz) (d n m : Nat) (fl : Clif.MemFlags)
    (A : Reg → Reg → AMode) (g : BitVec 64 → BitVec 64 → BitVec 64)
    (hA : ∀ a b : Nat, a < 29 → b < 29 → MemMode sz.bytes (A (.x a) (.x b)))
    (hg : ∀ (a b : Nat) s, (A (.x a) (.x b)).addr ctx sz.bytes s =
      g (Arm.r (.GPR (rnum a)) s) (Arm.r (.GPR (rnum b)) s)) :
    AccW F ctx #[⟨d, .float, .use, .early, .reg⟩, ⟨n, .int, .use, .early, .reg⟩,
      ⟨m, .int, .use, .early, .reg⟩]
      (fun r => .fpuStore sz (r.getD 0 .xzr) (A (r.getD 1 .xzr) (r.getD 2 .xzr)) fl) := by
  intro regs s w ha hw hacc ls ps ps' hl env
  have hsz' := ha.size
  simp only [List.size_toArray, List.length_cons, List.length_nil] at hsz'
  have hf := ha.fits
  obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz'
  simp [RegFits] at hf
  rcases hf with ⟨⟨n0, rfl, hn0⟩, ⟨n1, rfl, hn1⟩, ⟨n2, rfl, hn2⟩⟩
  have hcanon : canonRegs #[⟨d, .float, .use, .early, .reg⟩, ⟨n, .int, .use, .early, .reg⟩,
      ⟨m, .int, .use, .early, .reg⟩] = #[.v 0, .x 1, .x 2] := by
    simp [canonRegs, canonReg, canonBase, List.range_succ]
  have ht : placeUses #[⟨d, .float, .use, .early, .reg⟩, ⟨n, .int, .use, .early, .reg⟩,
      ⟨m, .int, .use, .early, .reg⟩]
      (canonRegs #[⟨d, .float, .use, .early, .reg⟩, ⟨n, .int, .use, .early, .reg⟩,
        ⟨m, .int, .use, .early, .reg⟩])
      (useVals #[⟨d, .float, .use, .early, .reg⟩, ⟨n, .int, .use, .early, .reg⟩,
        ⟨m, .int, .use, .early, .reg⟩] #[.v n0, .x n1, .x n2] s) w =
      Arm.w (.GPR 2#5) (Arm.r (.GPR (rnum n2)) s) (Arm.w (.GPR 1#5) (Arm.r (.GPR (rnum n1)) s)
        (Arm.w (.SFP 0#5) (Arm.r (.SFP (rnum n0)) s) w)) := by
    simp [placeUses, useVals, hcanon, Operand.isUse, lo64, regVal, rnum]
  rw [ht, hcanon] at hacc
  have hav : Avoids F sz.bytes ((A (.x 1) (.x 2)).addr ctx sz.bytes
      (Arm.w (.GPR 2#5) (Arm.r (.GPR (rnum n2)) s) (Arm.w (.GPR 1#5) (Arm.r (.GPR (rnum n1)) s)
        (Arm.w (.SFP 0#5) (Arm.r (.SFP (rnum n0)) s) w)))) :=
    hacc _ (List.mem_singleton_self _)
  rw [hg, show rnum 1 = 1#5 from rfl, show rnum 2 = 2#5 from rfl, Arm.r_of_w_same,
    Arm.r_of_w_different (by simp), Arm.r_of_w_same, ← hg] at hav
  refine (fstore_writes ctx hsz (hA n1 n2 hn1.1 hn2.1) hl env s).mono ?_
  rintro a ⟨k, hk, rfl⟩
  exact hav k hk

end

/-! ## The covered forms -/

set_option maxHeartbeats 4000000 in
/-- The writes of an allocated covered `fpuStore`. -/
theorem formOk_fpuStore_writes {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {sz : ScalarSize}
    {d : Nat} {m : AMode} {fl : Clif.MemFlags}
    (h : ((sz == .size32 || sz == .size64) && memOk sz.bytes m) = true) {ops : Array Operand}
    (hops : (MInst.fpuStore sz (.vreg d .float) m fl).operands = .ok ops)
    {regs : Array Reg} {i' : MInst} {s w : Arm.ArmState} {r : List CV × Arm.ArmState × Ctl}
    {ls : List Line} {ps ps' : PState} (ha : AllocOk ops regs)
    (hasg : (MInst.fpuStore sz (.vreg d .float) m fl).assign regs = .ok i')
    (hl : i'.lines ctx ps = .ok (ls, ps'))
    (hw : SameWorld F s w) (he : Arm.r .ERR w = .None) (hal : Arm.CheckSPAlignment w)
    (hsem : csem F ctx X (.fpuStore sz (.vreg d .float) m fl) (useVals ops regs s) w = some r)
    (env : Env) : LinesWrites env ls s (fun a => ¬ F a) := by
  have hfo : FormOk ctx (.fpuStore sz (.vreg d .float) m fl) = true := h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hszb, hm⟩ := h
  have hsz := fpSz_of_beq hszb
  unfold memOk at hm
  split at hm <;> (try cases hm) <;> (try simp only [decide_eq_true_eq] at hm)
  all_goals first
    | exact writes_of_accW rfl _ (by assign_tac) hfo rfl
        (accW_fpuStore0g F ctx _ hsz _ (.slotOffset _) _ trivial fun s w v hw => by
          simp only [AMode.addr, spOf]
          rw [Arm.r_of_w_different (by simp), sw_r_eq hw (by simp [Masked])])
        hops ha hasg hl hw he hal hsem env
    | exact writes_of_accW rfl _ (by assign_tac) hfo rfl
        (accW_fpuStore0g F ctx _ hsz _ (.spOffset _) _ trivial fun s w v hw => by
          simp only [AMode.addr, spOf]
          rw [Arm.r_of_w_different (by simp), sw_r_eq hw (by simp [Masked])])
        hops ha hasg hl hw he hal hsem env
    | exact writes_of_accW rfl _ (by assign_tac) hfo rfl
        (accW_fpuStore0g F ctx _ hsz _ (.fpOffset _) _ trivial fun s w v hw => by
          simp only [AMode.addr, regX]
          rw [Arm.r_of_w_different (by simp), sw_r_eq hw (by simp [Masked, rnum])])
        hops ha hasg hl hw he hal hsem env
    | exact writes_of_accW rfl _ (by assign_tac) hfo rfl
        (accW_fpuStore1 F ctx _ hsz _ _ _ (fun r => .unscaled r _) (fun a => a + BitVec.ofInt 64 _)
          (mm_unscaled hm.1 hm.2) (fun _ _ => rfl))
        hops ha hasg hl hw he hal hsem env
    | exact writes_of_accW rfl _ (by assign_tac) hfo rfl
        (accW_fpuStore1 F ctx _ hsz _ _ _ (fun r => .unsignedOffset r _)
          (fun a => a + BitVec.ofNat 64 _) (mm_uoff hm.1 hm.2) (fun _ _ => rfl))
        hops ha hasg hl hw he hal hsem env
    | exact writes_of_accW rfl _ (by assign_tac) hfo rfl
        (accW_fpuStore2 F ctx _ hsz _ _ _ _ .regReg (fun a b => a + b) mm_regReg (fun _ _ _ => rfl))
        hops ha hasg hl hw he hal hsem env
    | exact writes_of_accW rfl _ (by assign_tac) hfo rfl
        (accW_fpuStore2 F ctx _ hsz _ _ _ _ .regScaled (fun a b => a + b <<< log2 _) mm_regScaled
          (fun _ _ _ => rfl))
        hops ha hasg hl hw he hal hsem env
    | exact writes_of_accW rfl _ (by assign_tac) hfo rfl
        (accW_fpuStore2 F ctx _ hsz _ _ _ _ (fun a b => .regScaledExtended a b _)
          (fun a b => a + Arm.extend_reg b (Arm.decode_reg_extend _) (log2 _))
          (mm_regScaledExtended hm) (fun _ _ _ => rfl))
        hops ha hasg hl hw he hal hsem env
    | exact writes_of_accW rfl _ (by assign_tac) hfo rfl
        (accW_fpuStore2 F ctx _ hsz _ _ _ _ (fun a b => .regExtended a b _)
          (fun a b => a + Arm.extend_reg b (Arm.decode_reg_extend _) 0)
          (mm_regExtended hm) (fun _ _ _ => rfl))
        hops ha hasg hl hw he hal hsem env

set_option maxHeartbeats 4000000 in
/-- The writes of an allocated covered integer `store`. -/
theorem formOk_store_writes {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {op : StoreOp}
    {d : Nat} {m : AMode} {fl : Clif.MemFlags}
    (h : (op != .fpuStore128 && memOk op.bytes m) = true) {ops : Array Operand}
    (hops : (MInst.store op (.vreg d .int) m fl).operands = .ok ops)
    {regs : Array Reg} {i' : MInst} {s w : Arm.ArmState} {r : List CV × Arm.ArmState × Ctl}
    {ls : List Line} {ps ps' : PState} (ha : AllocOk ops regs)
    (hasg : (MInst.store op (.vreg d .int) m fl).assign regs = .ok i')
    (hl : i'.lines ctx ps = .ok (ls, ps'))
    (hw : SameWorld F s w) (he : Arm.r .ERR w = .None) (hal : Arm.CheckSPAlignment w)
    (hsem : csem F ctx X (.store op (.vreg d .int) m fl) (useVals ops regs s) w = some r)
    (env : Env) : LinesWrites env ls s (fun a => ¬ F a) := by
  have hfo : FormOk ctx (.store op (.vreg d .int) m fl) = true := h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨hop, hm⟩ := h
  unfold memOk at hm
  split at hm <;> (try cases hm) <;> (try simp only [decide_eq_true_eq] at hm)
  all_goals first
    | exact writes_of_accW rfl _ (by assign_tac) hfo rfl
        (accW_store0g F ctx _ hop _ (.slotOffset _) _ trivial fun s w v hw => by
          simp only [AMode.addr, spOf]
          rw [Arm.r_of_w_different (by simp), sw_r_eq hw (by simp [Masked])])
        hops ha hasg hl hw he hal hsem env
    | exact writes_of_accW rfl _ (by assign_tac) hfo rfl
        (accW_store0g F ctx _ hop _ (.spOffset _) _ trivial fun s w v hw => by
          simp only [AMode.addr, spOf]
          rw [Arm.r_of_w_different (by simp), sw_r_eq hw (by simp [Masked])])
        hops ha hasg hl hw he hal hsem env
    | exact writes_of_accW rfl _ (by assign_tac) hfo rfl
        (accW_store0g F ctx _ hop _ (.fpOffset _) _ trivial fun s w v hw => by
          simp only [AMode.addr, regX]
          rw [Arm.r_of_w_different (by simp [rnum]), sw_r_eq hw (by simp [Masked, rnum])])
        hops ha hasg hl hw he hal hsem env
    | exact writes_of_accW rfl _ (by assign_tac) hfo rfl
        (accW_store1 F ctx _ hop _ _ _ (fun r => .unscaled r _) (fun a => a + BitVec.ofInt 64 _)
          (mm_unscaled hm.1 hm.2) (fun _ _ => rfl))
        hops ha hasg hl hw he hal hsem env
    | exact writes_of_accW rfl _ (by assign_tac) hfo rfl
        (accW_store1 F ctx _ hop _ _ _ (fun r => .unsignedOffset r _)
          (fun a => a + BitVec.ofNat 64 _) (mm_uoff hm.1 hm.2) (fun _ _ => rfl))
        hops ha hasg hl hw he hal hsem env
    | exact writes_of_accW rfl _ (by assign_tac) hfo rfl
        (accW_store2 F ctx _ hop _ _ _ _ .regReg (fun a b => a + b) mm_regReg (fun _ _ _ => rfl))
        hops ha hasg hl hw he hal hsem env
    | exact writes_of_accW rfl _ (by assign_tac) hfo rfl
        (accW_store2 F ctx _ hop _ _ _ _ .regScaled (fun a b => a + b <<< log2 _) mm_regScaled
          (fun _ _ _ => rfl))
        hops ha hasg hl hw he hal hsem env
    | exact writes_of_accW rfl _ (by assign_tac) hfo rfl
        (accW_store2 F ctx _ hop _ _ _ _ (fun a b => .regScaledExtended a b _)
          (fun a b => a + Arm.extend_reg b (Arm.decode_reg_extend _) (log2 _))
          (mm_regScaledExtended hm) (fun _ _ _ => rfl))
        hops ha hasg hl hw he hal hsem env
    | exact writes_of_accW rfl _ (by assign_tac) hfo rfl
        (accW_store2 F ctx _ hop _ _ _ _ (fun a b => .regExtended a b _)
          (fun a b => a + Arm.extend_reg b (Arm.decode_reg_extend _) 0)
          (mm_regExtended hm) (fun _ _ _ => rfl))
        hops ha hasg hl hw he hal hsem env

set_option maxHeartbeats 4000000 in
/-- An allocated covered `load` is not `memWr`. -/
theorem formOk_load_memWr {op : LoadOp} {d : Nat} {m : AMode} {fl : Clif.MemFlags}
    (h : (op != .fpuLoad128 && memOk op.bytes m) = true) {regs : Array Reg} {i' : MInst}
    (hasg : (MInst.load op (.vreg d .int) m fl).assign regs = .ok i') : i'.memWr = false := by
  simp only [Bool.and_eq_true] at h
  obtain ⟨-, hm⟩ := h
  unfold memOk at hm
  split at hm <;> (try cases hm)
  all_goals (assign_inv hasg <;> rfl)

set_option maxHeartbeats 4000000 in
/-- An allocated covered `fpuLoad` is not `memWr`. -/
theorem formOk_fpuLoad_memWr {sz : ScalarSize} {d : Nat} {m : AMode} {fl : Clif.MemFlags}
    (h : ((sz == .size32 || sz == .size64) && memOk sz.bytes m) = true)
    {regs : Array Reg} {i' : MInst}
    (hasg : (MInst.fpuLoad sz (.vreg d .float) m fl).assign regs = .ok i') : i'.memWr = false := by
  simp only [Bool.and_eq_true] at h
  obtain ⟨-, hm⟩ := h
  unfold memOk at hm
  split at hm <;> (try cases hm)
  all_goals (assign_inv hasg <;> rfl)

set_option maxHeartbeats 4000000 in
/-- **The writes of an allocated covered form** avoid the frame addresses `F` (module doc). -/
theorem formOk_writes {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {i : MInst}
    (h : FormOk ctx i = true) {ops : Array Operand} (hops : i.operands = .ok ops)
    {regs : Array Reg} {i' : MInst} {s w : Arm.ArmState} {r : List CV × Arm.ArmState × Ctl}
    {ls : List Line} {ps ps' : PState}
    (ha : AllocOk ops regs) (hasg : i.assign regs = .ok i') (hl : i'.lines ctx ps = .ok (ls, ps'))
    (hw : SameWorld F s w) (he : Arm.r .ERR w = .None) (hal : Arm.CheckSPAlignment w)
    (hsem : csem F ctx X i (useVals ops regs s) w = some r) (env : Env) :
    LinesWrites env ls s (fun a => ¬ F a) := by
  by_cases hmw : i'.memWr = false
  · exact linesWrites_noStores (lines_noStores hl hmw)
  unfold FormOk at h
  split at h
  all_goals first
    | exact formOk_fpuStore_writes h hops ha hasg hl hw he hal hsem env
    | exact formOk_store_writes h hops ha hasg hl hw he hal hsem env
    | exact writes_of_accW rfl _ (by assign_tac) (by simp [FormOk, of_decide_eq_true h]) rfl
        (accW_storeRelease F ctx _ (of_decide_eq_true h) _ _ _) hops ha hasg hl hw he hal hsem env
    | exact absurd (formOk_load_memWr h hasg) hmw
    | exact absurd (formOk_fpuLoad_memWr h hasg) hmw
    | (simp at h; done)
    | (assign_inv hasg <;> exact absurd rfl hmw)

end Backend.Proof
