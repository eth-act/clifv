import FV.Backend.Proof.RegallocCover
import FV.E2E.ExecReads

/-!
# The memory reads of the covered straight-line forms (L3 (c), D2)

`formOk_reads`: the lines of an allocated covered form (`FormOk`), run from a state `s` whose
world `w` gives `csem` a result, read only bytes outside the frame addresses `F`. The forms
other than the loads read nothing (`lines_noLoads`); a load reads `op.bytes` bytes at its address
(`mload_reads`), which is the canonical instance's address (`AccR`, per addressing mode as the
`Corr` proofs of `RegallocMemCorr`), and `csem` (`straightSem`) is defined only when that access
avoids `F` (`AccessOk`); `ldar` likewise.
-/

namespace Backend.Proof

open Backend E2E

/-- **The reads obligation of a form**: the allocated instruction's lines, run from `s`, read only
outside `F`, when the canonical instance's accesses on the canonical state avoid `F`. -/
def AccR (F : BitVec 64 → Prop) (ctx : FnCtx) (ops : Array Operand) (mk : Array Reg → MInst) :
    Prop :=
  ∀ (regs : Array Reg) (s w : Arm.ArmState), AllocOk ops regs → SameWorld F s w →
    AccessOk F ctx (mk (canonRegs ops)) (placeUses ops (canonRegs ops) (useVals ops regs s) w) →
    ∀ ls ps ps', (mk regs).lines ctx ps = .ok (ls, ps') → ∀ env,
      LinesReads env ls s (fun a => ¬ F a)

/-- `AccR` gives the reads of the allocated instruction from `csem`'s result. -/
theorem reads_of_accR {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {i : MInst}
    {ops : Array Operand} (hops : i.operands = .ok ops) (mk : Array Reg → MInst)
    (hmk : ∀ regs : Array Reg, regs.size = ops.size → i.assign regs = .ok (mk regs))
    (hfo : FormOk ctx i = true) (hctl : i.isCtl = false) (hc : AccR F ctx ops mk)
    {ops' : Array Operand} (hops' : i.operands = .ok ops') {regs : Array Reg} {i' : MInst}
    {s w : Arm.ArmState} {r : List CV × Arm.ArmState × Ctl} {ls : List Line} {ps ps' : PState}
    (ha : AllocOk ops' regs) (hasg : i.assign regs = .ok i') (hl : i'.lines ctx ps = .ok (ls, ps'))
    (hw : SameWorld F s w) (he : Arm.r .ERR w = .None) (hal : Arm.CheckSPAlignment w)
    (hsem : csem F ctx X i (useVals ops' regs s) w = some r) (env : Env) :
    LinesReads env ls s (fun a => ¬ F a) := by
  rw [hops] at hops'
  cases hops'
  rw [hmk regs ha.size] at hasg
  cases hasg
  rw [csem_of_wf hctl (by simp [csemWF, hfo, hops, useVals_length ops regs ha.size]) he hal] at hsem
  simp only [straightSem, hops, hmk _ (canonRegs_size ops)] at hsem
  split at hsem
  · exact hc regs s w ha hw ‹_› ls ps ps' hl env
  · cases hsem

/-! ## `AccR` of the loads -/

section
variable (F : BitVec 64 → Prop) (ctx : FnCtx)

theorem accR_load0g (op : LoadOp) (hop : op ≠ .fpuLoad128) (d : Nat) (am : AMode)
    (fl : Clif.MemFlags) (hmm : MemMode op.bytes am)
    (hA : ∀ s w : Arm.ArmState, SameWorld F s w → am.addr ctx op.bytes w = am.addr ctx op.bytes s) :
    AccR F ctx #[⟨d, .int, .def, .late, .reg⟩] (fun r => .load op (r.getD 0 .xzr) am fl) := by
  intro regs s w ha hw hacc ls ps ps' hl env
  have hsz := ha.size
  simp only [List.size_toArray, List.length_cons, List.length_nil] at hsz
  obtain ⟨r0, rfl⟩ := regs1 hsz
  have hcanon : canonRegs #[⟨d, .int, .def, .late, .reg⟩] = #[.x 0] := by
    simp [canonRegs, canonReg, canonBase, List.range_succ]
  have ht : placeUses #[⟨d, .int, .def, .late, .reg⟩] (canonRegs #[⟨d, .int, .def, .late, .reg⟩])
      (useVals #[⟨d, .int, .def, .late, .reg⟩] #[r0] s) w = w := by
    simp [placeUses, useVals, hcanon, Operand.isUse]
  rw [ht, hcanon] at hacc
  have hav : Avoids F op.bytes (am.addr ctx op.bytes w) := hacc _ (List.mem_singleton_self _)
  refine (mload_reads ctx hmm (fun e => absurd e hop) hl env s).mono ?_
  rintro a ⟨k, hk, rfl⟩
  rw [← hA s w hw]
  exact hav k hk

theorem accR_load1 (op : LoadOp) (hop : op ≠ .fpuLoad128) (d n : Nat) (fl : Clif.MemFlags)
    (A : Reg → AMode) (g : BitVec 64 → BitVec 64)
    (hA : ∀ a : Nat, a < 29 → MemMode op.bytes (A (.x a)))
    (hg : ∀ (a : Nat) s, (A (.x a)).addr ctx op.bytes s = g (Arm.r (.GPR (rnum a)) s)) :
    AccR F ctx #[⟨d, .int, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩]
      (fun r => .load op (r.getD 0 .xzr) (A (r.getD 1 .xzr)) fl) := by
  intro regs s w ha hw hacc ls ps ps' hl env
  have hsz := ha.size
  simp only [List.size_toArray, List.length_cons, List.length_nil] at hsz
  have hf := ha.fits
  obtain ⟨r0, r1, rfl⟩ := regs2 hsz
  simp [RegFits] at hf
  rcases hf with ⟨⟨n0, rfl, hn0⟩, ⟨n1, rfl, hn1⟩⟩
  have hcanon : canonRegs #[⟨d, .int, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩] =
      #[.x 0, .x 1] := by
    simp [canonRegs, canonReg, canonBase, List.range_succ]
  have ht : placeUses #[⟨d, .int, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩]
      (canonRegs #[⟨d, .int, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩])
      (useVals #[⟨d, .int, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩] #[.x n0, .x n1] s) w =
      Arm.w (.GPR 1#5) (Arm.r (.GPR (rnum n1)) s) w := by
    simp [placeUses, useVals, hcanon, Operand.isUse, lo64, regVal, rnum]
  rw [ht, hcanon] at hacc
  have hav : Avoids F op.bytes ((A (.x 1)).addr ctx op.bytes
      (Arm.w (.GPR 1#5) (Arm.r (.GPR (rnum n1)) s) w)) := hacc _ (List.mem_singleton_self _)
  rw [hg, show rnum 1 = 1#5 from rfl, Arm.r_of_w_same, ← hg] at hav
  refine (mload_reads ctx (hA n1 hn1.1) (fun e => absurd e hop) hl env s).mono ?_
  rintro a ⟨k, hk, rfl⟩
  exact hav k hk

theorem accR_load2 (op : LoadOp) (hop : op ≠ .fpuLoad128) (d n m : Nat) (fl : Clif.MemFlags)
    (A : Reg → Reg → AMode) (g : BitVec 64 → BitVec 64 → BitVec 64)
    (hA : ∀ a b : Nat, a < 29 → b < 29 → MemMode op.bytes (A (.x a) (.x b)))
    (hg : ∀ (a b : Nat) s, (A (.x a) (.x b)).addr ctx op.bytes s =
      g (Arm.r (.GPR (rnum a)) s) (Arm.r (.GPR (rnum b)) s)) :
    AccR F ctx #[⟨d, .int, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩,
      ⟨m, .int, .use, .early, .reg⟩]
      (fun r => .load op (r.getD 0 .xzr) (A (r.getD 1 .xzr) (r.getD 2 .xzr)) fl) := by
  intro regs s w ha hw hacc ls ps ps' hl env
  have hsz := ha.size
  simp only [List.size_toArray, List.length_cons, List.length_nil] at hsz
  have hf := ha.fits
  obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz
  simp [RegFits] at hf
  rcases hf with ⟨⟨n0, rfl, hn0⟩, ⟨n1, rfl, hn1⟩, ⟨n2, rfl, hn2⟩⟩
  have hcanon : canonRegs #[⟨d, .int, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩,
      ⟨m, .int, .use, .early, .reg⟩] = #[.x 0, .x 1, .x 2] := by
    simp [canonRegs, canonReg, canonBase, List.range_succ]
  have ht : placeUses #[⟨d, .int, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩,
      ⟨m, .int, .use, .early, .reg⟩]
      (canonRegs #[⟨d, .int, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩,
        ⟨m, .int, .use, .early, .reg⟩])
      (useVals #[⟨d, .int, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩,
        ⟨m, .int, .use, .early, .reg⟩] #[.x n0, .x n1, .x n2] s) w =
      Arm.w (.GPR 2#5) (Arm.r (.GPR (rnum n2)) s) (Arm.w (.GPR 1#5) (Arm.r (.GPR (rnum n1)) s) w) := by
    simp [placeUses, useVals, hcanon, Operand.isUse, lo64, regVal, rnum]
  rw [ht, hcanon] at hacc
  have hav : Avoids F op.bytes ((A (.x 1) (.x 2)).addr ctx op.bytes
      (Arm.w (.GPR 2#5) (Arm.r (.GPR (rnum n2)) s) (Arm.w (.GPR 1#5) (Arm.r (.GPR (rnum n1)) s) w))) :=
    hacc _ (List.mem_singleton_self _)
  rw [hg, show rnum 1 = 1#5 from rfl, show rnum 2 = 2#5 from rfl, Arm.r_of_w_same,
    Arm.r_of_w_different (by simp), Arm.r_of_w_same, ← hg] at hav
  refine (mload_reads ctx (hA n1 n2 hn1.1 hn2.1) (fun e => absurd e hop) hl env s).mono ?_
  rintro a ⟨k, hk, rfl⟩
  exact hav k hk

theorem accR_loadAcquire (ty : CTy) (hty : AtomTy ty) (fl : Clif.MemFlags) (d a : Nat) :
    AccR F ctx #[⟨a, .int, .use, .early, .reg⟩, ⟨d, .int, .def, .late, .reg⟩]
      (fun r => .loadAcquire ty (r.getD 1 .xzr) (r.getD 0 .xzr) fl) := by
  intro regs s w ha hw hacc ls ps ps' hl env
  have hsz := ha.size
  simp only [List.size_toArray, List.length_cons, List.length_nil] at hsz
  have hf := ha.fits
  obtain ⟨r0, r1, rfl⟩ := regs2 hsz
  simp [RegFits] at hf
  rcases hf with ⟨⟨n0, rfl, hn0⟩, ⟨n1, rfl, hn1⟩⟩
  have hcanon : canonRegs #[⟨a, .int, .use, .early, .reg⟩, ⟨d, .int, .def, .late, .reg⟩] =
      #[.x 0, .x 1] := by
    simp [canonRegs, canonReg, canonBase, List.range_succ]
  have ht : placeUses #[⟨a, .int, .use, .early, .reg⟩, ⟨d, .int, .def, .late, .reg⟩]
      (canonRegs #[⟨a, .int, .use, .early, .reg⟩, ⟨d, .int, .def, .late, .reg⟩])
      (useVals #[⟨a, .int, .use, .early, .reg⟩, ⟨d, .int, .def, .late, .reg⟩] #[.x n0, .x n1] s) w =
      Arm.w (.GPR 0#5) (Arm.r (.GPR (rnum n0)) s) w := by
    simp [placeUses, useVals, hcanon, Operand.isUse, lo64, regVal, rnum]
  rw [ht, hcanon] at hacc
  have hav : Avoids F ty.bytes (regX (Arm.w (.GPR 0#5) (Arm.r (.GPR (rnum n0)) s) w) (.x 0)) :=
    hacc _ (List.mem_singleton_self _)
  simp only [regX] at hav
  rw [show rnum 0 = 0#5 from rfl, Arm.r_of_w_same] at hav
  simp only [MInst.lines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl
  obtain ⟨rfl, -⟩ := hl
  refine linesReads_cons (by simp) fun env' x hx p hp k hk => ?_
  rw [memReads_excl (show BaseOk (.x n0) from by simp [BaseOk]; omega) (.inl hx),
    List.mem_singleton] at hp
  subst hp
  exact hav k hk

end

/-! ## The covered forms -/

theorem memRd_store {op : StoreOp} {r : Reg} {m : AMode} {fl : Clif.MemFlags}
    (h : op ≠ .fpuStore128) : (MInst.store op r m fl).memRd = false := by
  cases op <;> first | rfl | exact absurd rfl h

set_option maxHeartbeats 4000000 in
/-- **The reads of an allocated covered form** avoid the frame addresses `F` (module doc). -/
theorem formOk_reads {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {i : MInst}
    (h : FormOk ctx i = true) {ops : Array Operand} (hops : i.operands = .ok ops)
    {regs : Array Reg} {i' : MInst} {s w : Arm.ArmState} {r : List CV × Arm.ArmState × Ctl}
    {ls : List Line} {ps ps' : PState}
    (ha : AllocOk ops regs) (hasg : i.assign regs = .ok i') (hl : i'.lines ctx ps = .ok (ls, ps'))
    (hw : SameWorld F s w) (he : Arm.r .ERR w = .None) (hal : Arm.CheckSPAlignment w)
    (hsem : csem F ctx X i (useVals ops regs s) w = some r) (env : Env) :
    LinesReads env ls s (fun a => ¬ F a) := by
  by_cases hmr : i'.memRd = false
  · exact linesReads_noLoads (lines_noLoads hl hmr)
  unfold FormOk at h
  split at h
  rotate_left 32
  · -- loads
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨hop, hm⟩ := h
    unfold memOk at hm
    split at hm <;> (try cases hm) <;> (try simp only [decide_eq_true_eq] at hm)
    all_goals first
      | exact reads_of_accR rfl _ (by assign_tac) (by simp [FormOk, memOk, hop]) rfl
          (accR_load0g F ctx _ hop _ (.slotOffset _) _ trivial fun s w hw => by
            simp only [AMode.addr, spOf]; rw [sw_r_eq hw (by simp [Masked])])
          hops ha hasg hl hw he hal hsem env
      | exact reads_of_accR rfl _ (by assign_tac) (by simp [FormOk, memOk, hop]) rfl
          (accR_load0g F ctx _ hop _ (.spOffset _) _ trivial fun s w hw => by
            simp only [AMode.addr, spOf]; rw [sw_r_eq hw (by simp [Masked])])
          hops ha hasg hl hw he hal hsem env
      | exact reads_of_accR rfl _ (by assign_tac) (by simp [FormOk, memOk, hop]) rfl
          (accR_load0g F ctx _ hop _ (.fpOffset _) _ trivial fun s w hw => by
            simp only [AMode.addr, regX]; rw [sw_r_eq hw (by simp [Masked, rnum])])
          hops ha hasg hl hw he hal hsem env
      | exact reads_of_accR rfl _ (by assign_tac) (by simp [FormOk, memOk, hop, hm]) rfl
          (accR_load1 F ctx _ hop _ _ _ (fun r => .unscaled r _) (fun a => a + BitVec.ofInt 64 _)
            (mm_unscaled hm.1 hm.2) (fun _ _ => rfl))
          hops ha hasg hl hw he hal hsem env
      | exact reads_of_accR rfl _ (by assign_tac) (by simp [FormOk, memOk, hop, hm]) rfl
          (accR_load1 F ctx _ hop _ _ _ (fun r => .unsignedOffset r _)
            (fun a => a + BitVec.ofNat 64 _) (mm_uoff hm.1 hm.2) (fun _ _ => rfl))
          hops ha hasg hl hw he hal hsem env
      | exact reads_of_accR rfl _ (by assign_tac) (by simp [FormOk, memOk, hop]) rfl
          (accR_load2 F ctx _ hop _ _ _ _ .regReg (fun a b => a + b) mm_regReg (fun _ _ _ => rfl))
          hops ha hasg hl hw he hal hsem env
      | exact reads_of_accR rfl _ (by assign_tac) (by simp [FormOk, memOk, hop]) rfl
          (accR_load2 F ctx _ hop _ _ _ _ .regScaled (fun a b => a + b <<< log2 _) mm_regScaled
            (fun _ _ _ => rfl))
          hops ha hasg hl hw he hal hsem env
      | exact reads_of_accR rfl _ (by assign_tac) (by simp [FormOk, memOk, hop, hm]) rfl
          (accR_load2 F ctx _ hop _ _ _ _ (fun a b => .regScaledExtended a b _)
            (fun a b => a + Arm.extend_reg b (Arm.decode_reg_extend _) (log2 _))
            (mm_regScaledExtended hm) (fun _ _ _ => rfl))
          hops ha hasg hl hw he hal hsem env
      | exact reads_of_accR rfl _ (by assign_tac) (by simp [FormOk, memOk, hop, hm]) rfl
          (accR_load2 F ctx _ hop _ _ _ _ (fun a b => .regExtended a b _)
            (fun a b => a + Arm.extend_reg b (Arm.decode_reg_extend _) 0)
            (mm_regExtended hm) (fun _ _ _ => rfl))
          hops ha hasg hl hw he hal hsem env
  · -- stores: no load
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨hop, hm⟩ := h
    unfold memOk at hm
    split at hm <;> (try cases hm)
    all_goals (assign_inv hasg <;> exact absurd (memRd_store hop) hmr)
  rotate_left
  all_goals (try cases h)
  all_goals first
    | exact reads_of_accR rfl _ (by assign_tac) (by simp [FormOk, of_decide_eq_true h]) rfl
        (accR_loadAcquire F ctx _ (of_decide_eq_true h) _ _ _) hops ha hasg hl hw he hal hsem env
    | (assign_inv hasg <;> exact absurd rfl hmr)

end Backend.Proof
