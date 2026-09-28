import FV.Backend.Proof.IselCtlTbz
import FV.Backend.Proof.IselCmpExt
import FV.Backend.Proof.IselTermsImm

/-!
# Family Ctl: `br_table` (`lower_branch` rule 1140)

`br_table idx, default, [targets]` →
`emit_island; ridx = put_in_reg_zext32 idx; cmp ridx, #n (or cmp ridx, rn with rn = imm n);
jt_sequence ridx default targets` (`b.hs default`, then the table entry).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-! ## Semantics -/

theorem operands_jtSeq (d : Label) (ts : List Label) (r a b : Nat) :
    (MInst.jtSequence d ts (.vreg r .int) (.vreg a .int) (.vreg b .int)).operands =
      .ok #[⟨r, .int, .use, .early, .reg⟩, ⟨a, .int, .def, .early, .reg⟩,
        ⟨b, .int, .def, .early, .reg⟩] := rfl

theorem operands_emitIsland (k : Nat) : (MInst.emitIsland k).operands = .ok #[] := rfl

/-- `hs` on the flags of a 32-bit `cmp a, b`: `a ≥ b` unsigned. -/
theorem hs_cmp32 (a b : BitVec 32) :
    condOn Cond.hs.bits (cmpFlags a b) = decide (b.toNat ≤ a.toNat) := by
  have := condOn_cmp_32 .uge a b
  simp only [condOf] at this
  rw [this]
  simp [Clif.Sem.intcc, BitVec.ule]

/-- **The jump-table dispatch**: after a prefix `ms0` which leaves in `r` a register whose low
32 bits are the index and sets the flags so that `hs` is `n ≤ index`, `jt_sequence` goes to
the entry (`index + 1`) or the default (`0`). -/
theorem brTable_termOk_gen {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT} (hR : Refines F isem)
    (hMR : MRStable F MR) {ctx : Ctx} {st st2 : LState} {ms0 : List MInst} (hf : Frag st st2 ms0)
    {d : Label} {ts : List Label} {r a b : Nat} (ha : st.nextVreg ≤ a ∧ a < st2.nextVreg)
    (hb : st.nextVreg ≤ b ∧ b < st2.nextVreg)
    {x : Nat} {dc : Clif.BlockCall} {tbl : List Clif.BlockCall} (hlen : ts.length = tbl.length)
    (hsem : ∀ (fr : Clif.Frame) (ρ : Nat → CV) (v : Clif.Val), ValsHeld fr ρ → DFGCons ctx fr →
      fr.regs x = some v →
      UsesLo st.nextVreg fr (ms0 ++ [.jtSequence d ts (.vreg r .int) (.vreg a .int) (.vreg b .int)]) ∧
      ∀ w, ∃ ρ1 w1, seqRun isem ms0 ρ w = some (.fall ρ1 w1) ∧ SameWorldNF F w1 w ∧
        (Arm.ConditionHolds Cond.hs.bits w1 = decide (tbl.length ≤ v.toNat)) ∧
        ((lo64 (ρ1 r)).setWidth 32).toNat = v.toNat) :
    LowerTermOk isem MR ctx (.brTable x dc tbl) (d :: ts) st
      (st2.emit (.jtSequence d ts (.vreg r .int) (.vreg a .int) (.vreg b .int)))
      (ms0 ++ [.jtSequence d ts (.vreg r .int) (.vreg a .int) (.vreg b .int)]) := by
  have hf2 : Frag st (st2.emit (.jtSequence d ts (.vreg r .int) (.vreg a .int) (.vreg b .int)))
      (ms0 ++ [.jtSequence d ts (.vreg r .int) (.vreg a .int) (.vreg b .int)]) := by
    refine ⟨by simp [LState.emit, hf.emitted], by simpa [LState.emit] using hf.mono, ?_⟩
    intro m hm dd hd
    rcases List.mem_append.1 hm with hm | hm
    · have := hf.defs m hm dd hd; simpa [LState.emit] using this
    · simp only [List.mem_singleton] at hm
      subst hm
      have : dd = a ∨ dd = b := by
        simpa [vdefs, operands_jtSeq, Operand.isDef] using hd
      simp only [LState.emit]
      rcases this with rfl | rfl <;> omega
  refine ⟨hf2.mono, hf2.defs, ?_⟩
  intro fr cm ρ w _ hvh hdfg hmr
  refine ⟨fun i hi => ?_, fun j hj => ?_⟩
  · rw [List.getLast?_append] at hi
    simp at hi
    subst hi
    rfl
  · simp only [branchIdx] at hj
    cases hx : fr.get x with
    | ok v =>
      rw [hx] at hj
      simp only [Clif.Res.bind] at hj
      cases hj
      have hreg : fr.regs x = some v := by
        simp only [Clif.Frame.get, Clif.Res.ofOption] at hx
        split at hx <;> simp_all
      obtain ⟨hus, hrun⟩ := hsem fr ρ v hvh hdfg hreg
      obtain ⟨ρ1, w1, h1, hw1, hhs, hidx⟩ := hrun w
      have hs : ispec (.jtSequence d ts (.vreg r .int) (.vreg a .int) (.vreg b .int)) [ρ1 r] w1 =
          some ([ofX 0, ofX 0], w1,
            .goto (if v.toNat < tbl.length then v.toNat + 1 else 0)) := by
        simp only [ispec, hhs, hidx, hlen]
        by_cases hlt : v.toNat < tbl.length
        · have : ¬ tbl.length ≤ v.toNat := by omega
          simp [hlt, this]
        · have : tbl.length ≤ v.toNat := by omega
          simp [hlt, this]
      obtain ⟨w2, h2, hw2⟩ := seqRun_one_stop hR (operands_jtSeq d ts r a b) (ρ := ρ1)
        (by split <;> simp) hs rfl
      refine ⟨hus, _, _, _, _, _, _, _, seqRun_append_fall_stop isem h1 h2, by simp, ?_⟩
      exact hMR _ _ _ _ ((SameWorld.nf hw2).trans hw1) hmr
    | trap c => rw [hx] at hj; simp [Clif.Res.bind] at hj
    | stuck m => rw [hx] at hj; simp [Clif.Res.bind] at hj

/-! ## The terms -/

section
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)

include hp hc in
theorem emit_island_ok {n : Nat} (hn : 30 ≤ n) {k : V} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 46 669 [k] s v s') :
    s'.1 = s.1 ∧ v = .data 46 0 [.data 58 136 [k]] := by
  isel_split hp hc h 669
  brif_inv [*, rule_inst_5443] at hm he

include hp hc in
theorem jt_sequence_ok {n : Nat} (hn : 30 ≤ n) {r d ts : V} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 49 662 [r, d, ts] s v s') :
    s'.1 = ((s.1.fresh .int).2.fresh .int).2 ∧
      v = .data 49 0 [.data 58 128 [d, ts, r, .reg (s.1.fresh .int).1,
        .reg ((s.1.fresh .int).2.fresh .int).1]] := by
  isel_split hp hc h 662
  brif_inv [*, rule_inst_5394, ctor_temp_writable_reg_i64', ctor_writable_reg_to_reg'] at hm he

end

/-- What `br_table_impl n ridx default targets` did: code `ms0` (the bound check: `cmp` of
`ridx` with `n`, after loading `n` if it is no `imm12`) setting `hs` iff `n ≤` the low 32 bits
of `ridx`, then the `jt_sequence` with two fresh temporaries. -/
def JtOut (F : BitVec 64 → Prop) (isem : Sem) (st st' : LState) (n r : Nat) (d : Label)
    (ts : List Label) : Prop :=
  ∃ ms0 st2 t1 t2, Frag st st2 ms0 ∧
    st' = st2.emit (.jtSequence d ts (.vreg r .int) (.vreg t1 .int) (.vreg t2 .int)) ∧
    (st.nextVreg ≤ t1 ∧ t1 < st2.nextVreg) ∧ (st.nextVreg ≤ t2 ∧ t2 < st2.nextVreg) ∧
    (∀ m ∈ ms0, ∀ u ∈ vuseNums m, st.nextVreg ≤ u ∨ u = r) ∧
    ∀ ρ w, Runs F isem ms0 ρ w (fun ρ1 w1 => ρ1 r = ρ r ∧
      Arm.ConditionHolds Cond.hs.bits w1 = decide (n ≤ ((lo64 (ρ r)).setWidth 32).toNat))

theorem Frag.fresh2 (s : LState) : Frag s ((s.fresh .int).2.fresh .int).2 [] :=
  ⟨by simp [LState.fresh], by simp [LState.fresh]; omega, by simp⟩

theorem imm12_value {k : Nat} (hk : k < 2 ^ 32) {imm : Imm12} (h : Imm12.ofNat? k = some imm) :
    imm.bits < 4096 ∧ imm.value = k := by
  unfold Imm12.ofNat? at h
  have hm : mask64 k = k := by unfold mask64; omega
  rw [hm] at h
  simp only at h
  split at h
  · cases h; simp [Imm12.value]; omega
  · split at h
    · cases h
      rename_i h2
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h2
      simp [Imm12.value]; omega
    · cases h

theorem ofV_jtSeq (d : Label) (ts : List Label) (r a b : Reg) :
    MInst.ofV (.data 58 128 [.label d, .labels ts, .reg r, .reg a, .reg b]) =
      some (.jtSequence d ts r a b) := rfl

theorem u64_natCast {k : Nat} (hk : k < 2 ^ 64) : u64 (k : Int) = k := by
  unfold u64; omega

theorem ispec_cmpImm32 (r : Nat) {imm : Imm12} (hb : imm.bits < 4096) (a : CV) (w : Arm.ArmState) :
    ispec (.aluRRImm12 .subS .size32 .xzr (.vreg r .int) imm) [a] w =
      some ([], Arm.write_pstate (cmpFlags (opnd .size32 a) (BitVec.ofNat 32 imm.value)) w, .next) := by
  simp [ispec, hb, defOut, cmpFlags]
  rfl

theorem ispec_cmpRR32 (r q : Nat) (a b : CV) (w : Arm.ArmState) :
    ispec (.aluRRR .subS .size32 .xzr (.vreg r .int) (.vreg q .int)) [a, b] w =
      some ([], Arm.write_pstate (cmpFlags (opnd .size32 a) (opnd .size32 b)) w, .next) := by
  simp [ispec, defOut, cmpFlags]

theorem jtOut_imm12 {F : BitVec 64 → Prop} {isem : Sem} (hR : Refines F isem) {k r : Nat}
    {d : Label} {ts : List Label} {s0 : LState} {imm : Imm12} (hk : k < 2 ^ 32) (hr : r < s0.nextVreg)
    (himm : Imm12.ofNat? k = some imm) :
    JtOut F isem s0 ((((s0.fresh .int).2.fresh .int).2.emit
        (.aluRRImm12 .subS .size32 .xzr (.vreg r .int) imm)).emit
      (.jtSequence d ts (.vreg r .int) (s0.fresh .int).1 ((s0.fresh .int).2.fresh .int).1)) k r d ts := by
  obtain ⟨hb, hval⟩ := imm12_value hk himm
  have hF : Frag s0 ((((s0.fresh .int).2.fresh .int).2).emit
        (.aluRRImm12 .subS .size32 .xzr (.vreg r .int) imm)) [.aluRRImm12 .subS .size32 .xzr (.vreg r .int) imm] := by
    have := (Frag.fresh2 s0).append (Frag.emit_nodef _ (m := .aluRRImm12 .subS .size32 .xzr (.vreg r .int) imm) rfl)
    rwa [List.nil_append] at this
  refine ⟨_, _, s0.nextVreg, s0.nextVreg + 1, hF, rfl, ⟨Nat.le_refl _, ?_⟩, ⟨by omega, ?_⟩, ?_, ?_⟩
  · simp only [LState.emit, LState.fresh]; omega
  · simp only [LState.emit, LState.fresh]; omega
  · intro m hm u hu
    simp only [List.mem_singleton] at hm
    subst hm
    right
    rw [vuseNums_cmpImm] at hu
    simpa using hu
  · intro ρ w
    refine (Runs.flags hR ⟨_, rfl, rfl, fun w => ispec_cmpImm32 r hb (ρ r) w⟩ w).imp ?_
    rintro ρ1 w1 - ⟨rfl, hcond⟩
    refine ⟨rfl, ?_⟩
    rw [hcond]
    refine (hs_cmp32 (opnd .size32 (ρ1 r)) (BitVec.ofNat 32 imm.value)).trans ?_
    rw [hval]
    have : (BitVec.ofNat 32 k).toNat = k := by simp; omega
    rw [this]; rfl

theorem jtOut_reg {F : BitVec 64 → Prop} {isem : Sem} (hR : Refines F isem) {k r dd : Nat}
    {d : Label} {ts : List Label} {s0 s2 : LState} (hk : k < 2 ^ 32) (hr : r < s0.nextVreg)
    (hI : ImmOut F isem 64 1 (u64 (k : Int)) s0 s2 (.reg (.vreg dd .int))) :
    JtOut F isem s0 ((((s2.fresh .int).2.fresh .int).2.emit
        (.aluRRR .subS .size32 .xzr (.vreg r .int) (.vreg dd .int))).emit
      (.jtSequence d ts (.vreg r .int) (s2.fresh .int).1 ((s2.fresh .int).2.fresh .int).1)) k r d ts := by
  obtain ⟨ms, dd', hv, hsh, hrun⟩ := hI
  cases hv
  have hF : Frag s0 ((((s2.fresh .int).2.fresh .int).2).emit
        (.aluRRR .subS .size32 .xzr (.vreg r .int) (.vreg dd .int)))
      (ms ++ [.aluRRR .subS .size32 .xzr (.vreg r .int) (.vreg dd .int)]) := by
    have := ((⟨hsh.emitted, hsh.mono, hsh.defs⟩ : Frag s0 s2 ms).append (Frag.fresh2 s2)).append
      (Frag.emit_nodef _ (m := .aluRRR .subS .size32 .xzr (.vreg r .int) (.vreg dd .int)) rfl)
    rwa [List.append_nil] at this
  have hmono := hsh.mono
  have hres := hsh.res
  refine ⟨_, _, s2.nextVreg, s2.nextVreg + 1, hF, rfl, ⟨hmono, ?_⟩, ⟨by omega, ?_⟩, ?_, ?_⟩
  · simp only [LState.emit, LState.fresh]; omega
  · simp only [LState.emit, LState.fresh]; omega
  · intro m hm u hu
    rcases List.mem_append.1 hm with hm | hm
    · rcases hsh.uses m hm u hu with h | h
      · exact .inl h
      · exact .inl (by omega)
    · simp only [List.mem_singleton] at hm
      subst hm
      rw [vuseNums_cmpRR] at hu
      have : u = r ∨ u = dd := by simpa using hu
      rcases this with rfl | rfl
      · exact .inr rfl
      · exact .inl hres
  · intro ρ w
    obtain ⟨ρ', X, hpr, hx, hX, -⟩ := hrun ρ
    have hfr : ρ' r = ρ r := by
      obtain ⟨w', hr', -⟩ := hpr w
      exact seqRun_frame isem hr' r fun m hm hd => by have := hsh.defs m hm r hd; omega
    refine Runs.append (P := fun ρ1 _ => ρ1 = ρ') (by
      obtain ⟨w', hr', hw⟩ := hpr w
      exact ⟨ρ', w', hr', SameWorld.nf hw, rfl⟩) ?_
    rintro ρ1 w1 h1
    rw [h1]
    refine (Runs.flags hR ⟨_, rfl, rfl, fun w => ispec_cmpRR32 r dd (ρ' r) (ρ' dd) w⟩ w1).imp ?_
    rintro ρ2 w2 - ⟨h2, hcond⟩
    refine ⟨by rw [h2]; exact hfr, ?_⟩
    rw [hcond]
    refine (hs_cmp32 (opnd .size32 (ρ' r)) (opnd .size32 (ρ' dd))).trans ?_
    rw [hfr]
    have hk64 : u64 (k : Int) = k := u64_natCast (by omega)
    rw [hk64] at hX
    have : (opnd .size32 (ρ' dd)).toNat = k := by
      simp only [opnd, hx, OperandSize.bits]
      simp; omega
    simp only [opnd, OperandSize.bits] at this ⊢
    simp only [this]

section
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)

include hp hc in
theorem imm64_ok {F : BitVec 64 → Prop} {isem : Sem} (hR : Refines F isem) {n : Nat} (hn : 40 ≤ n)
    {k : Int} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 553 [.ty (.int 64), .data 122 1 [], .int k] s v s') :
    ImmOut F isem 64 1 (u64 k) s.1 s'.1 v := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 39 := ⟨n - 39, by omega⟩
  exact imm_ok hp ctx hc hR (.inr (.inr (.inr rfl))) (.inr rfl) (n := n') h

set_option maxHeartbeats 4000000 in
include hp hc in
theorem br_table_impl_ok {F : BitVec 64 → Prop} {isem : Sem} (hR : Refines F isem) {n : Nat}
    (hn : 300 ≤ n) {k r : Nat} {d : Label} {ts : List Label} {s s' : LState × Array RuleId} {v : V}
    (hk : k < 2 ^ 32) (hr : r < s.1.nextVreg)
    (h : ApplyInternal p (sem ctx) cfg n 13 670 [.int k, .reg (.vreg r .int), .label d, .labels ts]
      s v s') :
    JtOut F isem s.1 s'.1 k r d ts := by
  have kJ := fun n (hn : 30 ≤ n) r d ts s v s' h => jt_sequence_ok hp (ctx := ctx) hc (n := n)
    (r := r) (d := d) (ts := ts) (s := s) (v := v) (s' := s') hn h
  have kW := fun n (hn : 40 ≤ n) mi ci s v s' h => with_flags_side_effect_ok hp (ctx := ctx) hc
    (n := n) (mi := mi) (ci := ci) (s := s) (v := v) (s' := s') hn h
  have kE2 := fun n (hn : 30 ≤ n) i j s v s' h => emit_side_effect_inst2_ok hp (ctx := ctx) hc
    (n := n) (i := i) (j := j) (s := s) (v := v) (s' := s') hn h
  have kCI := fun n (hn : 30 ≤ n) a b c s v s' h => cmp_imm_ok hp (ctx := ctx) hc (n := n)
    (a := a) (b := b) (c := c) (s := s) (v := v) (s' := s') hn h
  have kC := fun n (hn : 30 ≤ n) a b c s v s' h => cmp_ok hp (ctx := ctx) hc (n := n)
    (a := a) (b := b) (c := c) (s := s) (v := v) (s' := s') hn h
  have hp' := hp
  isel_split hp hc h 670
  · brif_inv [*, rule_inst_5450, ext_imm12_from_u64_iff] at hm he
    obtain ⟨himm⟩ : Nonempty (Imm12.ofNat? (u64 k) = some _) := ⟨‹_›⟩
    rw [u64_natCast (by omega)] at himm
    have h391 := ‹ApplyInternal _ _ _ _ 47 391 _ _ _ _›
    obtain ⟨hs1, rfl⟩ := kCI _ (by omega) _ _ _ _ _ _ h391
    have h662 := ‹ApplyInternal _ _ _ _ 49 662 _ _ _ _›
    obtain ⟨hs2, rfl⟩ := kJ _ (by omega) _ _ _ _ _ _ h662
    have h256 := ‹ApplyInternal _ _ _ _ 46 256 _ _ _ _›
    obtain ⟨hs3, rfl⟩ := kW _ (by omega) _ _ _ _ _ h256
    have h242 := ‹ApplyInternal _ _ _ _ 13 242 _ _ _ _›
    obtain ⟨m1, m2, hs4, hm1, hm2⟩ := kE2 _ (by omega) _ _ _ _ _ h242
    rw [ofV_cmpImm32] at hm1
    rw [ofV_jtSeq] at hm2
    cases hm1; cases hm2
    simp only at hs1 hs2 hs3 hs4
    rw [hs4, hs3, hs2, hs1]
    exact jtOut_imm12 hR hk hr himm
  · brif_inv [*, rule_inst_5454] at hm he
    have hA := ‹ApplyInternal _ _ _ _ 27 553 _ _ _ _›
    obtain ⟨ms, dd, rfl, hsh, hrun⟩ := imm64_ok hp' hc hR (by omega) hA
    have h390 := ‹ApplyInternal _ _ _ _ 47 390 _ _ _ _›
    obtain ⟨hs1, rfl⟩ := kC _ (by omega) _ _ _ _ _ _ h390
    have h662 := ‹ApplyInternal _ _ _ _ 49 662 _ _ _ _›
    obtain ⟨hs2, rfl⟩ := kJ _ (by omega) _ _ _ _ _ _ h662
    have h256 := ‹ApplyInternal _ _ _ _ 46 256 _ _ _ _›
    obtain ⟨hs3, rfl⟩ := kW _ (by omega) _ _ _ _ _ h256
    have h242 := ‹ApplyInternal _ _ _ _ 13 242 _ _ _ _›
    obtain ⟨m1, m2, hs4, hm1, hm2⟩ := kE2 _ (by omega) _ _ _ _ _ h242
    rw [ofV_cmpRR32] at hm1
    rw [ofV_jtSeq] at hm2
    cases hm1; cases hm2
    simp only at hs1 hs2 hs3 hs4
    rw [hs4, hs3, hs2, hs1]
    exact jtOut_reg hR hk hr ⟨ms, dd, rfl, hsh, hrun⟩

end

end Backend.Proof
