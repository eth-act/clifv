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

/-! ## Rule 1140 -/

section
variable {ctx : Ctx}

theorem ext_jump_table_targets_iff (st : LState) (ls : List Label) (fs : List V) :
    externExtract ctx T.jump_table_targets (.labels ls) st = .ok fs ↔
      ∃ d ts, ls = d :: ts ∧ fs = [.label d, .labels ts] := by
  match ls with
  | [] =>
    have : externExtract ctx T.jump_table_targets (.labels []) st = .fail := rfl
    rw [this]; simp
  | d :: ts =>
    have : externExtract ctx T.jump_table_targets (.labels (d :: ts)) st =
      .ok [.label d, .labels ts] := rfl
    rw [this]
    simp only [ExtResult.ok.injEq, List.cons.injEq]
    constructor
    · rintro rfl; exact ⟨d, ts, ⟨rfl, rfl⟩, rfl⟩
    · rintro ⟨d', ts', ⟨rfl, rfl⟩, rfl⟩; rfl

theorem ctor_jump_table_size_iff (st : LState) (ls : List Label) (v : V) (st' : LState) :
    externCtor ctx T.jump_table_size [.labels ls] st = .ok (v, st') ↔
      v = .int ls.length ∧ st' = st := by
  have : externCtor ctx T.jump_table_size [.labels ls] st = .ok (.int ls.length, st) := rfl
  rw [this]; simp [eq_comm]

theorem ctor_targets_jt_space_iff (st : LState) (ls : List Label) (v : V) (st' : LState) :
    externCtor ctx T.targets_jt_space [.labels ls] st = .ok (v, st') ↔
      v = .int (4 * (8 + ls.length)) ∧ st' = st := by
  have : externCtor ctx T.targets_jt_space [.labels ls] st =
    .ok (.int (4 * (8 + ls.length)), st) := rfl
  rw [this]; simp [eq_comm]

theorem ofV_emitIsland (k : Nat) : MInst.ofV (.data 58 136 [.int (k : Int)]) = some (.emitIsland k) :=
  rfl

theorem vuseNums_jtSeq (d : Label) (ts : List Label) (r a b : Nat) :
    vuseNums (MInst.jtSequence d ts (.vreg r .int) (.vreg a .int) (.vreg b .int)) = [r] := rfl

theorem ctor_u32_into_u64_iff (st : LState) (a : Int) (v : V) (st' : LState) :
    externCtor ctx T.u32_into_u64 [.int a] st = .ok (v, st') ↔ v = .int a ∧ st' = st := by
  have : externCtor ctx T.u32_into_u64 [.int a] st = .ok (.int a, st) := rfl
  rw [this]; simp [eq_comm]

end

set_option maxHeartbeats 8000000 in
theorem brTable_ruleOk {p : Program} (hp : Data p) {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT}
    (hR : Refines F isem) (hMR : MRStable F MR) : BranchRuleOk isem MR p rule_lower_3277 := by
  intro f ctx hctx ti t data targets hd hi hbt htl cfg hc m n st tr env' s1 out st' tr' hm hn hvb _
    hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 400 := ⟨n - 400, by omega⟩
  have kS := fun n (hn : 60 ≤ n) i s v s' h => side_effect_inst_ok hp (ctx := ctx) hc (n := n)
    (i := i) (s := s) (v := v) (s' := s') hn h
  have kI := fun n (hn : 30 ≤ n) k s v s' h => emit_island_ok hp (ctx := ctx) hc (n := n)
    (k := k) (s := s) (v := v) (s' := s') hn h
  have kZ := fun n (hn : 40 ≤ n) x s v s' h => zext32_ok hp (ctx := ctx) hc (n := n)
    (x := x) (s := s) (v := v) (s' := s') hn h
  have kB := fun n (hn : 300 ≤ n) k r d ts s v s' hk hr h => br_table_impl_ok hp (ctx := ctx) hc hR
    (n := n) (k := k) (r := r) (d := d) (ts := ts) (s := s) (v := v) (s' := s') hn hk hr h
  have hf := ruleFmt_term hp (r := rule_lower_3277) rfl hp.t2451 term_2451_kind hd hi hmatch
  cases t with
  | brTable x dc tbl =>
    rw [termData_brTable] at hd; cases hd
    cases hp
    brif_inv [*, rule_lower_3277, ext_jump_table_targets_iff, ctor_jump_table_size_iff,
      ctor_targets_jt_space_iff, ctor_u32_into_u64_iff] at hmatch heval
    simp only [hi, Option.some.injEq] at *
    isel_destruct; subst_vars
    repeat (isel_inv_simp [ext_jump_table_targets_iff, ctor_jump_table_size_iff,
      ctor_targets_jt_space_iff, ctor_u32_into_u64_iff] at * <;> isel_destruct <;> subst_vars)
    rename LState => st
    obtain ⟨⟨wx, hwx, hTx⟩, htbl⟩ := hbt _ _ _ rfl
    have hlen := htl _ _ _ rfl
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    have h669 := ‹ApplyInternal _ _ _ _ 46 669 _ _ _ _›
    obtain ⟨hs1, rfl⟩ := kI _ (by omega) _ _ _ _ h669
    have h243 := ‹ApplyInternal _ _ _ _ 25 243 _ _ _ _›
    obtain ⟨mi, hmi, hs2, -⟩ := kS _ (by omega) _ _ _ _ h243
    rw [show ∀ n : Nat, (4 * (8 + (n : Int))) = ((4 * (8 + n) : Nat) : Int) from
      fun n => by push_cast; omega, ofV_emitIsland] at hmi
    cases hmi
    have h556 := ‹ApplyInternal _ _ _ _ 27 556 _ _ _ _›
    have hext := kZ _ (by omega) _ _ _ _ h556
    rw [hs2, hs1] at hext
    obtain ⟨k, msx, rfl, hFx, hkl, hkx, hxsem⟩ := ExtOut.sem hR hctx (pass := [.int 32, .int 64]) (by exact hvb) (.inl rfl)
      (by simp) (fun _ => by simp) hext
    have h670 := ‹ApplyInternal _ _ _ _ 13 670 _ _ _ _›
    have hJ := kB _ (by omega) _ _ _ _ _ _ _ (by omega) hkl h670
    simp only at hJ
    obtain ⟨ms0, st2, t1, t2, hF0, rfl, ht1, ht2, hu0, hr0⟩ := hJ
    have hFall := ((Frag.emit_nodef _ (m := .emitIsland _) rfl).append hFx).append hF0
    have hm1 := hFx.mono
    have hm0 := hF0.mono
    refine ⟨_, ?emit, brTable_termOk_gen hR hMR hFall (by dsimp only [LState.emit] at hm1 ht1 ⊢; omega)
      (by dsimp only [LState.emit] at hm1 ht2 ⊢; omega) hlen fun fr ρ v hvh hdfg hreg => ?_⟩
    case emit => simp [LState.emit, hFall.emitted]
    obtain ⟨hux, hrx⟩ := hxsem fr ρ v (hvh _ _ hreg) hdfg hreg
    have hkok : st.nextVreg ≤ k ∨ (fr.regs k).isSome := by
      rcases hkx with h | rfl
      · exact .inl (by dsimp only [LState.emit] at h ⊢; exact h)
      · exact .inr (by simp [hreg])
    refine ⟨?_, fun w => ?_⟩
    · intro mm hmm u hu
      simp only [List.append_assoc, List.mem_append, List.mem_singleton] at hmm
      rcases hmm with rfl | hmm | hmm | rfl
      · simp [vuseNums, operands_emitIsland] at hu
      · exact hux mm hmm u hu
      · rcases hu0 mm hmm u hu with h | rfl
        · exact .inl (by dsimp only [LState.emit] at hm1 hm0 h ⊢; omega)
        · exact hkok
      · rw [vuseNums_jtSeq, List.mem_singleton] at hu
        subst hu; exact hkok
    · have hty := hdfg.2 x _ v hTx hreg
      have hvw : v.ty.width = wx := by rw [← ofClif_bits, hty]; rfl
      rw [List.append_assoc]
      refine Runs.append (P := fun ρ1 _ => ρ1 = ρ)
        (Runs.one hR (operands_emitIsland _) (by rfl) rfl (SameWorldNF.refl F w)
          fun _ _ => vdefUpd_nil _ _) ?_
      rintro ρ1 w1 rfl
      refine Runs.append (hrx w1) ?_
      rintro ρ2 w2 ⟨-, hex⟩
      refine (hr0 ρ2 w2).imp ?_
      rintro ρ3 w3 - ⟨h3, hhs⟩
      have hx32 := hex (by omega)
      simp only [Bool.false_eq_true, ↓reduceIte] at hx32
      have hv : ((lo64 (ρ2 k)).setWidth 32).toNat = v.toNat := by
        rw [hx32, BitVec.toNat_setWidth, Nat.mod_eq_of_lt]
        · rfl
        · exact Nat.lt_of_lt_of_le v.bits.isLt (Nat.pow_le_pow_right (by omega) (by omega))
      refine ⟨by rw [hhs, hv, hlen], by rw [h3, hv]⟩
  | _ => simp [termFmt] at hf

end Backend.Proof
