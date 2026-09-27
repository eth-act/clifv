import FV.Backend.Proof.IselMemRun
import FV.Backend.Proof.IselTermsALUA
import FV.Backend.Proof.IselFamALUA

/-!
# Memory family (M4Mem): the address helpers

Contracts of `amode_add` (`inst.isle:4119`: a register holding `base + off`).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

variable {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config} (hc : cfg.checkOverlap = false)
variable {F : BitVec 64 → Prop} {isem : Sem}

/-- What `amode_add a y` produced: code `ms` (fresh defs, reading fresh vregs or `a`) and a
register `d` (`a` itself, or fresh) holding `a + y` (64 bits) after every run. -/
structure AddOk (F : BitVec 64 → Prop) (isem : Sem) (st st' : LState) (ms : List MInst) (a : Nat)
    (y : Int) (d : Nat) : Prop where
  frag : Frag st st' ms
  uses : ∀ m ∈ ms, ∀ u ∈ vuseNums m, st.nextVreg ≤ u ∨ u = a
  res : d = a ∨ st.nextVreg ≤ d
  run : ∀ ρ w, Runs F isem ms ρ w (fun ρ' _ => lo64 (ρ' d) = lo64 (ρ a) + BitVec.ofInt 64 y)

theorem u64_ofNat_ofInt (y : Int) : BitVec.ofNat 64 (u64 y) = BitVec.ofInt 64 y := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_ofInt, u64]
  omega

theorem lo64_resX64 (r : BitVec 64) : lo64 (resX .size64 r) = r := by
  simp only [lo64, resX, ofX, OperandSize.bits]
  rw [BitVec.setWidth_setWidth_of_le _ (by decide)]
  simp

theorem opnd64 (a : CV) : opnd .size64 a = lo64 a := by
  simp [opnd, OperandSize.bits]

theorem lo64_resX64' (r : BitVec OperandSize.size64.bits) : lo64 (resX .size64 r) = r :=
  lo64_resX64 r

theorem opnd64' (a : CV) : opnd .size64 a = (lo64 a : BitVec OperandSize.size64.bits) := opnd64 a

theorem ofNat64' (k : Nat) : (BitVec.ofNat OperandSize.size64.bits k) = (BitVec.ofNat 64 k) := rfl

theorem u64_u64 (y : Int) : u64 (u64 y : Int) = u64 y := by unfold u64; omega

include hp hc in
theorem add_imm64_inv {n : Nat} (hn : 40 ≤ n) {a : Reg} {i : Imm12} {s s' : LState × Array RuleId}
    {v : V} (h : ApplyInternal p (sem ctx) cfg n 27 433 [.ty (.int 64), .reg a, .op (.imm12 i)] s v s') :
    v = .reg (s.1.fresh .int).1 ∧
      s'.1 = (s.1.fresh .int).2.emit (.aluRRImm12 .add .size64 (s.1.fresh .int).1 a i) := by
  obtain ⟨ks, rid, hks, hsz⟩ := operand_size_run hp ctx hc (w := 64) (by decide)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 29 := ⟨n - 29, by omega⟩
  obtain ⟨st, tr⟩ := s
  have e := add_imm_run hp ctx hc st tr k hsz hks a i
  unfold ApplyInternal at h
  rw [e] at h
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨rfl, rfl⟩

include hp hc in
theorem add64_inv {n : Nat} (hn : 40 ≤ n) {a b : Reg} {s s' : LState × Array RuleId}
    {v : V} (h : ApplyInternal p (sem ctx) cfg n 27 432 [.ty (.int 64), .reg a, .reg b] s v s') :
    v = .reg (s.1.fresh .int).1 ∧
      s'.1 = (s.1.fresh .int).2.emit (.aluRRR .add .size64 (s.1.fresh .int).1 a b) := by
  obtain ⟨ks, rid, hks, hsz⟩ := operand_size_run hp ctx hc (w := 64) (by decide)
  have hks1 : ks = 1 := by
    simp only [szOf] at hks
    cases ks with
    | zero => simp [OperandSize.ofIdx?] at hks
    | succ k => cases k with
      | zero => rfl
      | succ k => simp [OperandSize.ofIdx?] at hks
  subst hks1
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 29 := ⟨n - 29, by omega⟩
  obtain ⟨st, tr⟩ := s
  have e := add_run hp ctx hc st tr k hsz (fun st rd rn rm => ctor_emit ctx st (ofV_aluRRR_add_64 rd rn rm)) a b
  unfold ApplyInternal at h
  rw [e] at h
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨rfl, rfl⟩

theorem runs_add_imm64 (hR : Refines F isem) {d a : Nat} {i : Imm12} (hi : i.bits < 4096)
    (ρ : Nat → CV) (w : Arm.ArmState) :
    Runs F isem [.aluRRImm12 .add .size64 (.vreg d .int) (.vreg a .int) i] ρ w
      (fun ρ' _ => ρ' = upd ρ d (resX .size64 (opnd .size64 (ρ a) + BitVec.ofNat _ i.value))) :=
  Runs.one hR (operands_aluRRImm12 .add .size64 d a i) (ispec_aluRRImm12_add hi) rfl
    (SameWorldNF.refl F w) (fun _ _ => rfl)

theorem runs_add64 (hR : Refines F isem) {d a b : Nat} (ρ : Nat → CV) (w : Arm.ArmState) :
    Runs F isem [.aluRRR .add .size64 (.vreg d .int) (.vreg a .int) (.vreg b .int)] ρ w
      (fun ρ' _ => ρ' = upd ρ d (resX .size64 (opnd .size64 (ρ a) + opnd .size64 (ρ b)))) :=
  Runs.one hR (operands_aluRRR .add .size64 d a b) (ispec_aluRRR (op := .add) rfl) rfl
    (SameWorldNF.refl F w) (fun _ _ => rfl)

theorem frag_one (st : LState) (m : MInst) (hd : vdefs m = [st.nextVreg]) :
    Frag st ((st.fresh .int).2.emit m) [m] := by
  refine ⟨by simp [emitted_fresh_emit], by rw [nextVreg_fresh_emit]; omega, ?_⟩
  intro m' hm d hd'
  simp only [List.mem_singleton] at hm; subst hm
  rw [hd] at hd'; simp at hd'; subst hd'; rw [nextVreg_fresh_emit]; omega

theorem addOk_imm12 (hR : Refines F isem) (st : LState) {a : Nat} {y : Int} {imm : Imm12}
    (hv : imm.value = u64 y) (hb : imm.bits < 4096) :
    AddOk F isem st ((st.fresh .int).2.emit
      (.aluRRImm12 .add .size64 (st.fresh .int).1 (.vreg a .int) imm))
      [.aluRRImm12 .add .size64 (st.fresh .int).1 (.vreg a .int) imm] a y st.nextVreg := by
  rw [fresh_fst]
  refine ⟨frag_one st _ rfl, ?_, .inr (Nat.le_refl _), fun ρ w => ?_⟩
  · intro m hm u hu
    simp only [List.mem_singleton] at hm; subst hm
    simp [vuseNums, operands_aluRRImm12, Operand.isUse] at hu
    exact .inr hu
  · refine (runs_add_imm64 hR hb ρ w).imp fun ρ' _ _ e => ?_
    subst e
    rw [upd_same, lo64_resX64', opnd64', ofNat64', hv, u64_ofNat_ofInt]; rfl

theorem ofNat_mod64 {X c : Nat} (h : X % 2 ^ 64 = c % 2 ^ 64) :
    BitVec.ofNat 64 X = BitVec.ofNat 64 c := by
  apply BitVec.eq_of_toNat_eq; simpa using h

theorem addOk_add (hR : Refines F isem) {st st2 : LState} {ms : List MInst} {a d : Nat} {y : Int}
    (hsh : CodeShape st st2 ms d st.nextVreg) (ha : a < st.nextVreg)
    (hrun : ∀ ρ, ∃ ρ' X, PRun F isem ms ρ ρ' ∧ lo64 (ρ' d) = BitVec.ofNat 64 X ∧
      X % 2 ^ 64 = u64 (u64 y : Int) % 2 ^ 64) :
    AddOk F isem st ((st2.fresh .int).2.emit
      (.aluRRR .add .size64 (st2.fresh .int).1 (.vreg a .int) (.vreg d .int)))
      (ms ++ [.aluRRR .add .size64 (st2.fresh .int).1 (.vreg a .int) (.vreg d .int)]) a y
      st2.nextVreg := by
  have hfr : Frag st st2 ms := ⟨hsh.emitted, hsh.mono, hsh.defs⟩
  rw [fresh_fst]
  refine ⟨hfr.append (frag_one st2 _ rfl), ?_, .inr hsh.mono, fun ρ w => ?_⟩
  · intro m hm u hu
    rcases List.mem_append.1 hm with hm | hm
    · rcases hsh.uses m hm u hu with h | h
      · exact .inl h
      · exact .inl (by omega)
    · simp only [List.mem_singleton] at hm; subst hm
      simp [vuseNums, operands_aluRRR, Operand.isUse] at hu
      rcases hu with rfl | rfl
      · exact .inr rfl
      · exact .inl hsh.res
  · obtain ⟨ρ1, X, hp1, hX, hXc⟩ := hrun ρ
    refine (Runs.of_prun hp1 w (P := fun ρ' _ => ρ' = ρ1) (fun _ _ => rfl)).append
      (fun ρ2 w2 e => e ▸ (runs_add64 hR ρ1 w2).imp fun ρ' _ _ e' => ?_)
    subst e'
    have hfa : ρ1 a = ρ a := hfr.frame (hp1 w).choose_spec.1 ha
    rw [upd_same, lo64_resX64', opnd64', opnd64', hX, hfa, ofNat_mod64 hXc, u64_u64,
      u64_ofNat_ofInt]; rfl

include hp hc in
theorem imm64_inv (hR : Refines F isem) {n : Nat} (hn : 40 ≤ n) {i : Int}
    {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 553 [.ty (.int 64), .data 122 1 [], .int i] s v s') :
    ImmOut F isem 64 1 (u64 i) s.1 s'.1 v := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 39 := ⟨n - 39, by omega⟩
  obtain ⟨st, tr⟩ := s
  exact imm_ok hp ctx hc hR (w := 64) (by decide) (e := 1) (by decide) (n := k) h

include hp hc in
/-- **`amode_add a y`** (all three rules): `a` itself when `y = 0`, `add_imm` when `y` is an
`imm12`, else `add` of an `imm`. -/
theorem amode_add_ok (hR : Refines F isem) {n : Nat} (hn : 100 ≤ n) {a : Nat} {y : Int}
    {s s' : LState × Array RuleId} {v : V} (ha : a < s.1.nextVreg)
    (h : ApplyInternal p (sem ctx) cfg n 27 577 [.reg (.vreg a .int), .int y] s v s') :
    ∃ d ms, v = .reg (.vreg d .int) ∧ AddOk F isem s.1 s'.1 ms a y d := by
  obtain ⟨st, tr⟩ := s
  mem_split hp hc h 577
  · mem_inv hp [] at hm he
    exact ⟨a, rfl, [], ⟨Frag.nil _, by simp, .inl rfl, fun ρ w => Runs.nil (by simp)⟩⟩
  · mem_inv hp [] at hm he
    rename_i imm himm hadd
    obtain ⟨rfl, rfl⟩ := add_imm64_inv hp ctx hc (by omega) hadd
    obtain ⟨hv, hb⟩ := imm12_ofNat_value himm (u64_lt' _)
    rw [u64_u64] at hv
    exact ⟨_, by rw [fresh_fst], _, addOk_imm12 hR _ hv hb⟩
  · mem_inv hp [] at hm he
    have h553 := ‹ApplyInternal _ _ _ _ 27 553 _ _ _ _›
    have h432 := ‹ApplyInternal _ _ _ _ 27 432 _ _ _ _›
    obtain ⟨ms, d, rfl, hsh, hrun⟩ := imm64_inv hp ctx hc hR (by omega) h553
    obtain ⟨rfl, rfl⟩ := add64_inv hp ctx hc (by omega) h432
    refine ⟨_, by rw [fresh_fst], _, addOk_add hR hsh ha fun ρ => ?_⟩
    obtain ⟨ρ', X, h1, h2, h3, -⟩ := hrun ρ
    exact ⟨ρ', X, h1, h2, h3⟩

end Backend.Proof
