import FV.Backend.Proof.IselCtlBrif
import FV.Backend.Proof.IselFamALUAMul
import FV.Backend.Proof.IselFamALUALogic

/-!
# Family Ctl: `tbnz` / `tbz` (`lower_branch` rules 1137, 1138)

`brif (band x (iconst 2^k))` → `tbnz x, #k`; `brif (icmp eq (band x (iconst 2^k)) (iconst 0))` →
`tbz x, #k` (`test_and_compare_bit_const`: `n` has exactly one set bit, below the type's width).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-- `test_and_compare_bit_const ty n`. -/
def tcbc (ty : CTy) (n : Int) : Option Nat :=
  match (List.range 64).filter ((u64 n).testBit ·) with
  | [bit] => if bit < ty.bits then some bit else none
  | _ => none

theorem ctor_tcbc_iff {ctx : Ctx} (st : LState) (ty : CTy) (n : Int) (v : V) (st' : LState) :
    externCtor ctx T.test_and_compare_bit_const [.ty ty, .int n] st = .ok (v, st') ↔
      ∃ bit, tcbc ty n = some bit ∧ v = .int bit ∧ st' = st := by
  have : externCtor ctx T.test_and_compare_bit_const [.ty ty, .int n] st =
      match tcbc ty n with
      | some b => .ok (.int b, st)
      | none => .fail := by
    simp only [tcbc]
    show (match (List.range 64).filter ((u64 n).testBit ·) with
      | [bit] => if bit < ty.bits then _ else _
      | _ => _) = _
    split
    · split <;> rfl
    · rfl
  rw [this]
  cases tcbc ty n <;> simp [eq_comm]

theorem truthy_and_pow {w : Nat} (u imm : BitVec w) (bit : Nat) (hb : bit < w) (himm : imm.toNat = 2 ^ bit) :
    Clif.Sem.truthy (u &&& imm) = u.getLsbD bit := by
  have hlt : 2 ^ bit < 2 ^ w := Nat.pow_lt_pow_right (by omega) hb
  have : imm = BitVec.twoPow w bit := by
    apply BitVec.eq_of_toNat_eq
    rw [himm, BitVec.toNat_twoPow, Nat.mod_eq_of_lt hlt]
  subst this
  rw [BitVec.and_twoPow]
  split
  · rename_i h
    have hne : BitVec.twoPow w bit ≠ 0#w := by
      intro h0
      have := congrArg BitVec.toNat h0
      rw [BitVec.toNat_twoPow, Nat.mod_eq_of_lt hlt] at this
      simp at this
    simp [Clif.Sem.truthy, hne, h]
  · simp_all [Clif.Sem.truthy]

theorem u64_lt_ctl (n : Int) : u64 n < 2 ^ 64 := by
  unfold u64; omega

theorem pow_of_ones {m bit : Nat} (hm : m < 2 ^ 64)
    (h : (List.range 64).filter (m.testBit ·) = [bit]) : m = 2 ^ bit ∧ bit < 64 := by
  have hmem : ∀ i, i < 64 → (m.testBit i = true ↔ i = bit) := by
    intro i hi
    have : i ∈ (List.range 64).filter (m.testBit ·) ↔ i ∈ [bit] := by rw [h]
    simpa [hi] using this
  have hb : bit < 64 := by
    have : bit ∈ (List.range 64).filter (m.testBit ·) := by rw [h]; simp
    simpa using (List.mem_filter.mp this).1
  refine ⟨Nat.eq_of_testBit_eq fun i => ?_, hb⟩
  rw [Nat.testBit_two_pow]
  by_cases hi : i < 64
  · have := hmem i hi
    by_cases e : i = bit
    · subst e; simp [this.mpr rfl]
    · have : m.testBit i = false := by simpa [e] using this
      simp [this, Ne.symm e]
  · have h1 : m.testBit i = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by omega) (by omega)))
    rw [h1]; simp; omega

theorem tcbc_spec {ty : CTy} {n : Int} {bit : Nat} (h : tcbc ty n = some bit) :
    u64 n = 2 ^ bit ∧ bit < ty.bits := by
  unfold tcbc at h
  split at h
  · rename_i b hf
    split at h
    · cases h; exact ⟨(pow_of_ones (u64_lt_ctl n) hf).1, ‹_›⟩
    · cases h
  · cases h

theorem ofClif_bits_ctl (ty : Clif.Ty) : (CTy.ofClif ty).bits = ty.width := by
  cases ty <;> rfl

theorem operands_tbb (k : TestBitAndBranchKind) (a b : Label) (n bit : Nat) :
    (MInst.testBitAndBranch k a b (.vreg n .int) bit).operands =
      .ok #[⟨n, .int, .use, .early, .reg⟩] := rfl

theorem getLsbD_lo64 {w : Nat} (x : CV) {bit : Nat} (hb : bit < w) (hw : w ≤ 64) :
    (lo64 x).getLsbD bit = (x.setWidth w).getLsbD bit := by
  have : bit < 64 := by omega
  simp [lo64, BitVec.getLsbD_setWidth, this, hb]

/-- The test-bit branch lowering: `x` is `band a b` with `b = iconst 2^bit`, branch on bit `bit`
of `a` (`tbnz`: taken when set; `tbz`, on `x = icmp eq (band a b) 0` handled separately). -/
theorem tbnz_termOk {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT} (hR : Refines F isem)
    (hMR : MRStable F MR) {ctx : Ctx} {x j1 j2 a b bit : Nat} {info1 info2 : IInfo}
    {ty1 ty2 : Clif.Ty} {imm : BitVec ty2.width} {t : CTy}
    (hj1 : ctx.defInst? x = some j1) (hi1 : ctx.insts[j1]? = some info1)
    (hcl1 : info1.clif = some (.binary .band ty1 a b))
    (hj2 : ctx.defInst? b = some j2) (hi2 : ctx.insts[j2]? = some info2)
    (hcl2 : info2.clif = some (.iconst ty2 imm)) (he2 : eTy ty2 = true)
    (hta : ctx.valueType? a = some t)
    (htc : tcbc t ((u64 (imm64OfIconst ty2 imm) : Nat) : Int) = some bit)
    {st : LState} {la lb : Label} {tb eb : Clif.BlockCall} :
    LowerTermOk isem MR ctx (.brif x tb eb) [la, lb] st
      (st.emit (.testBitAndBranch .nz la lb (.vreg a .int) bit))
      [.testBitAndBranch .nz la lb (.vreg a .int) bit] := by
  have hd : vdefs (.testBitAndBranch .nz la lb (.vreg a .int) bit) = [] := rfl
  have hf2 := Frag.emit_nodef st hd
  refine ⟨hf2.mono, hf2.defs, ?_⟩
  intro fr cm ρ w _ hvh hdfg hmr
  refine ⟨fun i hi => ?_, fun j hj => ?_⟩
  · simp at hi; subst hi; rfl
  simp only [branchIdx] at hj
  cases hx : fr.get x with
  | trap c => rw [hx] at hj; simp [Clif.Res.bind] at hj
  | stuck m => rw [hx] at hj; simp [Clif.Res.bind] at hj
  | ok vc =>
    rw [hx] at hj
    simp only [Clif.Res.bind] at hj
    cases hj
    have hreg : fr.regs x = some vc := by
      simp only [Clif.Frame.get, Clif.Res.ofOption] at hx
      split at hx <;> simp_all
    obtain ⟨vals, hev, hl⟩ := hdfg.1 x j1 info1 _ vc hj1 hi1 hcl1 rfl hreg
    obtain ⟨u, v2, ha, hb, rfl⟩ := evalInst_binary_inv rfl (hev default)
    have hvc := lookup_zip_single hl
    subst hvc
    have hbv := iconst_val hdfg hj2 hi2 hcl2 (getAs_ok hb)
    cases hbv
    have hra := getAs_ok ha
    have htt := hdfg.2 a t _ hta hra
    subst htt
    obtain ⟨hpow, hbit⟩ := tcbc_spec htc
    rw [ofClif_bits_ctl] at hbit
    rw [u64_iconst he2] at hpow
    have hw := eTy_width he2
    have hholds : (ρ a).setWidth ty1.width = u := hvh a _ hra
    have hs : ispec (.testBitAndBranch .nz la lb (.vreg a .int) bit) [ρ a] w =
        some ([], w, .goto (if Clif.Sem.truthy (Clif.Sem.binary .band u v2) then 0 else 1)) := by
      simp only [ispec, Clif.Sem.binary, Clif.Sem.band, truthy_and_pow u v2 bit hbit hpow,
        getLsbD_lo64 (ρ a) hbit hw, hholds]
      cases u.getLsbD bit <;> rfl
    obtain ⟨w2, h2, hw2⟩ := seqRun_one_stop hR (operands_tbb .nz la lb a bit) (ρ := ρ) (by simp) hs
      rfl
    refine ⟨?_, _, _, _, _, _, _, _, h2, rfl, hMR _ _ _ _ (SameWorld.nf hw2) hmr⟩
    intro m hm u' hu
    simp only [List.mem_singleton] at hm
    subst hm
    have : u' = a := by simpa [vuseNums, operands_tbb, Operand.isUse] using hu
    subst this
    exact .inr (by rw [hra]; rfl)


theorem ofV_tbb_nz (a b : Label) (r : Reg) (bit : Nat) :
    MInst.ofV (.data 58 119 [.data 94 1 [], .label a, .label b, .reg r, .int bit]) =
      some (.testBitAndBranch .nz a b r bit) := rfl

theorem ofV_tbb_z (a b : Label) (r : Reg) (bit : Nat) :
    MInst.ofV (.data 58 119 [.data 94 0 [], .label a, .label b, .reg r, .int bit]) =
      some (.testBitAndBranch .z a b r bit) := rfl

section
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)

include hp hc in
theorem tbb_ok {n : Nat} (hn : 30 ≤ n) {k a b r bit : V} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 46 666 [k, a, b, r, bit] s v s') :
    s'.1 = s.1 ∧ v = .data 46 0 [.data 58 119 [k, a, b, r, bit]] := by
  isel_split hp hc h 666
  brif_inv [*, rule_inst_5425] at hm he

include hp hc in
theorem tbnz_inst_ok {n : Nat} (hn : 60 ≤ n) {a b r bit : V} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 46 667 [a, b, r, bit] s v s') :
    s'.1 = s.1 ∧ v = .data 46 0 [.data 58 119 [.data 94 1 [], a, b, r, bit]] := by
  have k := fun n (hn : 30 ≤ n) k a b r bit s v s' h => tbb_ok hp (ctx := ctx) hc (n := n) (k := k)
    (a := a) (b := b) (r := r) (bit := bit) (s := s) (v := v) (s' := s') hn h
  isel_split hp hc h 667
  brif_inv [*, rule_inst_5431] at hm he
  have h666 := ‹ApplyInternal _ _ _ _ 46 666 _ _ _ _›
  obtain ⟨hs, rfl⟩ := k _ (by omega) _ _ _ _ _ _ _ _ h666
  exact ⟨hs, rfl⟩

include hp hc in
theorem tbz_inst_ok {n : Nat} (hn : 60 ≤ n) {a b r bit : V} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 46 668 [a, b, r, bit] s v s') :
    s'.1 = s.1 ∧ v = .data 46 0 [.data 58 119 [.data 94 0 [], a, b, r, bit]] := by
  have k := fun n (hn : 30 ≤ n) k a b r bit s v s' h => tbb_ok hp (ctx := ctx) hc (n := n) (k := k)
    (a := a) (b := b) (r := r) (bit := bit) (s := s) (v := v) (s' := s') hn h
  isel_split hp hc h 668
  brif_inv [*, rule_inst_5437] at hm he
  have h666 := ‹ApplyInternal _ _ _ _ 46 666 _ _ _ _›
  obtain ⟨hs, rfl⟩ := k _ (by omega) _ _ _ _ _ _ _ _ h666
  exact ⟨hs, rfl⟩

end

set_option maxHeartbeats 4000000 in
theorem tbnz_ruleOk {p : Program} (hp : Data p) {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT}
    (hR : Refines F isem) (hMR : MRStable F MR) : BranchRuleOk isem MR p rule_lower_3251 := by
  intro f ctx hctx ti t data targets hd hi _ _ cfg hc m n st tr env' s1 out st' tr' hm hn hvb _ hmatch
    heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  have kT := fun n (hn : 60 ≤ n) a b r bit s v s' h => tbnz_inst_ok hp (ctx := ctx) hc (n := n)
    (a := a) (b := b) (r := r) (bit := bit) (s := s) (v := v) (s' := s') hn h
  have kE := fun n (hn : 30 ≤ n) i s v s' h => emit_side_effect_inst_ok hp (ctx := ctx) hc (n := n)
    (i := i) (s := s) (v := v) (s' := s') hn h
  have hf := ruleFmt_term hp (r := rule_lower_3251) rfl hp.t2452 term_2452_kind hd hi hmatch
  cases t with
  | brif x tb eb =>
    rw [termData_brif] at hd; cases hd
    cases hp
    brif_inv [*, rule_lower_3251, ctor_tcbc_iff] at hmatch heval
    simp only [hi, Option.some.injEq] at *
    isel_destruct; subst_vars
    have hdat := ‹V.data 152 5 _ = _›
    simp only [V.data.injEq, List.cons.injEq, and_true, true_and] at hdat
    obtain ⟨rfl, rfl⟩ := hdat
    repeat (isel_inv_simp [ctor_tcbc_iff] at * <;> isel_destruct <;> subst_vars)
    obtain ⟨hj1⟩ : Nonempty (ctx.defInst? x = some _) := ⟨‹_›⟩
    obtain ⟨hi1⟩ : Nonempty (ctx.insts[_]? = some _) := ⟨‹ctx.insts[_]? = some _›⟩
    obtain ⟨cl1, hcl1, hdat1⟩ := ctxInv_clif hctx hj1 hi1
    obtain ⟨hd1⟩ : Nonempty (V.data 152 2 _ = _) := ⟨‹_›⟩
    rw [← hd1] at hdat1
    obtain ⟨ty1, a, b, rfl, he1, hfs1⟩ := instData_binary_inv (cop := .band) variantNames_Band rfl hdat1
    simp only [List.cons.injEq, and_true] at hfs1
    subst hfs1
    repeat (isel_inv_simp [ctor_tcbc_iff] at * <;> isel_destruct <;> subst_vars)
    obtain ⟨hj2⟩ : Nonempty (ctx.defInst? b = some _) := ⟨‹_›⟩
    obtain ⟨hd2⟩ : Nonempty (V.data 152 35 _ = _) := ⟨‹_›⟩
    obtain ⟨hi2⟩ : Nonempty (ctx.insts[_]? = some _) := ⟨‹ctx.insts[_]? = some _›⟩
    obtain ⟨ty2, imm, rfl, he2, hcl2⟩ := iconst_data_inv hctx hj2 hi2 hd2
    repeat (isel_inv_simp [ctor_tcbc_iff] at * <;> isel_destruct <;> subst_vars)
    obtain ⟨hta⟩ : Nonempty (ctx.valueType? a = some _) := ⟨‹_›⟩
    obtain ⟨htc⟩ : Nonempty (tcbc _ _ = some _) := ⟨‹_›⟩
    have hra := hctx.valueReg a _ ‹ctx.valueReg? a = some _›
    subst hra
    have h667 := ‹ApplyInternal _ _ _ _ 46 667 _ _ _ _›
    obtain ⟨hs1, rfl⟩ := kT _ (by omega) _ _ _ _ _ _ _ h667
    have h242 := ‹ApplyInternal _ _ _ _ 13 242 _ _ _ _›
    obtain ⟨mi, hmi, hs2, -⟩ := kE _ (by omega) _ _ _ _ h242
    rw [ofV_tbb_nz] at hmi
    cases hmi
    simp only at hs1 hs2
    rw [hs2, hs1]
    exact ⟨_, by simp [LState.emit], tbnz_termOk hR hMR hj1 hi1 hcl1 hj2 hi2 hcl2 he2 hta htc⟩
  | _ => simp [termFmt] at hf

end Backend.Proof
