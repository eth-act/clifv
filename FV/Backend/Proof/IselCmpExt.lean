import FV.Backend.Proof.IselCmpTerms

/-!
# `put_in_reg_{z,s}ext{32,64}`: syntactic contracts (flags/select/div family)

Each lemma: an internal call of the term on `[.value x]` that returned `v` either passed the
value's own register through (`$I32`/`$I64` rules) or emitted one `extend` into a fresh vreg
(the `fits_in_32` rule; for the 32-bit terms the earlier `$I32` rule failed, so the type is
narrower than 32 bits).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)

/-- What a `put_in_reg_*ext*` call on value `x` did: passed `x`'s register through (type in
`pass`), or emitted `extend fresh rx sg t.bits toB` for a type `t` of at most 32 bits (not in
`pass`). -/
def ExtOut (ctx : Ctx) (x : Nat) (sg : Bool) (toB : Nat) (pass : List CTy) (s s' : LState)
    (v : V) : Prop :=
  ∃ t, ctx.valueType? x = some t ∧ ∃ rx, ctx.valueReg? x = some rx ∧
    ((t ∈ pass ∧ v = .reg rx ∧ s' = s) ∨
     (t ∉ pass ∧ t.bits ≤ 32 ∧ v = .reg (s.fresh .int).1 ∧
       s' = (s.fresh .int).2.emit (.extend (s.fresh .int).1 rx sg t.bits toB)))

set_option maxHeartbeats 1000000 in
include hp hc in
theorem zext32_ok {n : Nat} (hn : 40 ≤ n) {x : Nat} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 556 [.value x] s v s') :
    ExtOut ctx x false 32 [.int 32, .int 64] s.1 s'.1 v := by
  have hp' := hp
  isel_split hp hc h 556
  · isel_inv [*, rule_inst_3813] at hm he
    exact ⟨_, ‹_›, _, ‹_›, .inl ⟨by simp, rfl, rfl⟩⟩
  · isel_inv [*, rule_inst_3814] at hm he
    exact ⟨_, ‹_›, _, ‹_›, .inl ⟨by simp, rfl, rfl⟩⟩
  · isel_inv [*, rule_inst_3809] at hm he
    rename_i t hT rx hb hx hext
    obtain ⟨rfl, m, hm, rfl⟩ := extend_ok hp' hc (by omega) hext
    have h32 : t ≠ .int 32 := by
      rintro rfl
      obtain ⟨k, s2, h2⟩ := hpre _ (List.mem_cons_self ..)
      revert h2
      isel_eval [*, rule_inst_3813, ext_value_type ctx _ hT, sem_eq]
      simp
    refine ⟨t, hT, rx, hx, .inr ⟨?_, hb, rfl, ?_⟩⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨h32, fun h => by subst h; exact absurd hb (by decide)⟩
    · rw [ofV_extend_32] at hm
      cases hm; rfl

set_option maxHeartbeats 1000000 in
include hp hc in
theorem sext32_ok {n : Nat} (hn : 40 ≤ n) {x : Nat} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 555 [.value x] s v s') :
    ExtOut ctx x true 32 [.int 32, .int 64] s.1 s'.1 v := by
  have hp' := hp
  isel_split hp hc h 555
  · isel_inv [*, rule_inst_3803] at hm he
    exact ⟨_, ‹_›, _, ‹_›, .inl ⟨by simp, rfl, rfl⟩⟩
  · isel_inv [*, rule_inst_3804] at hm he
    exact ⟨_, ‹_›, _, ‹_›, .inl ⟨by simp, rfl, rfl⟩⟩
  · isel_inv [*, rule_inst_3799] at hm he
    rename_i t hT rx hb hx hext
    obtain ⟨rfl, m, hm, rfl⟩ := extend_ok hp' hc (by omega) hext
    have h32 : t ≠ .int 32 := by
      rintro rfl
      obtain ⟨k, s2, h2⟩ := hpre _ (List.mem_cons_self ..)
      revert h2
      isel_eval [*, rule_inst_3803, ext_value_type ctx _ hT, sem_eq]
      simp
    refine ⟨t, hT, rx, hx, .inr ⟨?_, hb, rfl, ?_⟩⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨h32, fun h => by subst h; exact absurd hb (by decide)⟩
    · rw [ofV_extend_32] at hm
      cases hm; rfl

theorem ofV_extend_64 (rd rn : Reg) (sg : Bool) (a : Nat) :
    MInst.ofV (.data 58 28 [.reg rd, .reg rn, .bool sg, .int (a : Int), .int 64]) =
      some (.extend rd rn sg a 64) := rfl

set_option maxHeartbeats 1000000 in
include hp hc in
theorem zext64_ok {n : Nat} (hn : 40 ≤ n) {x : Nat} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 558 [.value x] s v s') :
    ExtOut ctx x false 64 [.int 64] s.1 s'.1 v := by
  have hp' := hp
  isel_split hp hc h 558
  · isel_inv [*, rule_inst_3829] at hm he
    rename_i t hT rx hb hx hext
    obtain ⟨rfl, m, hm, rfl⟩ := extend_ok hp' hc (by omega) hext
    refine ⟨t, hT, rx, hx, .inr ⟨?_, hb, rfl, ?_⟩⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact fun h => by subst h; exact absurd hb (by decide)
    · rw [ofV_extend_64] at hm
      cases hm; rfl
  · isel_inv [*, rule_inst_3833] at hm he
    exact ⟨_, ‹_›, _, ‹_›, .inl ⟨by simp, rfl, rfl⟩⟩

set_option maxHeartbeats 1000000 in
include hp hc in
theorem sext64_ok {n : Nat} (hn : 40 ≤ n) {x : Nat} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 557 [.value x] s v s') :
    ExtOut ctx x true 64 [.int 64] s.1 s'.1 v := by
  have hp' := hp
  isel_split hp hc h 557
  · isel_inv [*, rule_inst_3819] at hm he
    rename_i t hT rx hb hx hext
    obtain ⟨rfl, m, hm, rfl⟩ := extend_ok hp' hc (by omega) hext
    refine ⟨t, hT, rx, hx, .inr ⟨?_, hb, rfl, ?_⟩⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact fun h => by subst h; exact absurd hb (by decide)
    · rw [ofV_extend_64] at hm
      cases hm; rfl
  · isel_inv [*, rule_inst_3823] at hm he
    exact ⟨_, ‹_›, _, ‹_›, .inl ⟨by simp, rfl, rfl⟩⟩


/-! ## Running emitted code: generic single-instruction steps and fragments -/

section Run
variable {F : BitVec 64 → Prop} {isem : Sem}

/-- A fragment that allocated one fresh vreg and emitted `m` defining only it. -/
theorem Frag.fresh_emit (s : LState) {m : MInst} (hd : vdefs m ⊆ [s.nextVreg]) :
    Frag s ((s.fresh .int).2.emit m) [m] := by
  refine ⟨?_, ?_, ?_⟩
  · simp [LState.emit, LState.fresh]
  · simp [LState.emit, LState.fresh]
  · intro m' hm' d hd'
    simp only [List.mem_singleton] at hm'
    subst hm'
    have := hd hd'
    simp only [List.mem_singleton] at this
    simp [LState.emit, LState.fresh, this]

/-- A fragment that emitted `m`, which defines no vreg. -/
theorem Frag.emit_nodef (s : LState) {m : MInst} (hd : vdefs m = []) : Frag s (s.emit m) [m] := by
  refine ⟨?_, ?_, ?_⟩
  · simp [LState.emit]
  · simp [LState.emit]
  · intro m' hm' d hd'
    simp only [List.mem_singleton] at hm'
    subst hm'
    simp [hd] at hd'

end Run

/-! ## Meaning of `put_in_reg_*ext*` -/

/-- Register value `a` holds `v` (low bits) and, when `v` has at most 32 bits, its low `n` bits
are `v` sign- or zero-extended. -/
def ExtHolds (sg : Bool) (n : Nat) (v : Clif.Val) (a : CV) : Prop :=
  VHolds v a ∧
    (v.ty.width ≤ 32 → (lo64 a).setWidth n = if sg then v.bits.signExtend n else v.bits.setWidth n)

theorem ispec_extend {d : Nat} {rn : Reg} {sg : Bool} {a b : Nat} {x : CV} {w : Arm.ArmState}
    (ha : a = 8 ∨ a = 16 ∨ a = 32) (hb : b = 32 ∨ b = 64) (hab : a < b) :
    ispec (.extend (.vreg d .int) rn sg a b) [x] w =
      some ([ofX (if sg then (((lo64 x).setWidth a).signExtend b).setWidth 64
        else (((lo64 x).setWidth a).setWidth b).setWidth 64)], w, .next) := by
  rcases hb with rfl | rfl <;> rcases ha with rfl | rfl | rfl <;> simp at hab <;> rfl

theorem extHolds_extend (sg : Bool) {ty : Clif.Ty} (bits : BitVec ty.width) (hw : ty.width ≤ 32)
    (b : Nat) (hb : b = 32 ∨ b = 64) (hlt : ty.width < b) (x : CV) (hx : VHolds ⟨ty, bits⟩ x) :
    ExtHolds sg b ⟨ty, bits⟩ (ofX (if sg then (((lo64 x).setWidth ty.width).signExtend b).setWidth 64
        else (((lo64 x).setWidth ty.width).setWidth b).setWidth 64)) := by
  simp only [VHolds] at hx
  refine ⟨?_, fun _ => ?_⟩ <;> simp only [VHolds] <;> subst hx <;>
    cases ty <;> simp [Clif.Ty.width] at hw hlt ⊢ <;> rcases hb with rfl | rfl <;>
    simp at hlt <;> cases sg <;> simp only [lo64, ofX, Bool.false_eq_true, ↓reduceIte] <;> bv_decide

theorem ofClif_bits (ty : Clif.Ty) : (CTy.ofClif ty).bits = ty.width := by cases ty <;> rfl

theorem vreg_lt {ctx : Ctx} {st : LState} (hvb : ValsBelow ctx st) {x : Nat} {r : Reg}
    (h : ctx.valueReg? x = some r) : x < st.nextVreg := hvb x r h

theorem operands_extend' (d x : Nat) (sg : Bool) (a b : Nat) :
    (MInst.extend (.vreg d .int) (.vreg x .int) sg a b).operands =
      .ok #[⟨d, .int, .def, .late, .reg⟩, ⟨x, .int, .use, .early, .reg⟩] := rfl

theorem vdefs_extend' (d x : Nat) (sg : Bool) (a b : Nat) :
    vdefs (MInst.extend (.vreg d .int) (.vreg x .int) sg a b) = [d] := rfl

theorem vuseNums_extend' (d x : Nat) (sg : Bool) (a b : Nat) :
    vuseNums (MInst.extend (.vreg d .int) (.vreg x .int) sg a b) = [x] := rfl

theorem vdefUpd_extend' (d x : Nat) (y : CV) (ρ : Nat → CV) :
    vdefUpd #[⟨d, .int, .def, .late, .reg⟩, ⟨x, .int, .use, .early, .reg⟩] [y] ρ = upd ρ d y := rfl

/-- **Meaning of a `put_in_reg_*ext*` call**: the returned vreg (the value's own, or a fresh one
defined by the emitted `extend`) holds the value, extended to `toB` bits when it is at most 32
bits wide. -/
theorem ExtOut.sem {F : BitVec 64 → Prop} {isem : Sem} (hR : Refines F isem) {f : Clif.Function}
    {ctx : Ctx} (hctx : CtxInv f ctx) {x : Nat} {sg : Bool} {toB : Nat} {pass : List CTy}
    {s s' : LState} {v : V} (hvb : ValsBelow ctx s) (hto : toB = 32 ∨ toB = 64)
    (hpass : ∀ t ∈ pass, t = .int 64 ∨ (t = .int 32 ∧ toB = 32)) (h32 : toB = 32 → .int 32 ∈ pass)
    (h : ExtOut ctx x sg toB pass s s' v) :
    ∃ k ms, v = .reg (.vreg k .int) ∧ Frag s s' ms ∧ k < s'.nextVreg ∧ (s.nextVreg ≤ k ∨ k = x) ∧
      ∀ (fr : Clif.Frame) (ρ : Nat → CV) (vx : Clif.Val), ValsHeld fr ρ → DFGCons ctx fr →
        fr.regs x = some vx →
        UsesLo s.nextVreg fr ms ∧ ∀ w, Runs F isem ms ρ w (fun ρ' _ => ExtHolds sg toB vx (ρ' k)) := by
  obtain ⟨t, hT, rx, hx, hcase⟩ := h
  have hrx := hctx.valueReg x rx hx
  subst hrx
  have hxlt := vreg_lt hvb hx
  rcases hcase with ⟨ht, rfl, hs⟩ | ⟨ht, hb, rfl, rfl⟩
  · subst s'
    refine ⟨x, [], rfl, Frag.nil _, hxlt, .inr rfl, fun fr ρ vx hheld hdfg hvx => ⟨UsesLo.nil _ _, fun w => ?_⟩⟩
    refine Runs.nil ⟨hheld x vx hvx, fun hw => ?_⟩
    have hty := hdfg.2 x t vx hT hvx
    obtain ⟨vty, vb⟩ := vx
    have hv := hheld x _ hvx
    simp only [VHolds] at hv
    subst hty
    rcases hpass _ ht with h64 | ⟨h32', rfl⟩
    · cases vty <;> simp [CTy.ofClif] at h64; simp [Clif.Ty.width] at hw
    · cases vty <;> simp [CTy.ofClif] at h32'
      subst hv
      simp only [lo64, Clif.Ty.width, Bool.false_eq_true, ↓reduceIte]
      cases sg <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> bv_decide
  · have hf : (s.fresh .int).1 = .vreg s.nextVreg .int := rfl
    rw [hf]
    refine ⟨s.nextVreg, _, rfl, Frag.fresh_emit s (by rw [vdefs_extend']; simp), by
      simp [LState.emit, LState.fresh], .inl (Nat.le_refl _), fun fr ρ vx hheld hdfg hvx => ⟨?_, fun w => ?_⟩⟩
    · intro m hm u hu
      simp only [List.mem_singleton] at hm
      subst hm
      rw [vuseNums_extend', List.mem_singleton] at hu
      subst hu
      exact .inr (by simp [hvx])
    · have hty := hdfg.2 x t vx hT hvx
      obtain ⟨vty, vb⟩ := vx
      subst hty
      rw [ofClif_bits] at hb
      dsimp only at hb
      have hne : vty.width < toB := by
        rcases hto with rfl | rfl
        · have := h32 rfl
          cases vty <;> simp [Clif.Ty.width, CTy.ofClif] at hb ⊢
          exact ht this
        · omega
      have hfrom : vty.width = 8 ∨ vty.width = 16 ∨ vty.width = 32 := by
        cases vty <;> simp [Clif.Ty.width] at hb ⊢
      have hs := ispec_extend (d := s.nextVreg) (rn := .vreg x .int) (sg := sg) (x := ρ x) (w := w)
        hfrom hto hne
      rw [ofClif_bits]
      refine Runs.one hR (operands_extend' _ _ _ _ _) hs rfl (SameWorldNF.refl F w) ?_
      · intro w'' _
        have hv := hheld x _ hvx
        rw [vdefUpd_extend']
        simp only [upd, ite_true]
        exact extHolds_extend sg vb (by omega) toB hto hne _ hv
end Backend.Proof
