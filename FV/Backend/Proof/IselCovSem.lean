import FV.Backend.Proof.IselCovDom

/-!
# Form coverage of the ISLE lowering (V3): the meaning of the abstract values

`γ f ctx a v`: the ISLE value `v` (of a run of the driver on `f` in context `ctx`) is one of
the values `a` describes. `covV v`: every `MInst` inside `v` is covered (`isCtl` or `FormOk`).
The shallow lemmas about the checks `covOk` reads (register kinds, enum variants, addressing
modes) are here; `covOk_sound` is in `IselCovForm`.
-/

namespace Backend.Proof.Cov

open Backend Backend.Proof Backend.Proof.Flow Isle Isle.Aarch64

/-- An instruction is covered: a control form or a covered straight-line form. -/
def Covered (i : MInst) : Bool := i.isCtl || FormOk default i

mutual
/-- Every `MInst` inside the value is covered. -/
def covV : V → Bool
  | .data t k fs =>
    (t != tyMInst || (match MInst.ofV (.data t k fs) with
      | some i => Covered i
      | none => true)) && covVL fs
  | _ => true
/-- `covV` of every value of a list. -/
def covVL : List V → Bool
  | [] => true
  | v :: vs => covV v && covVL vs
end

/-- The emitter encodes every logical immediate `ImmLogic.ofNat?` accepts (`bitmaskEnc?` is
complete and decodes back): the remaining V3 obligation, a hypothesis until proven. -/
def LogicImmComplete : Prop :=
  ∀ (i : ImmLogic) (sz : OperandSize) (op : ALUOp), ImmLogic.ofNat? i.value sz = some i →
    logicOpOk op = true → logicImmOk op sz i = true

/-- Every register inside `v` has a kind of the mask `m`. -/
def DeepRegs (m : Nat) (v : V) : Prop := ∀ r ∈ v.regsIn, r.kind &&& m ≠ 0

/-- **The meaning of a numeric/operand leaf** `AW.num k b`. -/
def NumOk : NK → Nat → V → Prop
  | .int, b, v => ∃ i : Int, v = .int i ∧ 0 ≤ i ∧ i < b
  | .imm12, b, v => ∃ i : Imm12, v = .op (.imm12 i) ∧ i.bits < b
  | .immShift, b, v => ∃ n, v = .op (.immShift n) ∧ n < b
  | .uimm5, b, v => ∃ n, v = .op (.uimm5 n) ∧ n < b
  | .uimm6, b, v => ∃ n, v = .op (.uimm6 n) ∧ n < b
  | .shiftAmt, b, v => ∃ s : ShiftOpAndAmt, v = .op (.shiftOpAndAmt s) ∧ s.amt < b ∧ s.op ≠ .ror
  | .mwc, b, v => ∃ m : MoveWideConst, v = .op (.moveWideConst m) ∧ m.bits < 2 ^ 16 ∧ m.shift < b
  | .callInfo, _, v => ∃ c : CallInfo, v = .op (.callInfo c) ∧
      ∀ r, c.dest = .reg r → ∃ n, r = .vreg n .int

/-- A leaf describes an integer or an operand. -/
theorem numOk_shape {k : NK} {b : Nat} {v : V} (h : NumOk k b v) :
    (∃ i, v = .int i) ∨ ∃ o, v = .op o := by
  cases k <;> simp only [NumOk] at h
  · obtain ⟨i, rfl, -⟩ := h; exact .inl ⟨i, rfl⟩
  all_goals obtain ⟨_, rfl, -⟩ := h; exact .inr ⟨_, rfl⟩

/-- A larger bound describes more. -/
theorem numOk_mono {k : NK} {b b' : Nat} (hb : b ≤ b') {v : V} (h : NumOk k b v) : NumOk k b' v := by
  cases k <;> simp only [NumOk] at h ⊢
  · obtain ⟨i, rfl, h0, h1⟩ := h; exact ⟨i, rfl, h0, by omega⟩
  · obtain ⟨i, rfl, h1⟩ := h; exact ⟨i, rfl, by omega⟩
  · obtain ⟨i, rfl, h1⟩ := h; exact ⟨i, rfl, by omega⟩
  · obtain ⟨i, rfl, h1⟩ := h; exact ⟨i, rfl, by omega⟩
  · obtain ⟨i, rfl, h1⟩ := h; exact ⟨i, rfl, by omega⟩
  · obtain ⟨i, rfl, h1, h2⟩ := h; exact ⟨i, rfl, by omega, h2⟩
  · obtain ⟨i, rfl, h1, h2⟩ := h; exact ⟨i, rfl, h1, by omega⟩
  · exact h

section
variable (f : Clif.Function) (ctx : Ctx)

mutual
/-- **The meaning of an abstract value.** -/
def γ : AW → V → Prop
  | .bot, _ => False
  | .flat m c, v => DeepRegs m v ∧ (c = true → covV v = true)
  | .reg m, v => ∃ r, v = .reg r ∧ r.kind &&& m ≠ 0
  | .ty ts, v => ∃ t ∈ ts, v = .ty t
  | .bool b, v => v = .bool b
  | .logic sz, v => ∃ i, v = .op (.immLogic i) ∧ ImmLogic.ofNat? i.value sz = some i ∧
      ∀ op, logicOpOk op = true → logicImmOk op sz i = true
  | .scale b, v => ∃ o, v = .op (.uimm12Scaled o) ∧ o % b = 0 ∧ o / b < 4096
  | .simm9, v => ∃ i, v = .op (.simm9 i) ∧ -256 ≤ i ∧ i < 256
  | .xv e, v => e.toAV.Holds f ctx v ∧ v.regsIn = [] ∧ covV v = true
  | .alts as, v => γAny as v
  | .data t k fs, v => ∃ vs, v = .data t k vs ∧ γL fs vs
  | .num k b, v => NumOk k b v
/-- Some abstract value of the list describes `v`. -/
def γAny : List AW → V → Prop
  | [], _ => False
  | a :: as, v => γ a v ∨ γAny as v
/-- Pointwise `γ` (same lengths). -/
def γL : List AW → List V → Prop
  | [], [] => True
  | a :: as, v :: vs => γ a v ∧ γL as vs
  | _, _ => False
end

end

variable {f : Clif.Function} {ctx : Ctx}

theorem γAny_iff : ∀ {as : List AW} {v : V}, γAny f ctx as v ↔ ∃ a ∈ as, γ f ctx a v
  | [], v => by simp [γAny]
  | a :: as, v => by
    rw [γAny, γAny_iff]
    simp

theorem γL_length : ∀ {as : List AW} {vs : List V}, γL f ctx as vs → as.length = vs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp [γL_length h.2]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem γL_get : ∀ {as : List AW} {vs : List V}, γL f ctx as vs →
    ∀ (i : Nat) (a : AW) (v : V), as[i]? = some a → vs[i]? = some v → γ f ctx a v
  | [], [], _, _, _, _, h, _ => by cases h
  | a :: as, w :: vs, ⟨h1, h2⟩, i, b, v, ha, hv => by
    cases i with
    | zero => simp at ha hv; subst ha hv; exact h1
    | succ i => exact γL_get h2 i b v (by simpa using ha) (by simpa using hv)
  | [], _ :: _, h, _, _, _, _, _ => h.elim
  | _ :: _, [], h, _, _, _, _, _ => h.elim

/-! ## Register kinds -/

theorem kind_cases (r : Reg) : r.kind = 1 ∨ r.kind = 2 ∨ r.kind = 4 ∨ r.kind = 8 := by
  unfold Reg.kind; split <;> simp

theorem regsIn_reg (r : Reg) : (V.reg r).regsIn = [r] := rfl

/-- The register a value names has a kind of the abstract value's mask. -/
theorem mask_sound {a : AW} {r : Reg} (h : γ f ctx a (.reg r)) : r.kind &&& a.mask ≠ 0 := by
  cases a with
  | bot => exact h.elim
  | flat m c => exact h.1 r (by simp [regsIn_reg])
  | reg m =>
    obtain ⟨r', he, hk⟩ := h
    cases he; exact hk
  | ty ts => obtain ⟨t, -, he⟩ := h; cases he
  | bool b => cases h
  | logic sz => obtain ⟨i, he, -⟩ := h; cases he
  | scale b => obtain ⟨o, he, -⟩ := h; cases he
  | simm9 => obtain ⟨i, he, -⟩ := h; cases he
  | xv e => simp [γ, regsIn_reg] at h
  | alts as => simp only [AW.mask]; rcases kind_cases r with h | h | h | h <;> rw [h] <;> decide
  | data t k fs => obtain ⟨vs, he, -⟩ := h; cases he
  | num k b => rcases numOk_shape h with ⟨_, he⟩ | ⟨_, he⟩ <;> cases he

theorem kind_int {r : Reg} (h : r.kind = 1) : ∃ n, r = .vreg n .int := by
  unfold Reg.kind at h; split at h <;> simp_all

theorem kind_float {r : Reg} (h : r.kind = 2) : ∃ n, r = .vreg n .float := by
  unfold Reg.kind at h; split at h <;> simp_all

theorem kind_xzr {r : Reg} (h : r.kind = 4) : r = .xzr := by
  unfold Reg.kind at h; split at h <;> simp_all

theorem isV_sound {a : AW} (ha : a.isV = true) {r : Reg} (h : γ f ctx a (.reg r)) :
    ∃ n, r = .vreg n .int := by
  have hm := mask_sound h
  simp only [AW.isV, beq_iff_eq] at ha
  apply kind_int
  rcases kind_cases r with h1 | h1 | h1 | h1 <;> rw [h1] at hm ⊢ <;> try rfl
  all_goals exfalso; apply hm; apply Nat.eq_of_testBit_eq; intro i
  all_goals have := congrArg (·.testBit i) ha
  all_goals simp only [Nat.testBit_and] at this ⊢
  all_goals rcases i with _ | _ | _ | _ | i <;> simp_all [Nat.testBit_succ]

theorem isF_sound {a : AW} (ha : a.isF = true) {r : Reg} (h : γ f ctx a (.reg r)) :
    ∃ n, r = .vreg n .float := by
  have hm := mask_sound h
  simp only [AW.isF, beq_iff_eq] at ha
  apply kind_float
  rcases kind_cases r with h1 | h1 | h1 | h1 <;> rw [h1] at hm ⊢ <;> try rfl
  all_goals exfalso; apply hm; apply Nat.eq_of_testBit_eq; intro i
  all_goals have := congrArg (·.testBit i) ha
  all_goals simp only [Nat.testBit_and] at this ⊢
  all_goals rcases i with _ | _ | _ | _ | i <;> simp_all [Nat.testBit_succ]

theorem isVZ_sound {a : AW} (ha : a.isVZ = true) {r : Reg} (h : γ f ctx a (.reg r)) :
    (∃ n, r = .vreg n .int) ∨ r = .xzr := by
  have hm := mask_sound h
  simp only [AW.isVZ, beq_iff_eq] at ha
  rcases kind_cases r with h1 | h1 | h1 | h1
  · exact .inl (kind_int h1)
  · rw [h1] at hm; exfalso; apply hm; apply Nat.eq_of_testBit_eq; intro i
    have := congrArg (·.testBit i) ha
    simp only [Nat.testBit_and] at this ⊢
    rcases i with _ | _ | _ | _ | i <;> simp_all [Nat.testBit_succ]
  · exact .inr (kind_xzr h1)
  · rw [h1] at hm; exfalso; apply hm; apply Nat.eq_of_testBit_eq; intro i
    have := congrArg (·.testBit i) ha
    simp only [Nat.testBit_and] at this ⊢
    rcases i with _ | _ | _ | _ | i <;> simp_all [Nat.testBit_succ]

/-! ## Enum variants -/

theorem mapM_enum_mem : ∀ {as : List AW} {ks : List Nat},
    as.mapM (fun a => match a with | .data _ k [] => some k | _ => none) = some ks →
    ∀ a ∈ as, ∃ t k, a = .data t k [] ∧ k ∈ ks
  | [], ks, _ => fun _ h => by cases h
  | a :: as, ks, h => by
    rw [List.mapM_cons] at h
    obtain ⟨k0, h0, h⟩ := bind_some_ex h
    obtain ⟨ks', h1, h⟩ := bind_some_ex h
    simp only [pure, Option.some.injEq] at h
    subst h
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · split at h0
      · cases h0; exact ⟨_, _, rfl, List.mem_cons_self⟩
      · cases h0
    · obtain ⟨t, k, he, hk⟩ := mapM_enum_mem h1 b hb
      exact ⟨t, k, he, List.mem_cons_of_mem _ hk⟩

/-- A field-less enum value has one of the abstract value's variants. -/
theorem enumsOf_sound {a : AW} {ks : List Nat} (ha : a.enumsOf = some ks) {v : V}
    (h : γ f ctx a v) : ∃ t k, v = .data t k [] ∧ k ∈ ks := by
  cases a with
  | data t k fs =>
    cases fs with
    | nil =>
      simp only [AW.enumsOf, Option.some.injEq] at ha
      subst ha
      obtain ⟨vs, rfl, hl⟩ := h
      cases vs with
      | nil => exact ⟨t, k, rfl, List.mem_singleton_self _⟩
      | cons _ _ => exact hl.elim
    | cons _ _ => simp [AW.enumsOf] at ha
  | alts as =>
    simp only [AW.enumsOf] at ha
    obtain ⟨b, hb, hv⟩ := γAny_iff.mp h
    obtain ⟨t, k, rfl, hk⟩ := mapM_enum_mem ha b hb
    obtain ⟨vs, rfl, hl⟩ := hv
    cases vs with
    | nil => exact ⟨t, k, rfl, hk⟩
    | cons _ _ => exact hl.elim
  | _ => simp [AW.enumsOf] at ha

theorem enumAll_sound {a : AW} {p : Nat → Bool} (ha : a.enumAll p = true) {v : V}
    (h : γ f ctx a v) : ∃ t k, v = .data t k [] ∧ p k = true := by
  unfold AW.enumAll at ha
  split at ha
  · rename_i ks hks
    obtain ⟨t, k, rfl, hk⟩ := enumsOf_sound hks h
    exact ⟨t, k, rfl, List.all_eq_true.mp ha k hk⟩
  · cases ha

end Backend.Proof.Cov
