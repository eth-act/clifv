import FV.Backend.Proof.IselCovTDom
import FV.Backend.Proof.IselCovSem

/-!
# Form coverage over float-capable contexts (typed V3): the meaning of the abstract values

`γP ctx I a v`: the ISLE value `v` (of a run of the driver in context `ctx`) is one of the values
`a` describes, where `I fs` is the meaning of the instruction atom `inst fs`. The typed atoms:

* `val ts`: `.value x` with `ValIn ctx x ts` (`x`'s type, if any, is in `ts`; an untyped value
  needs an integer type in `ts`, since its vreg is an int vreg, `valClassOf`);
* `vals tss`: `.values xs`, `ValIn` position by position;
* `movi`: the plain `movi` immediate.

The instruction meaning is fixed in `IselCovTFam` (an instruction of the context of a family of
`famTab`, whose data is described by `γP ctx noInst`). The shallow lemmas (register kinds, enum
variants) are here, for every `I` that only describes instruction references (`InstRef I`).

The typed analysis has its own coverage (`Covered`, `covV`, `covVL`): the integer analysis's
(`Cov.Covered`: `isCtl` or `FormOk`) plus the literal-pool load (`MInst.isPoolLoad`, #565), which
only `constant_f64`'s pool rule emits. The integer analysis keeps the two-way form, so on subset E
the lowering has no pool load (`Driver.formsCovered2_complete`). `covV_of_cov` lifts the integer
facts.
-/

namespace Backend.Proof.CovT

open Backend Backend.Proof Backend.Proof.Flow Isle Isle.Aarch64
open Backend.Proof.Cov (DeepRegs NumOk numOk_shape numOk_mono kind_cases regsIn_reg kind_int
  kind_float kind_xzr)

/-- An instruction is covered by the typed analysis: a control form, a covered straight-line form
or the literal-pool load (#565). -/
def Covered (i : MInst) : Bool := i.isCtl || FormOk default i || i.isPoolLoad

mutual
/-- Every `MInst` inside the value is covered (`Covered`). -/
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

theorem covered_of_cov {i : MInst} (h : Cov.Covered i = true) : Covered i = true := by
  unfold Cov.Covered at h
  unfold Covered
  rw [h]; rfl

theorem covV_data (t k : Nat) (vs : List V) :
    covV (.data t k vs) = ((t != tyMInst || (match MInst.ofV (.data t k vs) with
      | some i => Covered i
      | none => true)) && covVL vs) := by
  rfl

theorem covVL_iff : ∀ {vs : List V}, covVL vs = true ↔ ∀ v ∈ vs, covV v = true
  | [] => by simp [covVL]
  | v :: vs => by simp [covVL, covVL_iff]

mutual
/-- The integer analysis's coverage implies the typed one. -/
theorem covV_of_cov : ∀ {v : V}, Cov.covV v = true → covV v = true
  | .data t k fs, h => by
    simp only [Cov.covV] at h
    rw [covV_data]
    simp only [Bool.and_eq_true, Bool.or_eq_true] at h ⊢
    refine ⟨?_, covVL_of_cov h.2⟩
    rcases h.1 with h1 | h1
    · exact .inl h1
    · right
      cases hm : MInst.ofV (.data t k fs) with
      | none => rfl
      | some i => rw [hm] at h1; exact covered_of_cov h1
  | .int _, _ | .bool _, _ | .ty _, _ | .inst _, _ | .value _, _ | .reg _, _ | .regs _, _
  | .regsVec _, _ | .label _, _ | .labels _, _ | .values _, _ | .blockCalls _, _ | .op _, _ => rfl
/-- `covV_of_cov` on a list. -/
theorem covVL_of_cov : ∀ {vs : List V}, Cov.covVL vs = true → covVL vs = true
  | [], _ => rfl
  | v :: vs, h => by
    simp only [Cov.covVL, covVL, Bool.and_eq_true] at h ⊢
    exact ⟨covV_of_cov h.1, covVL_of_cov h.2⟩
end

/-- `x` has a type of `ts`; an untyped value (whose vreg is an int vreg) needs an integer type in
`ts`. -/
def ValIn (ctx : Ctx) (x : Nat) (ts : List CTy) : Prop :=
  (∀ t, ctx.valueType? x = some t → t ∈ ts) ∧
    (ctx.valueType? x = none → ∃ t ∈ ts, t.regClass? = some .int)

/-- `ValIn` position by position (same lengths). -/
def ValsIn (ctx : Ctx) (xs : List Nat) (tss : List (List CTy)) : Prop :=
  xs.length = tss.length ∧
    ∀ (i x : Nat) (ts : List CTy), xs[i]? = some x → tss[i]? = some ts → ValIn ctx x ts

/-- The plain `movi` immediate (`FormOk`'s `VecDupImm`). -/
def MoviOk (i : ASIMDMovModImm) : Prop := i.shift = 0 ∧ i.shiftOnes = false ∧ i.is64 = false

section
variable (ctx : Ctx) (I : List Nat → V → Prop)

mutual
/-- **The meaning of an abstract value** (`I`: the meaning of `inst fs`). -/
def γP : AT → V → Prop
  | .bot, _ => False
  | .flat m c, v => DeepRegs m v ∧ (c = true → covV v = true)
  | .reg m, v => ∃ r, v = .reg r ∧ r.kind &&& m ≠ 0
  | .ty ts, v => ∃ t ∈ ts, v = .ty t
  | .bool b, v => v = .bool b
  | .logic sz, v => ∃ i, v = .op (.immLogic i) ∧ ImmLogic.ofNat? i.value sz = some i ∧
      ∀ op, logicOpOk op = true → logicImmOk op sz i = true
  | .scale b, v => ∃ o, v = .op (.uimm12Scaled o) ∧ o % b = 0 ∧ o / b < 4096
  | .simm9, v => ∃ i, v = .op (.simm9 i) ∧ -256 ≤ i ∧ i < 256
  | .val ts, v => ∃ x, v = .value x ∧ ValIn ctx x ts
  | .vals tss, v => ∃ xs, v = .values xs ∧ ValsIn ctx xs tss
  | .valsAll ts, v => ∃ xs, v = .values xs ∧ ∀ x ∈ xs, ValIn ctx x ts
  | .inst fs, v => I fs v
  | .movi, v => ∃ i, v = .op (.movModImm i) ∧ MoviOk i
  | .extv, v => ∃ x e b, v = .op (.extended x e) ∧ ctx.valueType? x = some (.int b)
  | .alts as, v => γAnyP as v
  | .data t k fs, v => ∃ vs, v = .data t k vs ∧ γLP fs vs
  | .num k b, v => NumOk k b v
/-- Some abstract value of the list describes `v`. -/
def γAnyP : List AT → V → Prop
  | [], _ => False
  | a :: as, v => γP a v ∨ γAnyP as v
/-- Pointwise `γP` (same lengths). -/
def γLP : List AT → List V → Prop
  | [], [] => True
  | a :: as, v :: vs => γP a v ∧ γLP as vs
  | _, _ => False
end

end

/-- `I` describes only instruction references. -/
def InstRef (I : List Nat → V → Prop) : Prop := ∀ fs v, I fs v → ∃ j, v = .inst j

/-- The meaning of instruction atoms inside families' data: none. -/
def noInst : List Nat → V → Prop := fun _ _ => False

theorem instRef_noInst : InstRef noInst := fun _ _ h => h.elim

variable {ctx : Ctx} {I : List Nat → V → Prop}

theorem γAnyP_iff : ∀ {as : List AT} {v : V}, γAnyP ctx I as v ↔ ∃ a ∈ as, γP ctx I a v
  | [], v => by simp [γAnyP]
  | a :: as, v => by
    rw [γAnyP, γAnyP_iff]
    simp

theorem γLP_length : ∀ {as : List AT} {vs : List V}, γLP ctx I as vs → as.length = vs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp [γLP_length h.2]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem γLP_get : ∀ {as : List AT} {vs : List V}, γLP ctx I as vs →
    ∀ (i : Nat) (a : AT) (v : V), as[i]? = some a → vs[i]? = some v → γP ctx I a v
  | [], [], _, _, _, _, h, _ => by cases h
  | a :: as, w :: vs, ⟨h1, h2⟩, i, b, v, ha, hv => by
    cases i with
    | zero => simp at ha hv; subst ha hv; exact h1
    | succ i => exact γLP_get h2 i b v (by simpa using ha) (by simpa using hv)
  | [], _ :: _, h, _, _, _, _, _ => h.elim
  | _ :: _, [], h, _, _, _, _, _ => h.elim

/-- **Monotonicity in the instruction meaning.** -/
theorem γP_mono {J : List Nat → V → Prop} (hIJ : ∀ fs v, I fs v → J fs v) :
    ∀ (a : AT) (v : V), γP ctx I a v → γP ctx J a v
  | .bot, _, h => h
  | .flat _ _, _, h => h
  | .reg _, _, h => h
  | .ty _, _, h => h
  | .bool _, _, h => h
  | .logic _, _, h => h
  | .scale _, _, h => h
  | .simm9, _, h => h
  | .val _, _, h => h
  | .vals _, _, h => h
  | .valsAll _, _, h => h
  | .inst fs, v, h => hIJ fs v h
  | .movi, _, h => h
  | .extv, _, h => h
  | .num _ _, _, h => h
  | .alts as, v, h => by
    simp only [γP] at h ⊢
    rw [γAnyP_iff] at h ⊢
    obtain ⟨a, ha, hv⟩ := h
    exact ⟨a, ha, γP_mono hIJ a v hv⟩
  | .data t k fs, v, h => by
    simp only [γP] at h ⊢
    obtain ⟨vs, rfl, hl⟩ := h
    exact ⟨vs, rfl, γLP_mono hIJ fs vs hl⟩
where
  γLP_mono {J : List Nat → V → Prop} (hIJ : ∀ fs v, I fs v → J fs v) :
      ∀ (as : List AT) (vs : List V), γLP ctx I as vs → γLP ctx J as vs
    | [], [], _ => trivial
    | a :: as, v :: vs, ⟨h1, h2⟩ => ⟨γP_mono hIJ a v h1, γLP_mono hIJ as vs h2⟩
    | [], _ :: _, h => h.elim
    | _ :: _, [], h => h.elim

/-! ## Register kinds -/

section Kinds
variable (hI : InstRef I)
include hI

/-- The register a value names has a kind of the abstract value's mask. -/
theorem mask_soundP {a : AT} {r : Reg} (h : γP ctx I a (.reg r)) : r.kind &&& a.mask ≠ 0 := by
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
  | val ts => obtain ⟨x, he, -⟩ := h; cases he
  | vals tss => obtain ⟨xs, he, -⟩ := h; cases he
  | valsAll ts => obtain ⟨xs, he, -⟩ := h; cases he
  | inst fs => obtain ⟨j, he⟩ := hI fs _ h; cases he
  | movi => obtain ⟨i, he, -⟩ := h; cases he
  | extv => obtain ⟨x, e, b, he, -⟩ := h; cases he
  | alts as => simp only [AT.mask]; rcases kind_cases r with h | h | h | h <;> rw [h] <;> decide
  | data t k fs => obtain ⟨vs, he, -⟩ := h; cases he
  | num k b => rcases numOk_shape h with ⟨_, he⟩ | ⟨_, he⟩ <;> cases he

theorem isV_soundP {a : AT} (ha : a.isV = true) {r : Reg} (h : γP ctx I a (.reg r)) :
    ∃ n, r = .vreg n .int := by
  have hm := mask_soundP hI h
  simp only [AT.isV, beq_iff_eq] at ha
  apply kind_int
  rcases kind_cases r with h1 | h1 | h1 | h1 <;> rw [h1] at hm ⊢ <;> try rfl
  all_goals exfalso; apply hm; apply Nat.eq_of_testBit_eq; intro i
  all_goals have := congrArg (·.testBit i) ha
  all_goals simp only [Nat.testBit_and] at this ⊢
  all_goals rcases i with _ | _ | _ | _ | i <;> simp_all [Nat.testBit_succ]

theorem isF_soundP {a : AT} (ha : a.isF = true) {r : Reg} (h : γP ctx I a (.reg r)) :
    ∃ n, r = .vreg n .float := by
  have hm := mask_soundP hI h
  simp only [AT.isF, beq_iff_eq] at ha
  apply kind_float
  rcases kind_cases r with h1 | h1 | h1 | h1 <;> rw [h1] at hm ⊢ <;> try rfl
  all_goals exfalso; apply hm; apply Nat.eq_of_testBit_eq; intro i
  all_goals have := congrArg (·.testBit i) ha
  all_goals simp only [Nat.testBit_and] at this ⊢
  all_goals rcases i with _ | _ | _ | _ | i <;> simp_all [Nat.testBit_succ]

theorem isVZ_soundP {a : AT} (ha : a.isVZ = true) {r : Reg} (h : γP ctx I a (.reg r)) :
    (∃ n, r = .vreg n .int) ∨ r = .xzr := by
  have hm := mask_soundP hI h
  simp only [AT.isVZ, beq_iff_eq] at ha
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

end Kinds

/-! ## Enum variants -/

theorem mapM_enum_mem : ∀ {as : List AT} {ks : List Nat},
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
theorem enumsOf_soundP {a : AT} {ks : List Nat} (ha : a.enumsOf = some ks) {v : V}
    (h : γP ctx I a v) : ∃ t k, v = .data t k [] ∧ k ∈ ks := by
  cases a with
  | data t k fs =>
    cases fs with
    | nil =>
      simp only [AT.enumsOf, Option.some.injEq] at ha
      subst ha
      obtain ⟨vs, rfl, hl⟩ := h
      cases vs with
      | nil => exact ⟨t, k, rfl, List.mem_singleton_self _⟩
      | cons _ _ => exact hl.elim
    | cons _ _ => simp [AT.enumsOf] at ha
  | alts as =>
    simp only [AT.enumsOf] at ha
    obtain ⟨b, hb, hv⟩ := γAnyP_iff.mp h
    obtain ⟨t, k, rfl, hk⟩ := mapM_enum_mem ha b hb
    obtain ⟨vs, rfl, hl⟩ := hv
    cases vs with
    | nil => exact ⟨t, k, rfl, hk⟩
    | cons _ _ => exact hl.elim
  | _ => simp [AT.enumsOf] at ha

theorem enumAll_soundP {a : AT} {p : Nat → Bool} (ha : a.enumAll p = true) {v : V}
    (h : γP ctx I a v) : ∃ t k, v = .data t k [] ∧ p k = true := by
  unfold AT.enumAll at ha
  split at ha
  · rename_i ks hks
    obtain ⟨t, k, rfl, hk⟩ := enumsOf_soundP hks h
    exact ⟨t, k, rfl, List.all_eq_true.mp ha k hk⟩
  · cases ha

end Backend.Proof.CovT
