import FV.Backend.Proof.IselCovSem
import FV.Backend.Proof.IselExclT

/-!
# Form coverage over float-capable contexts: the meaning of the abstract values

The typed counterpart of `IselCovSem`: `γT S iOps fOps f ctx a v` is `γ f ctx a v` with the
`.xv` case read over the typed abstract values `AVT` (`IselExclT`): a `.xv .data` value is the
`InstructionData` of an instruction of the scope `S` whose opcode is in `iOps` or `fOps`
(`AVT.HoldsS`; `InstSplit` of a context with `CtxInvT` provides it, `inst_split`). Every other
case is `γ`'s, and the context enters only through the scope `S`.

The shape lemmas are `γ`'s, restated for `γT` (`γT` of a register, an enum, a leaf; the masks
`isV`/`isF`/`isVZ`; `aun`/`aunS` fields come with `IselCovSoundT`). `Holds2T` is `γLT` pointwise,
`HoldsPT`/`EnvOKT` the positional forms.
-/

namespace Backend.Proof.Cov

open Backend Backend.Proof Backend.Proof.Flow Isle Isle.Aarch64

/-- The exclusion checker's abstract value, at the scope's opcode sets. -/
def XK.toAVT (iOps fOps : List Nat) : XK → AVT
  | .inst => .inst
  | .data => .data (iOps ++ fOps)
  | .value => .value

section
variable (S : Clif.Inst → Bool) (iOps fOps : List Nat) (f : Clif.Function) (ctx : Ctx)

mutual
/-- **The meaning of an abstract value** over a float-capable context: `γ` with `.xv` read
over `AVT.HoldsS` at the scope `S`. -/
def γT : AW → V → Prop
  | .bot, _ => False
  | .flat m c, v => DeepRegs m v ∧ (c = true → covV v = true)
  | .reg m, v => ∃ r, v = .reg r ∧ r.kind &&& m ≠ 0
  | .ty ts, v => ∃ t ∈ ts, v = .ty t
  | .bool b, v => v = .bool b
  | .logic sz, v => ∃ i, v = .op (.immLogic i) ∧ ImmLogic.ofNat? i.value sz = some i ∧
      ∀ op, logicOpOk op = true → logicImmOk op sz i = true
  | .scale b, v => ∃ o, v = .op (.uimm12Scaled o) ∧ o % b = 0 ∧ o / b < 4096
  | .simm9, v => ∃ i, v = .op (.simm9 i) ∧ -256 ≤ i ∧ i < 256
  | .xv e, v => (e.toAVT iOps fOps).HoldsS S f ctx v ∧ v.regsIn = [] ∧ covV v = true
  | .alts as, v => γAnyT as v
  | .data t k fs, v => ∃ vs, v = .data t k vs ∧ γLT fs vs
  | .num k b, v => NumOk k b v
/-- Some abstract value of the list describes `v`. -/
def γAnyT : List AW → V → Prop
  | [], _ => False
  | a :: as, v => γT a v ∨ γAnyT as v
/-- Pointwise `γT` (same lengths). -/
def γLT : List AW → List V → Prop
  | [], [] => True
  | a :: as, v :: vs => γT a v ∧ γLT as vs
  | _, _ => False
end

end

variable {S : Clif.Inst → Bool} {iOps fOps : List Nat} {f : Clif.Function} {ctx : Ctx}

theorem γAnyT_iff : ∀ {as : List AW} {v : V},
    γAnyT S iOps fOps f ctx as v ↔ ∃ a ∈ as, γT S iOps fOps f ctx a v
  | [], v => by simp [γAnyT]
  | a :: as, v => by
    rw [γAnyT, γAnyT_iff]
    simp

theorem γLT_length : ∀ {as : List AW} {vs : List V},
    γLT S iOps fOps f ctx as vs → as.length = vs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp [γLT_length h.2]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem γLT_get : ∀ {as : List AW} {vs : List V}, γLT S iOps fOps f ctx as vs →
    ∀ (i : Nat) (a : AW) (v : V), as[i]? = some a → vs[i]? = some v → γT S iOps fOps f ctx a v
  | [], [], _, _, _, _, h, _ => by cases h
  | a :: as, w :: vs, ⟨h1, h2⟩, i, b, v, ha, hv => by
    cases i with
    | zero => simp at ha hv; subst ha hv; exact h1
    | succ i => exact γLT_get h2 i b v (by simpa using ha) (by simpa using hv)
  | [], _ :: _, h, _, _, _, _, _ => h.elim
  | _ :: _, [], h, _, _, _, _, _ => h.elim

/-! ## Positional descriptions -/

/-- Abstract values describe values pointwise (same lengths). -/
def Holds2T (f : Clif.Function) (ctx : Ctx) : List AW → List V → Prop := γLT S iOps fOps f ctx

/-- Abstract values describe values position by position, `top` past the end. -/
def HoldsPT (f : Clif.Function) (ctx : Ctx) (as : List AW) (vs : List V) : Prop :=
  ∀ i v, vs[i]? = some v → γT S iOps fOps f ctx (as.getD i .top) v

/-- The abstract environment describes the bound variables (`top` past its end). -/
def EnvOKT (f : Clif.Function) (ctx : Ctx) (aenv : List AW) (env : Isle.Interp.Env V) : Prop :=
  ∀ x w, env[x]? = some (some w) → γT S iOps fOps f ctx (aenv.getD x .top) w

theorem γT_top (v : V) : γT S iOps fOps f ctx AW.top v :=
  ⟨fun r _ => kind_and_15 r, fun h => by cases h⟩

theorem holdsPT_of_holds2T : ∀ {as : List AW} {vs : List V},
    Holds2T S iOps fOps f ctx as vs → HoldsPT S iOps fOps f ctx as vs
  | [], [], _ => fun _ _ h => by simp at h
  | a :: as, v :: vs, ⟨h1, h2⟩ => by
    intro i w hw
    cases i with
    | zero => simp at hw; subst hw; exact h1
    | succ i => simpa using holdsPT_of_holds2T h2 i w (by simpa using hw)
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem holdsPT_cons {a : AW} {as : List AW} {v : V} {vs : List V}
    (h : HoldsPT S iOps fOps f ctx (a :: as) (v :: vs)) :
    γT S iOps fOps f ctx a v ∧ HoldsPT S iOps fOps f ctx as vs :=
  ⟨by simpa using h 0 v rfl, fun i w hw => by simpa using h (i + 1) w (by simpa using hw)⟩

theorem holdsPT_nil_cons {v : V} {vs : List V} (h : HoldsPT S iOps fOps f ctx [] (v :: vs)) :
    HoldsPT S iOps fOps f ctx [] vs :=
  fun i w hw => by simpa using h (i + 1) w (by simpa using hw)

theorem holdsPT_replicate {a : AW} {vs : List V} (h : ∀ v ∈ vs, γT S iOps fOps f ctx a v) (n : Nat) :
    HoldsPT S iOps fOps f ctx (List.replicate n a) vs := by
  intro i v hv
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split
  · exact h v (List.mem_of_getElem? hv)
  · exact γT_top v

theorem holdsPT_single {a : AW} {v : V} (h : γT S iOps fOps f ctx a v) :
    HoldsPT S iOps fOps f ctx [a] [v] := by
  intro i w hw
  cases i with
  | zero => simp at hw; subst hw; exact h
  | succ i => simp at hw

theorem envOKT_empty (aenv : List AW) (n : Nat) : EnvOKT S iOps fOps f ctx aenv (Array.replicate n none) := by
  intro x w hx
  simp [Array.getElem?_replicate] at hx

theorem envOKT_set {aenv : List AW} {env : Isle.Interp.Env V}
    (he : EnvOKT S iOps fOps f ctx aenv env) {a : AW} {v : V} (hv : γT S iOps fOps f ctx a v) (x : Nat) :
    EnvOKT S iOps fOps f ctx (aenv.set x a) (env.set! x (some v)) := by
  intro y w hy
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at hy
  by_cases hyx : x = y
  · subst hyx
    simp only [↓reduceIte] at hy
    split at hy
    · cases hy
      rw [List.getD_eq_getElem?_getD, List.getElem?_set]
      simp only [↓reduceIte]
      split
      · exact hv
      · exact γT_top _
    · simp only [hyx, ↓reduceIte] at hy
      have := he y w hy
      rwa [List.getD_eq_getElem?_getD, List.getElem?_set_ne hyx, ← List.getD_eq_getElem?_getD]
  · simp only [hyx, ↓reduceIte] at hy
    have := he y w hy
    rwa [List.getD_eq_getElem?_getD, List.getElem?_set_ne hyx, ← List.getD_eq_getElem?_getD]

/-! ## Register kinds -/

/-- The register a value names has a kind of the abstract value's mask. -/
theorem mask_soundT {a : AW} {r : Reg} (h : γT S iOps fOps f ctx a (.reg r)) :
    r.kind &&& a.mask ≠ 0 := by
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
  | xv e => simp [γT, regsIn_reg] at h
  | alts as => simp only [AW.mask]; rcases kind_cases r with h | h | h | h <;> rw [h] <;> decide
  | data t k fs => obtain ⟨vs, he, -⟩ := h; cases he
  | num k b => rcases numOk_shape h with ⟨_, he⟩ | ⟨_, he⟩ <;> cases he

theorem isV_soundT {a : AW} (ha : a.isV = true) {r : Reg} (h : γT S iOps fOps f ctx a (.reg r)) :
    ∃ n, r = .vreg n .int := by
  have hm := mask_soundT h
  simp only [AW.isV, beq_iff_eq] at ha
  apply kind_int
  rcases kind_cases r with h1 | h1 | h1 | h1 <;> rw [h1] at hm ⊢ <;> try rfl
  all_goals exfalso; apply hm; apply Nat.eq_of_testBit_eq; intro i
  all_goals have := congrArg (·.testBit i) ha
  all_goals simp only [Nat.testBit_and] at this ⊢
  all_goals rcases i with _ | _ | _ | _ | i <;> simp_all [Nat.testBit_succ]

theorem isF_soundT {a : AW} (ha : a.isF = true) {r : Reg} (h : γT S iOps fOps f ctx a (.reg r)) :
    ∃ n, r = .vreg n .float := by
  have hm := mask_soundT h
  simp only [AW.isF, beq_iff_eq] at ha
  apply kind_float
  rcases kind_cases r with h1 | h1 | h1 | h1 <;> rw [h1] at hm ⊢ <;> try rfl
  all_goals exfalso; apply hm; apply Nat.eq_of_testBit_eq; intro i
  all_goals have := congrArg (·.testBit i) ha
  all_goals simp only [Nat.testBit_and] at this ⊢
  all_goals rcases i with _ | _ | _ | _ | i <;> simp_all [Nat.testBit_succ]

theorem isVZ_soundT {a : AW} (ha : a.isVZ = true) {r : Reg} (h : γT S iOps fOps f ctx a (.reg r)) :
    (∃ n, r = .vreg n .int) ∨ r = .xzr := by
  have hm := mask_soundT h
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

/-- A field-less enum value has one of the abstract value's variants. -/
theorem enumsOf_soundT {a : AW} {ks : List Nat} (ha : a.enumsOf = some ks) {v : V}
    (h : γT S iOps fOps f ctx a v) : ∃ t k, v = .data t k [] ∧ k ∈ ks := by
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
    obtain ⟨b, hb, hv⟩ := γAnyT_iff.mp h
    obtain ⟨t, k, rfl, hk⟩ := mapM_enum_mem ha b hb
    obtain ⟨vs, rfl, hl⟩ := hv
    cases vs with
    | nil => exact ⟨t, k, rfl, hk⟩
    | cons _ _ => exact hl.elim
  | _ => simp [AW.enumsOf] at ha

theorem enumAll_soundT {a : AW} {p : Nat → Bool} (ha : a.enumAll p = true) {v : V}
    (h : γT S iOps fOps f ctx a v) : ∃ t k, v = .data t k [] ∧ p k = true := by
  unfold AW.enumAll at ha
  split at ha
  · rename_i ks hks
    obtain ⟨t, k, rfl, hk⟩ := enumsOf_soundT hks h
    exact ⟨t, k, rfl, List.all_eq_true.mp ha k hk⟩
  · cases ha

/-! ## The driver's seeds -/

theorem γT_c0_inst (i : Nat) : γT S iOps fOps f ctx AW.c0 (.inst i) :=
  ⟨fun r hr => by simp [V.regsIn] at hr, fun _ => rfl⟩

theorem γT_c0_labels (ls : List Label) : γT S iOps fOps f ctx AW.c0 (.labels ls) :=
  ⟨fun r hr => by simp [V.regsIn] at hr, fun _ => rfl⟩

/-- A context instruction's data is the `.xv .inst` seed value. -/
theorem holds_instT {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) {ii : Nat} {info : IInfo}
    {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst) :
    Holds2T Compile.instET opsT floatOps f ctx [.xv .inst] [.inst ii] :=
  ⟨⟨⟨ii, info, inst, rfl, hi, hc, hctx.data _ _ _ hi hc⟩, rfl, rfl⟩, trivial⟩

end Backend.Proof.Cov
