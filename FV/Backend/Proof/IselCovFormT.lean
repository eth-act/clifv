import FV.Backend.Proof.IselCovForm
import FV.Backend.Proof.IselCovSemT

/-!
# Form coverage over float-capable contexts: the coverage check

The typed counterpart of `IselCovForm`: `covOk_soundT` and the shallow lemmas, over `γT`.
-/



/-!
# Form coverage of the ISLE lowering (V3): `covOk` is the abstract `FormOk`

`covOk_sound`: an `MInst` value of variant `k` whose fields `covOk k` accepts decodes
(`MInst.ofV`) to a covered instruction (`Covered`: `isCtl` or `FormOk`). The addressing modes
are `memOkA_sound`; the logical immediates `logicImm_of_ofNat` (`IselCovLogic`).
-/

namespace Backend.Proof.Cov

open Backend Backend.Proof Backend.Proof.Flow Isle Isle.Aarch64

gen_match_split amode_split Backend.V.amode?.match_1

variable {f : Clif.Function} {ctx : Ctx}

/-! ## Decoding fields -/

theorem V_ofT {a : AW} (ha : a.isV = true) {v : V} {r : Reg} (hv : γT S iOps fOps f ctx a v)
    (hr : v.reg? = some r) : ∃ n, r = .vreg n .int := by
  rw [reg?_eq hr] at hv; exact isV_sound ha hv

theorem F_ofT {a : AW} (ha : a.isF = true) {v : V} {r : Reg} (hv : γT S iOps fOps f ctx a v)
    (hr : v.reg? = some r) : ∃ n, r = .vreg n .float := by
  rw [reg?_eq hr] at hv; exact isF_sound ha hv

theorem VZ_ofT {a : AW} (ha : a.isVZ = true) {v : V} {r : Reg} (hv : γT S iOps fOps f ctx a v)
    (hr : v.reg? = some r) : (∃ n, r = .vreg n .int) ∨ r = .xzr := by
  rw [reg?_eq hr] at hv; exact isVZ_sound ha hv

theorem enum_ofT {a : AW} {p : Nat → Bool} (ha : a.enumAll p = true) {v : V} (hv : γT S iOps fOps f ctx a v)
    {α : Type} {ty : TypeId} {g : Nat → Option α} {x : α} (hx : V.enum? ty g v = some x) :
    ∃ k, g k = some x ∧ p k = true := by
  obtain ⟨t, k, rfl, hp⟩ := enumAll_sound ha hv
  obtain ⟨k', fs, he, hg⟩ := enum?_eq hx
  cases he
  exact ⟨k, hg, hp⟩

theorem addS_subST {a : AW} (ha : a.aluOpsIn [VIdx.ALUOp.AddS, VIdx.ALUOp.SubS] = true) {v : V}
    (hv : γT S iOps fOps f ctx a v) {op : ALUOp} (ho : v.aluOp? = some op) : op = .addS ∨ op = .subS := by
  obtain ⟨k, hg, hp⟩ := enum_of ha hv ho
  simp only [List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_true,
    beq_iff_eq] at hp
  rcases hp with rfl | rfl
  · simp [ALUOp.ofIdx?] at hg; exact .inl hg.symm
  · simp [ALUOp.ofIdx?] at hg; exact .inr hg.symm

theorem andS_ofT {a : AW} (ha : a.aluOpsIn [VIdx.ALUOp.AndS] = true) {v : V}
    (hv : γT S iOps fOps f ctx a v) {op : ALUOp} (ho : v.aluOp? = some op) : op = .andS := by
  obtain ⟨k, hg, hp⟩ := enum_of ha hv ho
  simp only [List.contains_cons, List.contains_nil, Bool.or_false, beq_iff_eq] at hp
  subst hp
  simp [ALUOp.ofIdx?] at hg; exact hg.symm

theorem opOk_ofT {a : AW} {q : ALUOp → Bool}
    (ha : a.enumAll (fun k => match ALUOp.ofIdx? k with | some o => q o | none => false) = true)
    {v : V} (hv : γT S iOps fOps f ctx a v) {op : ALUOp} (ho : v.aluOp? = some op) : q op = true := by
  obtain ⟨k, hg, hp⟩ := enum_of ha hv ho
  rw [hg] at hp
  exact hp

theorem extOk_ofT {a : AW}
    (ha : a.enumAll (fun k => match ExtendOp.ofIdx? k with
      | some e => decide (extOk e) | none => false) = true)
    {v : V} (hv : γT S iOps fOps f ctx a v) {e : ExtendOp} (ho : v.extendOp? = some e) : extOk e := by
  obtain ⟨k, hg, hp⟩ := enum_of ha hv ho
  rw [hg] at hp
  exact of_decide_eq_true hp

theorem size_ofT {a : AW} {sz : OperandSize} {k : Nat} (ha : a.enumsOf = some [k])
    (hk : (k == AW.sizeIdx sz) = true) {v : V} (hv : γT S iOps fOps f ctx a v) {s : OperandSize}
    (hs : v.size? = some s) : s = sz := by
  obtain ⟨t, k', rfl, hk'⟩ := enumsOf_sound ha hv
  simp only [List.mem_singleton] at hk'
  subst hk'
  simp only [beq_iff_eq] at hk
  subst hk
  obtain ⟨k'', fs, he, hg⟩ := enum?_eq hs
  cases he
  cases sz <;> simp [AW.sizeIdx, OperandSize.ofIdx?] at hg <;> exact hg.symm

/-! ## Addressing modes -/

theorem γL_cons {a : List AW} {v : V} {vs : List V} (h : γLT S iOps fOps f ctx a (v :: vs)) :
    ∃ b bs, a = b :: bs ∧ γT S iOps fOps f ctx b v ∧ γLT S iOps fOps f ctx bs vs := by
  cases a with
  | nil => exact h.elim
  | cons b bs => exact ⟨b, bs, rfl, h.1, h.2⟩

theorem γL_nil {a : List AW} (h : γLT S iOps fOps f ctx a []) : a = [] := by
  cases a with
  | nil => rfl
  | cons _ _ => exact h.elim

/-- Destructure the abstract field list along the value list. -/
syntax "fields" ident : tactic
set_option hygiene false in
macro_rules
  | `(tactic| fields $h) => `(tactic| (
    repeat (obtain ⟨_, _, rfl, _, $h:ident⟩ := γL_cons $h:ident)
    obtain rfl := γL_nil $h:ident))

theorem memRR_soundT {a b : AW} {v w : V} {r1 r2 : Reg} {mk : Reg → Reg → AMode}
    (hmk : ∀ n1 n2 bs, bs ∈ AW.allBytes → memOk bs (mk (.vreg n1 .int) (.vreg n2 .int)) = true)
    (h1 : v.reg? = some r1) (h2 : w.reg? = some r2) (hv : γT S iOps fOps f ctx a v) (hw : γT S iOps fOps f ctx b w) :
    MemFacts (AW.memRR [a, b]) (mk r1 r2) := by
  simp only [AW.memRR]
  split
  · rename_i hab
    simp only [Bool.and_eq_true] at hab
    obtain ⟨n1, rfl⟩ := V_of hab.1 hv h1
    obtain ⟨n2, rfl⟩ := V_of hab.2 hw h2
    exact ⟨fun bs hb => hmk n1 n2 bs (List.contains_iff_mem.mp hb), fun h => by cases h⟩
  · exact memFacts_nil _

theorem memRRE_soundT {a b c : AW} {v w u : V} {r1 r2 : Reg} {e : ExtendOp}
    {mk : Reg → Reg → ExtendOp → AMode}
    (hmk : ∀ n1 n2 e bs, extOk e → memOk bs (mk (.vreg n1 .int) (.vreg n2 .int) e) = true)
    (h1 : v.reg? = some r1) (h2 : w.reg? = some r2) (h3 : u.extendOp? = some e)
    (hv : γT S iOps fOps f ctx a v) (hw : γT S iOps fOps f ctx b w) (hu : γT S iOps fOps f ctx c u) :
    MemFacts (AW.memRRE [a, b, c]) (mk r1 r2 e) := by
  simp only [AW.memRRE]
  split
  · rename_i hab
    simp only [Bool.and_eq_true] at hab
    obtain ⟨⟨ha1, ha2⟩, ha3⟩ := hab
    obtain ⟨n1, rfl⟩ := V_of ha1 hv h1
    obtain ⟨n2, rfl⟩ := V_of ha2 hw h2
    exact ⟨fun bs _ => hmk n1 n2 e bs (extOk_of ha3 hu h3), fun h => by cases h⟩
  · exact memFacts_nil _

theorem memUnscaled_soundT {a b : AW} {v : V} {r : Reg} {i : Int} (h1 : v.reg? = some r)
    (hv : γT S iOps fOps f ctx a v) (hb : γT S iOps fOps f ctx b (.op (.simm9 i))) :
    MemFacts (AW.memUnscaled [a, b]) (.unscaled r i) := by
  cases b with
  | simm9 =>
    simp only [AW.memUnscaled]
    split
    · rename_i ha
      obtain ⟨n, rfl⟩ := V_of ha hv h1
      obtain ⟨i', he, hlo, hhi⟩ := hb
      cases he
      exact ⟨fun _ _ => by simp [memOk]; omega, fun h => by cases h⟩
    · exact memFacts_nil _
  | _ => simp only [AW.memUnscaled]; exact memFacts_nil _

theorem memUOff_soundT {a b : AW} {v : V} {r : Reg} {o : Nat} (h1 : v.reg? = some r)
    (hv : γT S iOps fOps f ctx a v) (hb : γT S iOps fOps f ctx b (.op (.uimm12Scaled o))) :
    MemFacts (AW.memUOff [a, b]) (.unsignedOffset r o) := by
  cases b with
  | scale b' =>
    simp only [AW.memUOff]
    split
    · rename_i ha
      obtain ⟨n, rfl⟩ := V_of ha hv h1
      obtain ⟨o', he, hm, hd⟩ := hb
      cases he
      refine ⟨fun bs hbs => ?_, fun h => by cases h⟩
      simp only [List.contains_cons, List.contains_nil, Bool.or_false, beq_iff_eq] at hbs
      subst hbs
      simp [memOk, hm, hd]
    · exact memFacts_nil _
  | _ => simp only [AW.memUOff]; exact memFacts_nil _

set_option maxHeartbeats 1000000 in
theorem memOk1_soundT {t k : Nat} {vs : List V} {am : AMode} (hm : (V.data t k vs).amode? = some am)
    {as : List AW} (hl : γLT S iOps fOps f ctx as vs) : MemFacts (AW.memOk1 k as) am := by
  unfold V.amode? at hm
  obtain ⟨⟨k', fs'⟩, he, h2⟩ := bind_some_ex hm
  clear hm
  simp only [V.enumOf?] at he
  split at he
  rotate_left
  · cases he
  cases he
  dsimp only at h2
  revert h2 am as
  apply amode_split _ (fun k vs (r : Option AMode) => ∀ {am : AMode} {as : List AW},
    γLT S iOps fOps f ctx as vs → r = some am → MemFacts (AW.memOk1 k as) am) k vs
  all_goals
    intros
    rename_i am as hl hm
    try simp only at hm
    repeat' (first | (obtain ⟨_, _, hm⟩ := bind_some_ex hm) | split at hm)
    all_goals try (cases hm; done)
  all_goals try (simp only [pure, Option.some.injEq] at hm; subst hm)
  all_goals fields hl
  all_goals first
    | (rw [memOk1_none rfl]; exact memFacts_nil _)
    | (rw [memOk1_eq rfl]
       refine ⟨fun _ _ => rfl, fun h => ?_⟩
       first | exact ⟨_, rfl⟩ | simp [AW.memAny] at h)
    | (rw [memOk1_eq rfl]
       apply memRR_sound (mk := AMode.regReg) <;> first | assumption | (intros; rfl))
    | (rw [memOk1_eq rfl]
       apply memRR_sound (mk := AMode.regScaled) <;> first | assumption | (intros; rfl))
    | (rw [memOk1_eq rfl]
       apply memRRE_sound (mk := AMode.regScaledExtended) <;>
         first | assumption | (intro _ _ _ _ he; simp [memOk, he]))
    | (rw [memOk1_eq rfl]
       apply memRRE_sound (mk := AMode.regExtended) <;>
         first | assumption | (intro _ _ _ _ he; simp [memOk, he]))
    | (rw [memOk1_eq rfl]
       apply memUnscaled_sound <;> assumption)
    | (rw [memOk1_eq rfl]
       apply memUOff_sound <;> assumption)

/-! ## Addressing modes of alternatives -/

/-- `q` is below `q'`. -/
theorem memOkA_soundT {a : AW} {v : V} (hv : γT S iOps fOps f ctx a v) {am : AMode} (hm : v.amode? = some am) :
    MemFacts (AW.memOkA a) am := by
  have one : ∀ x, γT S iOps fOps f ctx x v → MemFacts (memOne x) am := by
    intro x hx
    cases x with
    | data t k fs =>
      obtain ⟨vs, rfl, hl⟩ := hx
      exact memOk1_sound hm hl
    | _ => exact memFacts_nil am
  cases a with
  | data t k fs => exact one _ hv
  | alts as =>
    obtain ⟨x, hx, hxv⟩ := γAny_iff.mp hv
    rw [memOkA_alts]
    exact memFacts_sub (one x hxv) (memFold_sub_mem as _ x hx)
  | _ => exact memFacts_nil am

/-! ## Instructions, per variant -/

theorem notVT {a : AW} (e : a.isV = true) {v : V} (g : γT S iOps fOps f ctx a v) (r : v.reg? = some .xzr) : False := by
  obtain ⟨n, h⟩ := V_of e g r; cases h

/-- Close a coverage goal after the register shapes are known. -/
syntax "cov_close" : tactic
macro_rules
  | `(tactic| cov_close) => `(tactic| first
    | rfl
    | (exfalso; first
        | exact notVT ‹_› ‹_› ‹_›
        | (rename_i e; exact notVT e ‹_› ‹_›))
    | skip)

theorem cov_aluRRRT {a1 a2 a3 a4 a5 : AW} {v3 v4 v5 : V} {op : ALUOp} {s : OperandSize}
    {rd rn rm : Reg} (hc : AW.cAluRRR [a1, a2, a3, a4, a5] = true) (g3 : γT S iOps fOps f ctx a3 v3)
    (g4 : γT S iOps fOps f ctx a4 v4) (g5 : γT S iOps fOps f ctx a5 v5) (r3 : v3.reg? = some rd) (r4 : v4.reg? = some rn)
    (r5 : v5.reg? = some rm) : Covered (.aluRRR op s rd rn rm) = true := by
  simp only [AW.cAluRRR, Bool.and_eq_true, Bool.or_eq_true] at hc
  obtain ⟨⟨⟨⟨h3, h4⟩, h5⟩, e1⟩, e2⟩ := hc
  rcases VZ_of h3 g3 r3 with ⟨n3, rfl⟩ | rfl <;> rcases VZ_of h4 g4 r4 with ⟨n4, rfl⟩ | rfl <;>
    rcases VZ_of h5 g5 r5 with ⟨n5, rfl⟩ | rfl
  all_goals first
    | rfl
    | (exfalso
       rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2 <;>
         first | exact notV e1 g4 r4 | exact notV e1 g5 r5 | exact notV e2 g3 r3 | exact notV e2 g4 r4)

theorem cov_aluRRRRT {a1 a2 a3 a4 a5 a6 : AW} {v3 v4 v5 v6 : V} {op : ALUOp3} {s : OperandSize}
    {rd rn rm ra : Reg} (hc : AW.cAluRRRR [a1, a2, a3, a4, a5, a6] = true) (g3 : γT S iOps fOps f ctx a3 v3)
    (g4 : γT S iOps fOps f ctx a4 v4) (g5 : γT S iOps fOps f ctx a5 v5) (g6 : γT S iOps fOps f ctx a6 v6) (r3 : v3.reg? = some rd)
    (r4 : v4.reg? = some rn) (r5 : v5.reg? = some rm) (r6 : v6.reg? = some ra) :
    Covered (.aluRRRR op s rd rn rm ra) = true := by
  simp only [AW.cAluRRRR, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨h3, h4⟩, h5⟩, h6⟩ := hc
  obtain ⟨n3, rfl⟩ := V_of h3 g3 r3
  obtain ⟨n4, rfl⟩ := V_of h4 g4 r4
  obtain ⟨n5, rfl⟩ := V_of h5 g5 r5
  rcases VZ_of h6 g6 r6 with ⟨n6, rfl⟩ | rfl <;> rfl

theorem cov_aluRRImm12T {a1 a2 a3 a4 a5 : AW} {v1 v3 v4 : V} {op : ALUOp} {s : OperandSize}
    {rd rn : Reg} {i : Imm12} (hc : AW.cAluRRImm12 [a1, a2, a3, a4, a5] = true)
    (g1 : γT S iOps fOps f ctx a1 v1) (g3 : γT S iOps fOps f ctx a3 v3) (g4 : γT S iOps fOps f ctx a4 v4) (o1 : v1.aluOp? = some op)
    (r3 : v3.reg? = some rd) (r4 : v4.reg? = some rn) : Covered (.aluRRImm12 op s rd rn i) = true := by
  simp only [AW.cAluRRImm12, Bool.and_eq_true, Bool.or_eq_true] at hc
  obtain ⟨h4, h3⟩ := hc
  obtain ⟨n4, rfl⟩ := V_of h4 g4 r4
  rcases h3 with h3 | ⟨h3, ho⟩
  · obtain ⟨n3, rfl⟩ := V_of h3 g3 r3; rfl
  · rcases VZ_of h3 g3 r3 with ⟨n3, rfl⟩ | rfl
    · rfl
    · rcases addS_subS ho g1 o1 with rfl | rfl <;> rfl

theorem cov_aluRRImmLogicT {a1 a2 a3 a4 a5 : AW} {v1 v2 v3 v4 v5 : V} {op : ALUOp}
    {s : OperandSize} {rd rn : Reg} {i : ImmLogic} (hc : AW.cAluRRImmLogic [a1, a2, a3, a4, a5] = true)
    (g1 : γT S iOps fOps f ctx a1 v1) (g2 : γT S iOps fOps f ctx a2 v2) (g3 : γT S iOps fOps f ctx a3 v3) (g4 : γT S iOps fOps f ctx a4 v4)
    (g5 : γT S iOps fOps f ctx a5 v5) (o1 : v1.aluOp? = some op) (s2 : v2.size? = some s) (r3 : v3.reg? = some rd)
    (r4 : v4.reg? = some rn) (i5 : v5.immLogic? = some i) :
    Covered (.aluRRImmLogic op s rd rn i) = true := by
  simp only [AW.cAluRRImmLogic, Bool.and_eq_true, Bool.or_eq_true] at hc
  obtain ⟨⟨⟨⟨hl, h3⟩, h4⟩, e1⟩, e2⟩ := hc
  simp only [AW.logicOk, Bool.and_eq_true] at hl
  obtain ⟨hop, hsz⟩ := hl
  have hlo : logicOpOk op = true := opOk_of hop g1 o1
  obtain ⟨k, sz, hk, rfl, hks⟩ := logicSz_inv hsz
  · have hs := size_of hk hks g2 s2
    subst hs
    obtain ⟨i', he, -, hall⟩ := g5
    subst he
    simp only [V.immLogic?, Option.some.injEq] at i5
    subst i5
    have hli := hall op hlo
    rcases VZ_of h3 g3 r3 with ⟨n3, rfl⟩ | rfl <;> rcases VZ_of h4 g4 r4 with ⟨n4, rfl⟩ | rfl
    · simp [Covered, FormOk, hlo, hli]
    · simp [Covered, FormOk, hlo, hli]
    · rcases e1 with e1 | ⟨-, e1⟩
      · exact (notV e1 g3 r3).elim
      · have := andS_of e1 g1 o1; subst this; simp [Covered, FormOk, hli]
    · exfalso; rcases e2 with e2 | e2
      · exact notV e2 g4 r4
      · exact notV e2 g3 r3

theorem cov_aluRRImmShiftT {a1 a2 a3 a4 a5 : AW} {v1 v3 v4 : V} {op : ALUOp} {s : OperandSize}
    {rd rn : Reg} {i : Nat} (hc : AW.cAluRRImmShift [a1, a2, a3, a4, a5] = true)
    (g1 : γT S iOps fOps f ctx a1 v1) (g3 : γT S iOps fOps f ctx a3 v3) (g4 : γT S iOps fOps f ctx a4 v4) (o1 : v1.aluOp? = some op)
    (r3 : v3.reg? = some rd) (r4 : v4.reg? = some rn) :
    Covered (.aluRRImmShift op s rd rn i) = true := by
  simp only [AW.cAluRRImmShift, Bool.and_eq_true] at hc
  obtain ⟨⟨h3, h4⟩, h1⟩ := hc
  obtain ⟨n3, rfl⟩ := V_of h3 g3 r3
  obtain ⟨n4, rfl⟩ := V_of h4 g4 r4
  have := opOk_of h1 g1 o1
  simp [Covered, FormOk, this]

theorem cov_aluRRRShiftT {a1 a2 a3 a4 a5 a6 : AW} {v3 v4 v5 : V} {op : ALUOp} {s : OperandSize}
    {rd rn rm : Reg} {sh : ShiftOpAndAmt} (hc : AW.cAluRRRShift [a1, a2, a3, a4, a5, a6] = true)
    (g3 : γT S iOps fOps f ctx a3 v3) (g4 : γT S iOps fOps f ctx a4 v4) (g5 : γT S iOps fOps f ctx a5 v5) (r3 : v3.reg? = some rd)
    (r4 : v4.reg? = some rn) (r5 : v5.reg? = some rm) :
    Covered (.aluRRRShift op s rd rn rm sh) = true := by
  simp only [AW.cAluRRRShift, Bool.and_eq_true, Bool.or_eq_true] at hc
  obtain ⟨⟨⟨h3, h4⟩, h5⟩, e⟩ := hc
  obtain ⟨n5, rfl⟩ := V_of h5 g5 r5
  rcases VZ_of h3 g3 r3 with ⟨n3, rfl⟩ | rfl <;> rcases VZ_of h4 g4 r4 with ⟨n4, rfl⟩ | rfl
  all_goals first
    | rfl
    | (exfalso; rcases e with e | e
       · exact notV e g3 r3
       · exact notV e g4 r4)

theorem cov_aluRRRExtendT {a1 a2 a3 a4 a5 a6 : AW} {v1 v3 v4 v5 : V} {op : ALUOp} {s : OperandSize}
    {rd rn rm : Reg} {e : ExtendOp} (hc : AW.cAluRRRExtend [a1, a2, a3, a4, a5, a6] = true)
    (g1 : γT S iOps fOps f ctx a1 v1) (g3 : γT S iOps fOps f ctx a3 v3) (g4 : γT S iOps fOps f ctx a4 v4) (g5 : γT S iOps fOps f ctx a5 v5)
    (o1 : v1.aluOp? = some op) (r3 : v3.reg? = some rd) (r4 : v4.reg? = some rn)
    (r5 : v5.reg? = some rm) : Covered (.aluRRRExtend op s rd rn rm e) = true := by
  simp only [AW.cAluRRRExtend, Bool.and_eq_true, Bool.or_eq_true] at hc
  obtain ⟨⟨h4, h5⟩, h3⟩ := hc
  obtain ⟨n4, rfl⟩ := V_of h4 g4 r4
  obtain ⟨n5, rfl⟩ := V_of h5 g5 r5
  rcases h3 with h3 | ⟨h3, ho⟩
  · obtain ⟨n3, rfl⟩ := V_of h3 g3 r3; rfl
  · rcases VZ_of h3 g3 r3 with ⟨n3, rfl⟩ | rfl
    · rfl
    · rcases addS_subS ho g1 o1 with rfl | rfl <;> rfl

section simple
variable {a1 a2 a3 a4 a5 a6 : AW} {v1 v2 v3 v4 v5 : V}

theorem cov_bitRRT {op : BitOp} {s : OperandSize} {rd rn : Reg} (hc : AW.cOp2 [a1, a2, a3, a4] = true)
    (g3 : γT S iOps fOps f ctx a3 v3) (g4 : γT S iOps fOps f ctx a4 v4) (r3 : v3.reg? = some rd) (r4 : v4.reg? = some rn) :
    Covered (.bitRR op s rd rn) = true := by
  simp only [AW.cOp2, Bool.and_eq_true] at hc
  obtain ⟨_, rfl⟩ := V_of hc.1 g3 r3; obtain ⟨_, rfl⟩ := V_of hc.2 g4 r4; rfl

theorem cov_movT {s : OperandSize} {rd rm : Reg} (hc : AW.cMov [a1, a2, a3] = true)
    (g2 : γT S iOps fOps f ctx a2 v2) (g3 : γT S iOps fOps f ctx a3 v3) (r2 : v2.reg? = some rd) (r3 : v3.reg? = some rm) :
    Covered (.mov s rd rm) = true := by
  simp only [AW.cMov, Bool.and_eq_true] at hc
  obtain ⟨_, rfl⟩ := V_of hc.1 g2 r2; obtain ⟨_, rfl⟩ := V_of hc.2 g3 r3; rfl

theorem cov_movWideT {op : MoveWideOp} {s : OperandSize} {rd : Reg} {i : MoveWideConst}
    (hc : AW.cMovWide [a1, a2, a3, a4] = true) (g2 : γT S iOps fOps f ctx a2 v2) (r2 : v2.reg? = some rd) :
    Covered (.movWide op rd i s) = true := by
  simp only [AW.cMovWide] at hc
  obtain ⟨_, rfl⟩ := V_of hc g2 r2; rfl

theorem cov_movKT {s : OperandSize} {rd rn : Reg} {i : MoveWideConst}
    (hc : AW.cMovK [a1, a2, a3, a4] = true) (g1 : γT S iOps fOps f ctx a1 v1) (g2 : γT S iOps fOps f ctx a2 v2)
    (r1 : v1.reg? = some rd) (r2 : v2.reg? = some rn) : Covered (.movK rd rn i s) = true := by
  simp only [AW.cMovK, Bool.and_eq_true] at hc
  obtain ⟨_, rfl⟩ := V_of hc.1 g1 r1; obtain ⟨_, rfl⟩ := V_of hc.2 g2 r2; rfl

theorem cov_extendT {rd rn : Reg} {sg : Bool} {a b : Nat} (hc : AW.cExtend [a1, a2, a3, a4, a5] = true)
    (g1 : γT S iOps fOps f ctx a1 v1) (g2 : γT S iOps fOps f ctx a2 v2) (r1 : v1.reg? = some rd) (r2 : v2.reg? = some rn) :
    Covered (.extend rd rn sg a b) = true := by
  simp only [AW.cExtend, Bool.and_eq_true] at hc
  obtain ⟨_, rfl⟩ := V_of hc.1 g1 r1; obtain ⟨_, rfl⟩ := V_of hc.2 g2 r2; rfl

theorem cov_bfmT {s : OperandSize} {op : BfmOp} {rd rn : Reg} {a b : Nat}
    (hc : AW.cBfm [a1, a2, a3, a4, a5, a6] = true) (g3 : γT S iOps fOps f ctx a3 v3) (g4 : γT S iOps fOps f ctx a4 v4)
    (r3 : v3.reg? = some rd) (r4 : v4.reg? = some rn) : Covered (.bitfieldMove s op rd rn a b) = true := by
  simp only [AW.cBfm, Bool.and_eq_true] at hc
  obtain ⟨_, rfl⟩ := V_of hc.1 g3 r3; obtain ⟨_, rfl⟩ := V_of hc.2 g4 r4; rfl

theorem cov_csetT {rd : Reg} {c : Cond} (hc : AW.cCSet [a1, a2] = true) (g1 : γT S iOps fOps f ctx a1 v1)
    (r1 : v1.reg? = some rd) : Covered (.cset rd c) = true := by
  simp only [AW.cCSet] at hc
  obtain ⟨_, rfl⟩ := V_of hc g1 r1; rfl

theorem cov_csetmT {rd : Reg} {c : Cond} (hc : AW.cCSet [a1, a2] = true) (g1 : γT S iOps fOps f ctx a1 v1)
    (r1 : v1.reg? = some rd) : Covered (.csetm rd c) = true := by
  simp only [AW.cCSet] at hc
  obtain ⟨_, rfl⟩ := V_of hc g1 r1; rfl

theorem cov_cselT {rd rn rm : Reg} {c : Cond} (hc : AW.cCSel [a1, a2, a3, a4] = true)
    (g1 : γT S iOps fOps f ctx a1 v1) (g3 : γT S iOps fOps f ctx a3 v3) (g4 : γT S iOps fOps f ctx a4 v4) (r1 : v1.reg? = some rd)
    (r3 : v3.reg? = some rn) (r4 : v4.reg? = some rm) : Covered (.csel rd rn rm c) = true := by
  simp only [AW.cCSel, Bool.and_eq_true] at hc
  obtain ⟨⟨h1, h3⟩, h4⟩ := hc
  obtain ⟨_, rfl⟩ := V_of h1 g1 r1; obtain ⟨_, rfl⟩ := V_of h3 g3 r3
  obtain ⟨_, rfl⟩ := V_of h4 g4 r4; rfl

theorem cov_ccmpT {s : OperandSize} {rn rm : Reg} {nz : NZCV} {c : Cond}
    (hc : AW.cCCmp [a1, a2, a3, a4, a5] = true) (g2 : γT S iOps fOps f ctx a2 v2) (g3 : γT S iOps fOps f ctx a3 v3)
    (r2 : v2.reg? = some rn) (r3 : v3.reg? = some rm) : Covered (.ccmp s rn rm nz c) = true := by
  simp only [AW.cCCmp, Bool.and_eq_true] at hc
  obtain ⟨_, rfl⟩ := V_of hc.1 g2 r2; obtain ⟨_, rfl⟩ := V_of hc.2 g3 r3; rfl

theorem cov_ccmpImmT {s : OperandSize} {rn : Reg} {i : Nat} {nz : NZCV} {c : Cond}
    (hc : AW.cCCmpImm [a1, a2, a3, a4, a5] = true) (g2 : γT S iOps fOps f ctx a2 v2)
    (r2 : v2.reg? = some rn) : Covered (.ccmpImm s rn i nz c) = true := by
  simp only [AW.cCCmpImm] at hc
  obtain ⟨_, rfl⟩ := V_of hc g2 r2; rfl

theorem cov_movToFpuT {rd rn : Reg} {s : ScalarSize} (hc : AW.cMovToFpu [a1, a2, a3] = true)
    (g1 : γT S iOps fOps f ctx a1 v1) (g2 : γT S iOps fOps f ctx a2 v2) (r1 : v1.reg? = some rd) (r2 : v2.reg? = some rn) :
    Covered (.movToFpu rd rn s) = true := by
  simp only [AW.cMovToFpu, Bool.and_eq_true] at hc
  obtain ⟨_, rfl⟩ := F_of hc.1 g1 r1; obtain ⟨_, rfl⟩ := V_of hc.2 g2 r2; rfl

theorem cov_movFromVecT {rd rn : Reg} {i : Nat} {s : ScalarSize}
    (hc : AW.cMovFromVec [a1, a2, a3, a4] = true) (g1 : γT S iOps fOps f ctx a1 v1) (g2 : γT S iOps fOps f ctx a2 v2)
    (r1 : v1.reg? = some rd) (r2 : v2.reg? = some rn) : Covered (.movFromVec rd rn i s) = true := by
  simp only [AW.cMovFromVec, Bool.and_eq_true] at hc
  obtain ⟨_, rfl⟩ := V_of hc.1 g1 r1; obtain ⟨_, rfl⟩ := F_of hc.2 g2 r2; rfl

theorem cov_vecMiscT {op : VecMisc2} {rd rn : Reg} {s : VectorSize}
    (hc : AW.cVec2 [a1, a2, a3, a4] = true) (g2 : γT S iOps fOps f ctx a2 v2) (g3 : γT S iOps fOps f ctx a3 v3)
    (r2 : v2.reg? = some rd) (r3 : v3.reg? = some rn) : Covered (.vecMisc op rd rn s) = true := by
  simp only [AW.cVec2, Bool.and_eq_true] at hc
  obtain ⟨_, rfl⟩ := F_of hc.1 g2 r2; obtain ⟨_, rfl⟩ := F_of hc.2 g3 r3; rfl

theorem cov_vecLanesT {op : VecLanesOp} {rd rn : Reg} {s : VectorSize}
    (hc : AW.cVec2 [a1, a2, a3, a4] = true) (g2 : γT S iOps fOps f ctx a2 v2) (g3 : γT S iOps fOps f ctx a3 v3)
    (r2 : v2.reg? = some rd) (r3 : v3.reg? = some rn) : Covered (.vecLanes op rd rn s) = true := by
  simp only [AW.cVec2, Bool.and_eq_true] at hc
  obtain ⟨_, rfl⟩ := F_of hc.1 g2 r2; obtain ⟨_, rfl⟩ := F_of hc.2 g3 r3; rfl

theorem cov_vecRRRT {op : VecALUOp} {rd rn rm : Reg} {s : VectorSize}
    (hc : AW.cVecRRR [a1, a2, a3, a4, a5] = true) (g2 : γT S iOps fOps f ctx a2 v2) (g3 : γT S iOps fOps f ctx a3 v3)
    (g4 : γT S iOps fOps f ctx a4 v4) (r2 : v2.reg? = some rd) (r3 : v3.reg? = some rn) (r4 : v4.reg? = some rm) :
    Covered (.vecRRR op rd rn rm s) = true := by
  simp only [AW.cVecRRR, Bool.and_eq_true] at hc
  obtain ⟨⟨h2, h3⟩, h4⟩ := hc
  obtain ⟨_, rfl⟩ := F_of h2 g2 r2; obtain ⟨_, rfl⟩ := F_of h3 g3 r3
  obtain ⟨_, rfl⟩ := F_of h4 g4 r4; rfl

theorem cov_loadAddrT {rd : Reg} {am : AMode} (hc : AW.cLoadAddr [a1, a2] = true)
    (g1 : γT S iOps fOps f ctx a1 v1) (g2 : γT S iOps fOps f ctx a2 v2) (r1 : v1.reg? = some rd) (m2 : v2.amode? = some am) :
    Covered (.loadAddr rd am) = true := by
  simp only [AW.cLoadAddr, Bool.and_eq_true] at hc
  obtain ⟨_, rfl⟩ := V_of hc.1 g1 r1
  obtain ⟨o, rfl⟩ := (memOkA_sound g2 m2).2 hc.2
  rfl

theorem atom_ofT {a : AW} (ha : AW.atomOk a = true) {v : V} (hv : γT S iOps fOps f ctx a v) {t : CTy}
    (ht : v.ty? = some t) : AtomTy t := by
  cases a with
  | ty ts =>
    obtain ⟨t', ht', rfl⟩ := hv
    simp only [V.ty?, Option.some.injEq] at ht
    subst ht
    simp only [AW.atomOk, List.all_eq_true, decide_eq_true_eq] at ha
    exact ha _ ht'
  | _ => simp [AW.atomOk] at ha

theorem cov_loadAcquireT {ty : CTy} {rt rn : Reg} {fl : Clif.MemFlags}
    (hc : AW.cAtomic [a1, a2, a3, a4] = true) (g1 : γT S iOps fOps f ctx a1 v1) (g2 : γT S iOps fOps f ctx a2 v2)
    (g3 : γT S iOps fOps f ctx a3 v3) (t1 : v1.ty? = some ty) (r2 : v2.reg? = some rt) (r3 : v3.reg? = some rn) :
    Covered (.loadAcquire ty rt rn fl) = true := by
  simp only [AW.cAtomic, Bool.and_eq_true] at hc
  obtain ⟨⟨h1, h2⟩, h3⟩ := hc
  have := atom_of h1 g1 t1
  obtain ⟨_, rfl⟩ := V_of h2 g2 r2; obtain ⟨_, rfl⟩ := V_of h3 g3 r3
  simp [Covered, FormOk, this]

theorem cov_storeReleaseT {ty : CTy} {rt rn : Reg} {fl : Clif.MemFlags}
    (hc : AW.cAtomic [a1, a2, a3, a4] = true) (g1 : γT S iOps fOps f ctx a1 v1) (g2 : γT S iOps fOps f ctx a2 v2)
    (g3 : γT S iOps fOps f ctx a3 v3) (t1 : v1.ty? = some ty) (r2 : v2.reg? = some rt) (r3 : v3.reg? = some rn) :
    Covered (.storeRelease ty rt rn fl) = true := by
  simp only [AW.cAtomic, Bool.and_eq_true] at hc
  obtain ⟨⟨h1, h2⟩, h3⟩ := hc
  have := atom_of h1 g1 t1
  obtain ⟨_, rfl⟩ := V_of h2 g2 r2; obtain ⟨_, rfl⟩ := V_of h3 g3 r3
  simp [Covered, FormOk, this]


theorem cov_fpuCSelT {sz : ScalarSize} {rd rn rm : Reg} {c : Cond}
    (hc : AW.cFpuCSel [a1, a2, a3, a4] = true) (g1 : γT S iOps fOps f ctx a1 v1) (g2 : γT S iOps fOps f ctx a2 v2)
    (g3 : γT S iOps fOps f ctx a3 v3) (r1 : v1.reg? = some rd) (r2 : v2.reg? = some rn) (r3 : v3.reg? = some rm) :
    Covered (.fpuCSel sz rd rn rm c) = true := by
  simp only [AW.cFpuCSel, Bool.and_eq_true] at hc
  obtain ⟨⟨h1, h2⟩, h3⟩ := hc
  obtain ⟨_, rfl⟩ := F_of h1 g1 r1; obtain ⟨_, rfl⟩ := F_of h2 g2 r2
  obtain ⟨_, rfl⟩ := F_of h3 g3 r3; rfl

theorem cov_fpuMoveFPImmT {rd : Reg} {imm : ASIMDFPModImm} {sz : ScalarSize}
    (hc : AW.cFpuMoveFPImm [a1, a2, a3] = true) (g1 : γT S iOps fOps f ctx a1 v1) (r1 : v1.reg? = some rd) :
    Covered (.fpuMoveFPImm rd imm sz) = true := by
  simp only [AW.cFpuMoveFPImm] at hc
  obtain ⟨_, rfl⟩ := F_of hc g1 r1; rfl
end simple

/-! ## Loads and stores -/

theorem cov_loadT {k : Nat} {op : LoadOp} (hk : loadOpOfIdx? k = some op) {a1 a2 a3 : AW}
    {v1 v2 : V} {rd : Reg} {am : AMode} {fl : Clif.MemFlags} (hc : AW.covOk k [a1, a2, a3] = true)
    (g1 : γT S iOps fOps f ctx a1 v1) (g2 : γT S iOps fOps f ctx a2 v2) (r1 : v1.reg? = some rd) (m2 : v2.amode? = some am) :
    Covered (.load op rd am fl) = true := by
  obtain ⟨hl, hne⟩ := lookup_load hk
  rw [covOk_none hl] at hc
  simp only [AW.cMem, hk, Bool.and_eq_true] at hc
  obtain ⟨_, rfl⟩ := V_of hc.1 g1 r1
  have := (memOkA_sound g2 m2).1 _ hc.2
  simp [Covered, FormOk, hne, this]

theorem cov_storeT {k : Nat} {op : StoreOp} (hk : storeOpOfIdx? k = some op)
    (hk' : loadOpOfIdx? k = none) {a1 a2 a3 : AW}
    {v1 v2 : V} {rd : Reg} {am : AMode} {fl : Clif.MemFlags} (hc : AW.covOk k [a1, a2, a3] = true)
    (g1 : γT S iOps fOps f ctx a1 v1) (g2 : γT S iOps fOps f ctx a2 v2) (r1 : v1.reg? = some rd) (m2 : v2.amode? = some am) :
    Covered (.store op rd am fl) = true := by
  obtain ⟨hl, hne⟩ := lookup_store hk
  rw [covOk_none hl] at hc
  simp only [AW.cMem, hk, hk', Bool.and_eq_true] at hc
  obtain ⟨_, rfl⟩ := V_of hc.1 g1 r1
  have := (memOkA_sound g2 m2).1 _ hc.2
  simp [Covered, FormOk, hne, this]

/-! ## The coverage theorem -/

set_option maxHeartbeats 4000000 in
/-- **`covOk` is the abstract `FormOk`**: an `MInst` value of variant `k` whose fields `covOk`
accepts decodes to a covered instruction. -/
theorem covOk_soundT {t k : Nat} {as : List AW} {vs : List V} (hc : AW.covOk k as = true)
    (hl : γLT S iOps fOps f ctx as vs) {i : MInst} (h : MInst.ofV (.data t k vs) = some i) : Covered i = true := by
  unfold MInst.ofV at h
  obtain ⟨⟨k', fs'⟩, he, h2⟩ := bind_some_ex h
  clear h
  simp only [V.enumOf?] at he
  split at he
  rotate_left
  · cases he
  cases he
  dsimp only at h2
  revert h2 i as hc hl
  apply ofV_split _ (fun k vs (r : Option MInst) => ∀ {as : List AW}, AW.covOk k as = true →
    γLT S iOps fOps f ctx as vs → ∀ {i : MInst}, r = some i → Covered i = true) k vs
  all_goals
    intros
    rename_i as hc hl i hm
    try simp only at hm
    repeat' (first | (obtain ⟨_, _, hm⟩ := bind_some_ex hm) | split at hm)
    all_goals try (cases hm; done)
  all_goals try (simp only [pure, Option.some.injEq] at hm; subst hm)
  all_goals first
    | rfl
    | skip
  all_goals fields hl
  all_goals first
    | (apply cov_load (by assumption) hc <;> assumption)
    | (apply cov_store (by assumption) (by assumption) hc <;> assumption)
    | skip
  all_goals first
    | done
    | (rw [covOk_none rfl] at hc
       simp [AW.cMem, loadOpOfIdx?, storeOpOfIdx?] at hc
       done)
    | (rw [covOk_eq rfl] at hc
       first
       | (apply cov_aluRRR hc <;> assumption)
       | (apply cov_aluRRRR hc <;> assumption)
       | (apply cov_aluRRImm12 hc <;> assumption)
       | (apply cov_aluRRImmLogic hc <;> assumption)
       | (apply cov_aluRRImmShift hc <;> assumption)
       | (apply cov_aluRRRShift hc <;> assumption)
       | (apply cov_aluRRRExtend hc <;> assumption)
       | (apply cov_bitRR hc <;> assumption)
       | (apply cov_mov hc <;> assumption)
       | (apply cov_movWide hc <;> assumption)
       | (apply cov_movK hc <;> assumption)
       | (apply cov_extend hc <;> assumption)
       | (apply cov_bfm hc <;> assumption)
       | (apply cov_cset hc <;> assumption)
       | (apply cov_csetm hc <;> assumption)
       | (apply cov_csel hc <;> assumption)
       | (apply cov_ccmp hc <;> assumption)
       | (apply cov_ccmpImm hc <;> assumption)
       | (apply cov_movToFpu hc <;> assumption)
       | (apply cov_movFromVec hc <;> assumption)
       | (apply cov_vecMisc hc <;> assumption)
       | (apply cov_vecLanes hc <;> assumption)
       | (apply cov_vecRRR hc <;> assumption)
       | (apply cov_loadAddr hc <;> assumption)
       | (apply cov_loadAcquire hc <;> assumption)
       | (apply cov_storeRelease hc <;> assumption)
       | (apply cov_fpuCSel hc <;> assumption)
       | (apply cov_fpuMoveFPImm hc <;> assumption))
