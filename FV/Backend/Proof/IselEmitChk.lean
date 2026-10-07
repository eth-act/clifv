import FV.Backend.Proof.IselEmitFns
import FV.Backend.Proof.IselCovForm

/-!
# Emission conditions of the ISLE lowering (V6c): the emission check is sound

`emChk_sound`: an instruction value the abstract emission check `emChk nb` accepts decodes
(`MInst.ofV`, as `emit` does) to an instruction with the emission conditions (`MInst.emitOk`), and
without branch targets if `nb`. `senrLast_sound`: the instructions of a side effect `senrLast`
accepts have the emission conditions, branch targets only on the last one (`SenrOk`).
-/

namespace Backend.Proof.Cov

open Backend Backend.Proof Backend.Proof.Flow Isle Isle.Aarch64

variable {f : Clif.Function} {ctx : Ctx}

/-! ## Leaves, sizes, conditions -/

theorem leafLe_sound {k : NK} {a : AW} {n : Nat} (h : leafLe k a n = true) {v : V}
    (hv : γ f ctx a v) : NumOk k n v := by
  cases a with
  | num k' b =>
    simp only [leafLe, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨rfl, hb⟩ := h
    exact numOk_mono hb hv
  | _ => simp [leafLe] at h

/-- `sizeBnd` bounds by the width of the decoded operand size. -/
theorem sizeBnd_lt {s : AW} {v : V} (hv : γ f ctx s v) {sz : OperandSize} (h : v.size? = some sz)
    {x : Nat} (hx : x < sizeBnd s) : x < (if sz.is64 then 64 else 32) := by
  unfold sizeBnd at hx
  split at hx
  · rename_i ks hks
    split at hx
    · rename_i hall
      obtain ⟨t, k, rfl, hk⟩ := enumsOf_sound hks hv
      have := List.all_eq_true.mp hall k hk
      simp only [beq_iff_eq] at this
      subst this
      obtain ⟨k', fs, he, hg⟩ := enum?_eq h
      cases he
      cases sz
      · exact absurd hg (by decide)
      · exact hx
    · split <;> omega
  · split <;> omega

theorem sizeBnd_mwc {s : AW} {v : V} (hv : γ f ctx s v) {sz : OperandSize} (h : v.size? = some sz)
    {x : Nat} (hx : x < (if sizeBnd s == 64 then 4 else 2)) : x < (if sz.is64 then 4 else 2) := by
  split at hx
  · rename_i h64
    have := sizeBnd_lt hv h (x := 63) (by simp only [beq_iff_eq] at h64; omega)
    split at this
    · simp only [*, ite_true]
    · omega
  · split <;> omega

theorem cond_idx : ∀ {k : Nat} {c : Cond}, Cond.ofIdx? k = some c → c.idx = k := by
  intro k c h
  unfold Cond.ofIdx? at h
  split at h <;> cases h <;> rfl

theorem condA_sound {a : AW} (ha : condA a = true) {v : V} (hv : γ f ctx a v) {c : Cond}
    (hc : v.cond? = some c) : c ≠ .al ∧ c ≠ .nv := by
  obtain ⟨k, hg, hp⟩ := enum_of ha hv hc
  have hk := cond_idx hg
  subst hk
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hp
  exact ⟨fun h => hp.1 (by rw [h]), fun h => hp.2 (by rw [h])⟩

theorem condBrKind_cond {t : TypeId} {k : Nat} {vs : List V} {c : Cond}
    (h : (V.data t k vs).condBrKind? = some (.cond c)) :
    k = VIdx.CondBrKind.Cond ∧ ∃ w, vs = [w] ∧ w.cond? = some c := by
  unfold V.condBrKind? at h
  obtain ⟨⟨k', fs⟩, he, h2⟩ := bind_some_ex h
  have he' := enumOf_eq he
  cases he'
  dsimp only at h2
  split at h2
  · obtain ⟨_, _, h2⟩ := bind_some_ex h2
    obtain ⟨_, _, h2⟩ := bind_some_ex h2
    cases h2
  · obtain ⟨_, _, h2⟩ := bind_some_ex h2
    obtain ⟨_, _, h2⟩ := bind_some_ex h2
    cases h2
  · obtain ⟨c', hc', h2⟩ := bind_some_ex h2
    cases h2
    exact ⟨rfl, _, rfl, hc'⟩
  · cases h2

theorem kindE1_sound {a : AW} (ha : kindE1 a = true) {v : V} (hv : γ f ctx a v) {c : Cond}
    (h : v.condBrKind? = some (.cond c)) : c ≠ .al ∧ c ≠ .nv := by
  match a, ha, hv with
  | .data t k fs, ha, hv =>
    obtain ⟨vs, rfl, hl⟩ := hv
    obtain ⟨rfl, w, rfl, hw⟩ := condBrKind_cond h
    obtain ⟨b, bs, rfl, hb, hbs⟩ := γL_cons hl
    obtain rfl := γL_nil hbs
    simp only [kindE1, beq_self_eq_true, ite_true] at ha
    exact condA_sound ha hb hw

theorem kindE_sound {a : AW} (ha : kindE a = true) {v : V} (hv : γ f ctx a v) {c : Cond}
    (h : v.condBrKind? = some (.cond c)) : c ≠ .al ∧ c ≠ .nv := by
  cases a with
  | alts as =>
    simp only [kindE, List.all_eq_true] at ha
    obtain ⟨b, hb, hbv⟩ := γAny_iff.mp hv
    exact kindE1_sound (ha b hb) hbv h
  | _ => exact kindE1_sound (by simpa only [kindE] using ha) hv h

/-- The condition of a decoded `CondBrKind` the check accepts is not `al`/`nv`. -/
theorem kind_noAlways {a : AW} (ha : kindE a = true) {v : V} (hv : γ f ctx a v) {kd : CondBrKind}
    (h : v.condBrKind? = some kd) : ∀ c, kd = .cond c → !(c == .al || c == .nv) = true := by
  intro c hc
  subst hc
  obtain ⟨h1, h2⟩ := kindE_sound ha hv h
  cases c <;> simp_all

/-! ## The checked variants -/

section variants
variable {a1 a2 a3 a4 a5 a6 : AW} {v1 v2 v3 v4 v5 v6 : V}

theorem ec_aluRRImm12 {op : ALUOp} {s : OperandSize} {rd rn : Reg} {i : Imm12}
    (hc : eAluRRImm12 [a1, a2, a3, a4, a5] = true) (g1 : γ f ctx a1 v1) (g5 : γ f ctx a5 v5)
    (o1 : v1.aluOp? = some op) (i5 : v5.imm12? = some i) :
    (MInst.aluRRImm12 op s rd rn i).emitOk = true := by
  simp only [eAluRRImm12, Bool.and_eq_true] at hc
  have h1 := opOk_of (q := fun o => o.addSub?.isSome) hc.1 g1 o1
  obtain ⟨i', rfl, hb⟩ := leafLe_sound hc.2 g5
  simp only [V.imm12?, Option.some.injEq] at i5
  subst i5
  simp only [MInst.emitOk, immOkB, MInst.noAlways, h1, Bool.true_and, Bool.and_true,
    decide_eq_true_eq]
  omega

theorem ec_aluRRImmShift {op : ALUOp} {s : OperandSize} {rd rn : Reg} {n : Nat}
    (hc : eAluRRImmShift [a1, a2, a3, a4, a5] = true) (g2 : γ f ctx a2 v2) (g5 : γ f ctx a5 v5)
    (s2 : v2.size? = some s) (i5 : v5.immShift? = some n) :
    (MInst.aluRRImmShift op s rd rn n).emitOk = true := by
  simp only [eAluRRImmShift] at hc
  obtain ⟨n', rfl, hb⟩ := leafLe_sound hc g5
  simp only [V.immShift?, Option.some.injEq] at i5
  subst i5
  simp only [MInst.emitOk, immOkB, MInst.noAlways, Bool.and_true, decide_eq_true_eq]
  exact sizeBnd_lt g2 s2 hb

theorem ec_aluRRRShift {op : ALUOp} {s : OperandSize} {rd rn rm : Reg} {sh : ShiftOpAndAmt}
    (hc : eAluRRRShift [a1, a2, a3, a4, a5, a6] = true) (g1 : γ f ctx a1 v1) (g2 : γ f ctx a2 v2)
    (g6 : γ f ctx a6 v6) (o1 : v1.aluOp? = some op) (s2 : v2.size? = some s)
    (i6 : v6.shiftOpAndAmt? = some sh) :
    (MInst.aluRRRShift op s rd rn rm sh).emitOk = true := by
  simp only [eAluRRRShift, Bool.and_eq_true] at hc
  obtain ⟨sh', rfl, hb, hr⟩ := leafLe_sound hc.1 g6
  have h1 := opOk_of (q := fun o => o == .extr || o.addSub?.isSome || o.logic?.isSome) hc.2 g1 o1
  simp only [V.shiftOpAndAmt?, Option.some.injEq] at i6
  subst i6
  have hlt := sizeBnd_lt g2 s2 hb
  simp only [MInst.emitOk, immOkB, MInst.noAlways, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq]
  refine ⟨hlt, ?_⟩
  simp only [Bool.or_eq_true] at h1 ⊢
  have hr' : (sh'.op != .ror) = true := by simpa using hr
  rcases h1 with (h | h) | h
  · exact .inl (.inl h)
  · exact .inl (.inr (by simp [h, hr']))
  · exact .inr h

theorem ec_aluRRRExtend {op : ALUOp} {s : OperandSize} {rd rn rm : Reg} {e : ExtendOp}
    (hc : eAluRRRExtend [a1, a2, a3, a4, a5, a6] = true) (g1 : γ f ctx a1 v1)
    (o1 : v1.aluOp? = some op) : (MInst.aluRRRExtend op s rd rn rm e).emitOk = true := by
  simp only [eAluRRRExtend] at hc
  have h1 := opOk_of (q := fun o => o.addSub?.isSome) hc g1 o1
  simp only [MInst.emitOk, immOkB, MInst.noAlways, Bool.and_true]
  exact h1

theorem ec_mwc {s : OperandSize} {i : MoveWideConst} (hc : eMovWide [a1, a2, a3, a4] = true)
    (g3 : γ f ctx a3 v3) (g4 : γ f ctx a4 v4) (i3 : v3.moveWideConst? = some i)
    (s4 : v4.size? = some s) : i.bits < 2 ^ 16 ∧ i.shift < (if s.is64 then 4 else 2) := by
  simp only [eMovWide] at hc
  obtain ⟨i', rfl, hb, hs⟩ := leafLe_sound hc g3
  simp only [V.moveWideConst?, Option.some.injEq] at i3
  subst i3
  exact ⟨hb, sizeBnd_mwc g4 s4 hs⟩

theorem ec_movWide {op : MoveWideOp} {rd : Reg} {s : OperandSize} {i : MoveWideConst}
    (hc : eMovWide [a1, a2, a3, a4] = true) (g3 : γ f ctx a3 v3) (g4 : γ f ctx a4 v4)
    (i3 : v3.moveWideConst? = some i) (s4 : v4.size? = some s) :
    (MInst.movWide op rd i s).emitOk = true := by
  obtain ⟨h1, h2⟩ := ec_mwc hc g3 g4 i3 s4
  simp only [MInst.emitOk, immOkB, MInst.noAlways, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq]
  exact ⟨h1, h2⟩

theorem ec_movK {rd rn : Reg} {s : OperandSize} {i : MoveWideConst}
    (hc : eMovWide [a1, a2, a3, a4] = true) (g3 : γ f ctx a3 v3) (g4 : γ f ctx a4 v4)
    (i3 : v3.moveWideConst? = some i) (s4 : v4.size? = some s) :
    (MInst.movK rd rn i s).emitOk = true := by
  obtain ⟨h1, h2⟩ := ec_mwc hc g3 g4 i3 s4
  simp only [MInst.emitOk, immOkB, MInst.noAlways, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq]
  exact ⟨h1, h2⟩

theorem ec_extend {rd rn : Reg} {sg : Bool} {a b : Nat}
    (hc : eExtend [a1, a2, a3, a4, a5] = true) (g4 : γ f ctx a4 v4) (n4 : v4.nat? = some a) :
    (MInst.extend rd rn sg a b).emitOk = true := by
  simp only [eExtend] at hc
  obtain ⟨i, rfl, h0, h1⟩ := leafLe_sound hc g4
  simp only [V.nat?, h0, ite_true, Option.some.injEq] at n4
  subst n4
  have : i.toNat - 1 < 32 := by omega
  simp only [MInst.emitOk, immOkB, MInst.noAlways, Bool.and_true, Bool.or_eq_true,
    decide_eq_true_eq]
  refine .inr ?_
  split <;> omega

theorem ec_bfm {s : OperandSize} {op : BfmOp} {rd rn : Reg} {a b : Nat}
    (hc : eBfm [a1, a2, a3, a4, a5, a6] = true) (g1 : γ f ctx a1 v1) (g5 : γ f ctx a5 v5)
    (g6 : γ f ctx a6 v6) (s1 : v1.size? = some s) (u5 : v5.uimm6? = some a)
    (u6 : v6.uimm6? = some b) : (MInst.bitfieldMove s op rd rn a b).emitOk = true := by
  simp only [eBfm, Bool.and_eq_true] at hc
  obtain ⟨a', rfl, ha⟩ := leafLe_sound hc.1 g5
  obtain ⟨b', rfl, hb⟩ := leafLe_sound hc.2 g6
  simp only [V.uimm6?, Option.some.injEq] at u5 u6
  subst u5 u6
  simp only [MInst.emitOk, immOkB, MInst.noAlways, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq]
  exact ⟨sizeBnd_lt g1 s1 ha, sizeBnd_lt g1 s1 hb⟩

theorem ec_cset {rd : Reg} {c : Cond} (hc : eCSet [a1, a2] = true) (g2 : γ f ctx a2 v2)
    (c2 : v2.cond? = some c) : (MInst.cset rd c).emitOk = true := by
  simp only [eCSet] at hc
  obtain ⟨h1, h2⟩ := condA_sound hc g2 c2
  cases c <;> simp_all [MInst.emitOk, immOkB, MInst.noAlways]

theorem ec_csetm {rd : Reg} {c : Cond} (hc : eCSet [a1, a2] = true) (g2 : γ f ctx a2 v2)
    (c2 : v2.cond? = some c) : (MInst.csetm rd c).emitOk = true := by
  simp only [eCSet] at hc
  obtain ⟨h1, h2⟩ := condA_sound hc g2 c2
  cases c <;> simp_all [MInst.emitOk, immOkB, MInst.noAlways]

theorem ec_ccmpImm {s : OperandSize} {rn : Reg} {i : Nat} {nz : NZCV} {c : Cond}
    (hc : eCCmpImm [a1, a2, a3, a4, a5] = true) (g3 : γ f ctx a3 v3) (u3 : v3.uimm5? = some i) :
    (MInst.ccmpImm s rn i nz c).emitOk = true := by
  simp only [eCCmpImm] at hc
  obtain ⟨i', rfl, hb⟩ := leafLe_sound hc g3
  simp only [V.uimm5?, Option.some.injEq] at u3
  subst u3
  simp only [MInst.emitOk, immOkB, MInst.noAlways, Bool.and_true, decide_eq_true_eq]
  exact hb

theorem ec_movToFpu {rd rn : Reg} {s : ScalarSize} (hc : eMovToFpu [a1, a2, a3] = true)
    (g3 : γ f ctx a3 v3) (s3 : v3.scalarSize? = some s) : (MInst.movToFpu rd rn s).emitOk = true := by
  simp only [eMovToFpu] at hc
  obtain ⟨k, hg, hp⟩ := enum_of hc g3 s3
  simp only [Bool.or_eq_true, beq_iff_eq] at hp
  rcases hp with (rfl | rfl) | rfl <;> cases s <;> first | rfl | exact absurd hg (by decide)

theorem ec_movFromVec {rd rn : Reg} {i : Nat} {s : ScalarSize}
    (hc : eMovFromVec [a1, a2, a3, a4] = true) (g3 : γ f ctx a3 v3) (g4 : γ f ctx a4 v4)
    (n3 : v3.nat? = some i) (s4 : v4.scalarSize? = some s) :
    (MInst.movFromVec rd rn i s).emitOk = true := by
  match a3, hc, g3 with
  | .num .int b, hc, g3 =>
    simp only [eMovFromVec] at hc
    obtain ⟨j, rfl, h0, h1⟩ := (g3 : NumOk .int b v3)
    simp only [V.nat?, h0, ite_true, Option.some.injEq] at n3
    subst n3
    obtain ⟨k, hg, hp⟩ := enum_of hc g4 s4
    have hp' := of_decide_eq_true hp
    unfold ScalarSize.ofIdx? at hg
    split at hg <;> cases hg <;> simp only [laneB] at hp' <;>
      simp only [MInst.emitOk, immOkB, MInst.noAlways, Bool.and_true, decide_eq_true_eq] <;> omega

theorem ec_vecMisc {op : VecMisc2} {rd rn : Reg} {s : VectorSize}
    (hc : eVecMisc [a1, a2, a3, a4] = true) (g4 : γ f ctx a4 v4) (s4 : v4.vectorSize? = some s) :
    (MInst.vecMisc op rd rn s).emitOk = true := by
  simp only [eVecMisc] at hc
  obtain ⟨k, hg, hp⟩ := enum_of hc g4 s4
  simp only [Bool.or_eq_true, beq_iff_eq] at hp
  rcases hp with rfl | rfl <;> cases s <;> first | rfl | exact absurd hg (by decide)

theorem ec_vecLanes {op : VecLanesOp} {rd rn : Reg} {s : VectorSize}
    (hc : eVecLanes [a1, a2, a3, a4] = true) (g4 : γ f ctx a4 v4) (s4 : v4.vectorSize? = some s) :
    (MInst.vecLanes op rd rn s).emitOk = true := by
  simp only [eVecLanes] at hc
  obtain ⟨k, hg, hp⟩ := enum_of hc g4 s4
  unfold VectorSize.ofIdx? at hg
  split at hg <;> cases hg <;> first | rfl | exact absurd hp (by decide)

theorem ec_tbb {kd : TestBitAndBranchKind} {t e : Label} {rn : Reg} {b : Nat}
    (hc : eTbb [a1, a2, a3, a4, a5] = true) (g5 : γ f ctx a5 v5) (n5 : v5.nat? = some b) :
    (MInst.testBitAndBranch kd t e rn b).emitOk = true := by
  simp only [eTbb] at hc
  obtain ⟨i, rfl, h0, h1⟩ := leafLe_sound hc g5
  simp only [V.nat?, h0, ite_true, Option.some.injEq] at n5
  subst n5
  simp only [MInst.emitOk, immOkB, MInst.noAlways, Bool.and_true, decide_eq_true_eq]
  omega

theorem ec_condBr {t e : Label} {kd : CondBrKind} (hc : eCondBr [a1, a2, a3] = true)
    (g3 : γ f ctx a3 v3) (k3 : v3.condBrKind? = some kd) : (MInst.condBr t e kd).emitOk = true := by
  simp only [eCondBr] at hc
  have := kind_noAlways hc g3 k3
  cases kd with
  | cond c => simpa [MInst.emitOk, immOkB, MInst.noAlways] using this c rfl
  | _ => rfl

theorem ec_trapIf {kd : CondBrKind} {tc : Clif.TrapCode} (hc : eTrapIf [a1, a2] = true)
    (g1 : γ f ctx a1 v1) (k1 : v1.condBrKind? = some kd) : (MInst.trapIf kd tc).emitOk = true := by
  simp only [eTrapIf] at hc
  have := kind_noAlways hc g1 k1
  cases kd with
  | cond c => simpa [MInst.emitOk, immOkB, MInst.noAlways] using this c rfl
  | _ => rfl

theorem ec_call {info : CallInfo} (hc : eCall [a1] = true) (g1 : γ f ctx a1 v1)
    (c1 : v1.callInfo? = some info) : (MInst.call info).emitOk = true := by
  match a1, hc, g1 with
  | .num .callInfo _, _, g1 =>
    obtain ⟨c, rfl, hd⟩ := (g1 : NumOk .callInfo _ v1)
    simp only [V.callInfo?, Option.some.injEq] at c1
    subst c1
    simp only [MInst.emitOk, immOkB, MInst.noAlways, Bool.and_true]
    split
    · rfl
    · rename_i r hr
      obtain ⟨n, rfl⟩ := hd r hr
      rfl

theorem atom_ok {a : AW} (ha : atomTyE a = true) {v : V} (hv : γ f ctx a v) {ty : CTy}
    (ht : v.ty? = some ty) : (ty.bits == 8 || ty.bits == 16 || ty.bits == 32 || ty.bits == 64) = true := by
  match a, ha, hv with
  | .ty ts, ha, hv =>
    obtain ⟨t', ht', rfl⟩ := hv
    simp only [V.ty?, Option.some.injEq] at ht
    subst ht
    simp only [atomTyE, List.all_eq_true] at ha
    exact ha _ ht'

theorem ec_atomicRmw {ty : CTy} {op : AtomicRmwLoopOp} {fl : Clif.MemFlags} {r1 r2 r3 r4 r5 : Reg}
    {as : List AW} (hc : eAtomic (a1 :: as) = true) (g1 : γ f ctx a1 v1) (t1 : v1.ty? = some ty) :
    (MInst.atomicRmwLoop ty op fl r1 r2 r3 r4 r5).emitOk = true := by
  simp only [eAtomic] at hc
  simp only [MInst.emitOk, immOkB, MInst.noAlways, Bool.and_true]
  exact atom_ok hc g1 t1

theorem ec_atomicCas {ty : CTy} {fl : Clif.MemFlags} {r1 r2 r3 r4 r5 : Reg}
    {as : List AW} (hc : eAtomic (a1 :: as) = true) (g1 : γ f ctx a1 v1) (t1 : v1.ty? = some ty) :
    (MInst.atomicCasLoop ty fl r1 r2 r3 r4 r5).emitOk = true := by
  simp only [eAtomic] at hc
  simp only [MInst.emitOk, immOkB, MInst.noAlways, Bool.and_true]
  exact atom_ok hc g1 t1

end variants

/-! ## The check of a variant -/

theorem em1_eq {nb : Bool} {k : Nat} {c : List AW → Bool} (h : emTab.lookup k = some c)
    (as : List AW) : em1 nb k as = (!(nb && branchKs.contains k) && c as) := by
  unfold em1; rw [h]

theorem em1_none {nb : Bool} {k : Nat} (h : emTab.lookup k = none) (as : List AW) :
    em1 nb k as = !(nb && branchKs.contains k) := by
  unfold em1; rw [h]; simp

set_option maxHeartbeats 4000000 in
/-- **`em1` is the abstract emission condition**: an `MInst` value of variant `k` whose fields
`em1 nb k` accepts decodes to an instruction with the emission conditions, without branch
targets if `nb`. -/
theorem em1_sound {nb : Bool} {t k : Nat} {as : List AW} {vs : List V} (hc : em1 nb k as = true)
    (hl : γL f ctx as vs) {m : MInst} (h : MInst.ofV (.data t k vs) = some m) :
    m.emitOk = true ∧ (nb = true → m.targets = []) := by
  unfold MInst.ofV at h
  obtain ⟨⟨k', fs'⟩, he, h2⟩ := bind_some_ex h
  clear h
  simp only [V.enumOf?] at he
  split at he
  rotate_left
  · cases he
  cases he
  dsimp only at h2
  revert h2 m as hc hl
  apply ofV_split _ (fun k vs (r : Option MInst) => ∀ {as : List AW}, em1 nb k as = true →
    γL f ctx as vs → ∀ {m : MInst}, r = some m → m.emitOk = true ∧ (nb = true → m.targets = [])) k vs
  all_goals
    intros
    rename_i as hc hl m hm
    try simp only at hm
    repeat' (first | (obtain ⟨_, _, hm⟩ := bind_some_ex hm) | split at hm)
    all_goals try (cases hm; done)
  all_goals try (simp only [pure, Option.some.injEq] at hm; subst hm)
  all_goals first
    | exact ⟨rfl, fun _ => rfl⟩
    | skip
  all_goals fields hl
  all_goals first
    | (refine ⟨rfl, fun hnb => ?_⟩
       subst hnb
       rw [em1_none rfl] at hc
       exact absurd hc (by decide))
    | (rw [em1_eq rfl] at hc
       simp only [Bool.and_eq_true] at hc
       obtain ⟨hnb, hc⟩ := hc
       refine ⟨?_, fun h => ?_⟩
       rotate_left
       · first
         | rfl
         | (subst h; exact absurd hnb (by decide))
       first
       | (apply ec_aluRRImm12 hc <;> assumption)
       | (apply ec_aluRRImmShift hc <;> assumption)
       | (apply ec_aluRRRShift hc <;> assumption)
       | (apply ec_aluRRRExtend hc <;> assumption)
       | (apply ec_movWide hc <;> assumption)
       | (apply ec_movK hc <;> assumption)
       | (apply ec_extend hc <;> assumption)
       | (apply ec_bfm hc <;> assumption)
       | (apply ec_cset hc <;> assumption)
       | (apply ec_csetm hc <;> assumption)
       | (apply ec_ccmpImm hc <;> assumption)
       | (apply ec_movToFpu hc <;> assumption)
       | (apply ec_movFromVec hc <;> assumption)
       | (apply ec_vecMisc hc <;> assumption)
       | (apply ec_vecLanes hc <;> assumption)
       | (apply ec_tbb hc <;> assumption)
       | (apply ec_condBr hc <;> assumption)
       | (apply ec_trapIf hc <;> assumption)
       | (apply ec_call hc <;> assumption)
       | (apply ec_atomicRmw hc <;> assumption)
       | (apply ec_atomicCas hc <;> assumption))

theorem emA1_sound {nb : Bool} {a : AW} {v : V} {m : MInst} (ha : emA1 nb a = true)
    (hv : γ f ctx a v) (hm : MInst.ofV v = some m) :
    m.emitOk = true ∧ (nb = true → m.targets = []) := by
  match a, ha, hv with
  | .data t k fs, ha, hv =>
    obtain ⟨vs, rfl, hl⟩ := hv
    simp only [emA1, Bool.and_eq_true] at ha
    exact em1_sound ha.2 hl hm

/-- **The emission check is sound**: an instruction value `emChk nb` accepts decodes (as `emit`
decodes it, `MInst.ofV`) to an instruction with the emission conditions, and without branch
targets if `nb`. -/
theorem emChk_sound {nb : Bool} {a : AW} {v : V} {m : MInst} (ha : emChk nb a = true)
    (hv : γ f ctx a v) (hm : MInst.ofV v = some m) :
    m.emitOk = true ∧ (nb = true → m.targets = []) := by
  cases a with
  | alts as =>
    simp only [emChk, List.all_eq_true] at ha
    obtain ⟨b, hb, hbv⟩ := γAny_iff.mp hv
    exact emA1_sound (ha b hb) hbv hm
  | _ => exact emA1_sound (by simpa only [emChk] using ha) hv hm

/-! ## Side effects ending in a branch -/

/-- The decoded instruction of `i` has the emission conditions, and no branch targets if `nb`. -/
def ChkV (nb : Bool) (i : V) : Prop :=
  ∀ m, MInst.ofV i = some m → m.emitOk = true ∧ (nb = true → m.targets = [])

theorem chkV_of {nb : Bool} {a : AW} {i : V} (ha : emChk nb a = true) (hv : γ f ctx a i) :
    ChkV nb i :=
  fun _ hm => emChk_sound ha hv hm

/-- The side effects `senrLast` accepts (`emit_side_effect`'s argument): one, two or three
instructions with the emission conditions, branch targets only on the last one. -/
def SenrOk (v : V) : Prop :=
  (∃ i, v = .data TyId.SideEffectNoResult VIdx.SideEffectNoResult.Inst [i] ∧ ChkV false i) ∨
  (∃ i j, v = .data TyId.SideEffectNoResult VIdx.SideEffectNoResult.Inst2 [i, j] ∧
    ChkV true i ∧ ChkV false j) ∨
  (∃ i j l, v = .data TyId.SideEffectNoResult VIdx.SideEffectNoResult.Inst3 [i, j, l] ∧
    ChkV true i ∧ ChkV true j ∧ ChkV false l)

theorem senr1_sound {a : AW} (ha : senr1 a = true) {v : V} (hv : γ f ctx a v) : SenrOk v := by
  match a, ha, hv with
  | .data t k [i], ha, hv =>
    obtain ⟨vs, rfl, hl⟩ := hv
    simp only [senr1, Bool.and_eq_true, beq_iff_eq] at ha
    obtain ⟨⟨rfl, rfl⟩, h1⟩ := ha
    rcases vs with _ | ⟨w1, _ | ⟨w2, ws⟩⟩
    · exact hl.elim
    · exact .inl ⟨_, rfl, chkV_of h1 hl.1⟩
    · exact hl.2.elim
  | .data t k [i, j], ha, hv =>
    obtain ⟨vs, rfl, hl⟩ := hv
    simp only [senr1, Bool.and_eq_true, beq_iff_eq] at ha
    obtain ⟨⟨⟨rfl, rfl⟩, h1⟩, h2⟩ := ha
    rcases vs with _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, ws⟩⟩⟩
    · exact hl.elim
    · exact hl.2.elim
    · exact .inr (.inl ⟨_, _, rfl, chkV_of h1 hl.1, chkV_of h2 hl.2.1⟩)
    · exact hl.2.2.elim
  | .data t k [i, j, l], ha, hv =>
    obtain ⟨vs, rfl, hl⟩ := hv
    simp only [senr1, Bool.and_eq_true, beq_iff_eq] at ha
    obtain ⟨⟨⟨⟨rfl, rfl⟩, h1⟩, h2⟩, h3⟩ := ha
    rcases vs with _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, ws⟩⟩⟩⟩
    · exact hl.elim
    · exact hl.2.elim
    · exact hl.2.2.elim
    · exact .inr (.inr ⟨_, _, _, rfl, chkV_of h1 hl.1, chkV_of h2 hl.2.1, chkV_of h3 hl.2.2.1⟩)
    · exact hl.2.2.2.elim

/-- **The side-effect check is sound** (`aLast`'s `emit_side_effect` argument). -/
theorem senrLast_sound {a : AW} (ha : senrLast a = true) {v : V} (hv : γ f ctx a v) : SenrOk v := by
  cases a with
  | alts as =>
    simp only [senrLast, List.all_eq_true] at ha
    obtain ⟨b, hb, hbv⟩ := γAny_iff.mp hv
    exact senr1_sound (ha b hb) hbv
  | _ => exact senr1_sound (by simpa only [senrLast] using ha) hv

end Backend.Proof.Cov
