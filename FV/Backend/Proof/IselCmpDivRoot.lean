import FV.Backend.Proof.IselCmpDiv
import FV.Backend.Proof.IselTermsALUA

/-!
# Family C: division root rules
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-! ## The division instruction -/

set_option maxRecDepth 20000 in
theorem div_variantNames_Binary : (variantNames 152)[2]? = some "Binary" := rfl

theorem instData_div_inv {f : Clif.Function} {cl : Clif.Inst} {w : V} {ko : Nat} {op : Clif.DivOp}
    (hname : (variantNames 151)[ko]? = some (divOpcode op))
    (h : instData f cl = .ok (.data 152 2 [.data 151 ko [], w])) :
    ∃ ty x y, cl = .div op ty x y ∧ eTy ty = true ∧ w = .values [x, y] := by
  obtain ⟨hf, ho⟩ := instData_inv_names h
  rw [div_variantNames_Binary] at hf
  rw [hname] at ho
  cases cl <;> simp [instNames] at hf ho
  · rename_i op' _ _ _
    cases op <;> cases op' <;> simp [binaryOpcode, divOpcode] at ho
  · rename_i op' ty x y
    have : op' = op := by cases op <;> cases op' <;> simp [divOpcode] at ho ⊢
    subst this
    refine ⟨ty, x, y, rfl, ?_⟩
    simp only [instData] at h
    split at h
    · rename_i he
      simp only [pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨-, -, h3⟩ := mkVariant_eq_data h
      simp only [List.cons.injEq] at h3
      exact ⟨he, h3.2.1⟩
    · cases h

theorem getAs_ne_trap (fr : Clif.Frame) (x : Nat) (ty : Clif.Ty) (c : Clif.TrapCode) :
    fr.getAs x ty ≠ .trap c := by
  unfold Clif.Frame.getAs Clif.Frame.get
  cases fr.regs x with
  | none => simp [Clif.Res.ofOption, bind, Clif.Res.bind]
  | some v =>
    simp only [Clif.Res.ofOption, bind, Clif.Res.bind]
    cases v.as? ty <;> simp

theorem evalInst_div_inv {fr : Clif.Frame} {cm : Clif.Mem} {op : Clif.DivOp} {ty : Clif.Ty}
    {x y : Nat} {r : Clif.Res (List Clif.Val × Clif.Mem)} (h : Clif.evalInst fr cm (.div op ty x y) = r)
    (hr : ∀ m, r ≠ .stuck m) :
    ∃ a b, fr.regs x = some ⟨ty, a⟩ ∧ fr.regs y = some ⟨ty, b⟩ ∧
      r = Clif.Res.bind (Clif.Res.ofExcept (Clif.Sem.div op a b)) fun q => .ok ([⟨ty, q⟩], cm) := by
  simp only [Clif.evalInst] at h
  cases hx : fr.getAs x ty with
  | ok a =>
    cases hy : fr.getAs y ty with
    | ok b =>
      rw [hx, hy] at h
      exact ⟨a, b, getAs_ok hx, getAs_ok hy, by rw [← h]; rfl⟩
    | trap c => exact absurd hy (getAs_ne_trap _ _ _ _)
    | stuck m => rw [hx, hy] at h; subst h; exact absurd rfl (hr m)
  | trap c => exact absurd hx (getAs_ne_trap _ _ _ _)
  | stuck m => rw [hx] at h; subst h; exact absurd rfl (hr m)

/-- **`LowerInstOk` for a division**: the result's run when it returns, the halt at a trap
instruction with its code when it traps. -/
theorem lowerInstOk_div {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT} {env : Clif.Env}
    {cp : Clif.Program} {ctx : Ctx} {op : Clif.DivOp} {ty : Clif.Ty} {x y : Nat}
    {results : List Nat} {st st' : LState} {ms : List MInst} {d : Nat} (hMR : MRStable F MR)
    (hmono : st.nextVreg ≤ st'.nextVreg)
    (hdefs : ∀ m ∈ ms, ∀ d ∈ vdefs m, st.nextVreg ≤ d ∧ d < st'.nextVreg) (hd : st.nextVreg ≤ d)
    (hrun : ∀ (fr : Clif.Frame) (ρ : Nat → CV) (w : Arm.ArmState) (a b : BitVec ty.width),
      fr.func = ctx.func → ValsHeld fr ρ → DFGCons ctx fr →
      fr.regs x = some ⟨ty, a⟩ → fr.regs y = some ⟨ty, b⟩ →
      UsesOk st fr ms ∧
      (∀ c, Clif.Sem.div op a b = .error c → TrapRun isem ms ρ w c) ∧
      (∀ q, Clif.Sem.div op a b = .ok q → Runs F isem ms ρ w (fun ρ' _ => VHolds ⟨ty, q⟩ (ρ' d)))) :
    LowerInstOk isem MR env cp ctx (.div op ty x y) results st [[.vreg d .int]] st' ms := by
  refine ⟨hmono, hdefs, ?_⟩
  intro fr cm ρ w hf hv hdfg hmr
  have hev : instOutcome env cp fr cm (.div op ty x y) = Clif.evalInst fr cm (.div op ty x y) := rfl
  rw [hev]
  split
  · rename_i vals cm' ho
    obtain ⟨a, b, hxa, hyb, hr⟩ := evalInst_div_inv ho (fun m h => by cases h)
    obtain ⟨hu, -, hok⟩ := hrun fr ρ w a b hf hv hdfg hxa hyb
    cases hq : Clif.Sem.div op a b with
    | error c => rw [hq] at hr; cases hr
    | ok q =>
      rw [hq] at hr
      simp only [Clif.Res.ofExcept, Clif.Res.bind] at hr
      cases hr
      obtain ⟨ρ', w', hs, hw, hh⟩ := hok q hq
      refine ⟨hu, ρ', w', hs, .inr ⟨rfl, ?_⟩, hMR _ _ _ _ hw hmr⟩
      intro j rs val hrs hval
      match j, hrs, hval with
      | 0, hrs, hval =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hrs hval
        subst hrs; subst hval
        exact ⟨d, .int, rfl, .inl hd, hh⟩
      | _ + 1, hrs, _ => simp at hrs
  · rename_i c ho
    intro _
    obtain ⟨a, b, hxa, hyb, hr⟩ := evalInst_div_inv ho (fun m h => by cases h)
    obtain ⟨hu, htr, -⟩ := hrun fr ρ w a b hf hv hdfg hxa hyb
    cases hq : Clif.Sem.div op a b with
    | error c' =>
      rw [hq] at hr
      simp only [Clif.Res.ofExcept, Clif.Res.bind] at hr
      cases hr
      obtain ⟨k, i, ops, ρ₁, w₁, outs, w₂, hs, hc⟩ := htr c hq
      exact ⟨hu, k, i, ops, ρ₁, w₁, outs, w₂, hs, hc⟩
    | ok q => rw [hq] at hr; simp [Clif.Res.ofExcept, Clif.Res.bind] at hr
  · trivial

/-! ## Running the division instructions -/

theorem runs_udiv {F : BitVec 64 → Prop} {isem : Sem} (hR : Refines F isem) (sz : OperandSize)
    (d x y : Nat) (ρ : Nat → CV) (w : Arm.ArmState) :
    Runs F isem [.aluRRR .uDiv sz (.vreg d .int) (.vreg x .int) (.vreg y .int)] ρ w
      (fun ρ' _ => ρ' = upd ρ d (resX sz (opnd sz (ρ x) / opnd sz (ρ y)))) :=
  Runs.one hR (operands_aluRRR _ _ _ _ _) rfl rfl (SameWorldNF.refl F w) fun _ _ => rfl

theorem runs_sdiv {F : BitVec 64 → Prop} {isem : Sem} (hR : Refines F isem) (sz : OperandSize)
    (d x y : Nat) (ρ : Nat → CV) (w : Arm.ArmState) :
    Runs F isem [.aluRRR .sDiv sz (.vreg d .int) (.vreg x .int) (.vreg y .int)] ρ w
      (fun ρ' _ => ρ' = upd ρ d (resX sz ((opnd sz (ρ x)).sdiv (opnd sz (ρ y))))) :=
  Runs.one hR (operands_aluRRR _ _ _ _ _) rfl rfl (SameWorldNF.refl F w) fun _ _ => rfl

theorem div_operands_aluRRRR (op : ALUOp3) (sz : OperandSize) (d x y z : Nat) :
    (MInst.aluRRRR op sz (.vreg d .int) (.vreg x .int) (.vreg y .int) (.vreg z .int)).operands =
      .ok #[⟨d, .int, .def, .late, .reg⟩, ⟨x, .int, .use, .early, .reg⟩,
        ⟨y, .int, .use, .early, .reg⟩, ⟨z, .int, .use, .early, .reg⟩] := rfl

theorem runs_msub {F : BitVec 64 → Prop} {isem : Sem} (hR : Refines F isem) (sz : OperandSize)
    (d a b c : Nat) (ρ : Nat → CV) (w : Arm.ArmState) :
    Runs F isem [.aluRRRR .mSub sz (.vreg d .int) (.vreg a .int) (.vreg b .int) (.vreg c .int)] ρ w
      (fun ρ' _ => ρ' = upd ρ d (resX sz (opnd sz (ρ c) - opnd sz (ρ a) * opnd sz (ρ b)))) :=
  Runs.one hR (div_operands_aluRRRR _ _ _ _ _ _) rfl rfl (SameWorldNF.refl F w) fun _ _ => rfl

theorem opnd_resX (sz : OperandSize) (r : BitVec sz.bits) : opnd sz (resX sz r) = r := by
  apply BitVec.eq_of_toNat_eq
  have h := r.isLt
  have h2 : 2 ^ sz.bits ≤ 2 ^ 64 := by cases sz <;> decide
  simp only [opnd, resX, lo64, ofX, BitVec.toNat_setWidth]
  generalize r.toNat = t at *
  rw [Nat.mod_eq_of_lt (by omega : t < 2^64), Nat.mod_eq_of_lt (by omega : t < 2^128),
    Nat.mod_eq_of_lt (by omega : t < 2^64), Nat.mod_eq_of_lt h]

/-! ## Unsigned results -/

theorem pow_le64 {n : Nat} (hn : n ≤ 64) : 2 ^ n ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) hn

theorem divOpnd_toNat {n : Nat} (hn : n ≤ 64) {b : BitVec n} {a : CV} (h : DivOpnd false b a) :
    (opnd (szOf n) a).toNat = b.toNat := by
  unfold DivOpnd at h
  by_cases h32 : n ≤ 32
  · have e : szOf n = .size32 := ite_eq_left_iff.mpr (fun h => absurd h32 h)
    rw [e]
    simp only [h32, ↓reduceIte, Bool.false_eq_true] at h
    show ((lo64 a).setWidth 32).toNat = _
    rw [h, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le b.isLt (Nat.pow_le_pow_right (by omega) h32))]
  · have e : szOf n = .size64 := by simp [szOf, h32]
    rw [e]
    simp only [h32, ↓reduceIte] at h
    show ((lo64 a).setWidth 64).toNat = _
    rw [h, BitVec.toNat_setWidth, BitVec.toNat_setWidth]
    have := Nat.lt_of_lt_of_le b.isLt (pow_le64 hn)
    rw [Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt this]

theorem vholds_resX_toNat {ty : Clif.Ty} (hw : ty.width ≤ 64) {sz : OperandSize} {r : BitVec sz.bits}
    {q : BitVec ty.width} (h : r.toNat = q.toNat) : VHolds ⟨ty, q⟩ (resX sz r) := by
  simp only [VHolds, resX, ofX]
  apply BitVec.eq_of_toNat_eq
  have hq := q.isLt
  have h64 := pow_le64 hw
  simp only [BitVec.toNat_setWidth, h]
  rw [Nat.mod_eq_of_lt (by omega : q.toNat < 2 ^ 64), Nat.mod_eq_of_lt (by omega : q.toNat < 2 ^ 128),
    Nat.mod_eq_of_lt hq]

theorem udiv_vholds {ty : Clif.Ty} (hw : ty.width ≤ 64) {a b : BitVec ty.width} {A B : CV}
    (hA : DivOpnd false a A) (hB : DivOpnd false b B) :
    VHolds ⟨ty, a / b⟩ (resX (szOf ty.width) (opnd (szOf ty.width) A / opnd (szOf ty.width) B)) := by
  apply vholds_resX_toNat hw
  rw [BitVec.toNat_udiv, BitVec.toNat_udiv, divOpnd_toNat hw hA, divOpnd_toNat hw hB]

theorem urem_core {n : Nat} (X Y : BitVec n) : (X - (X / Y) * Y).toNat = X.toNat % Y.toNat := by
  have hq : (X / Y * Y).toNat = X.toNat / Y.toNat * Y.toNat := by
    rw [BitVec.toNat_mul, BitVec.toNat_udiv]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) X.isLt)
  have hle : X / Y * Y ≤ X := by
    rw [BitVec.le_def, hq]; exact Nat.div_mul_le_self _ _
  rw [BitVec.toNat_sub_of_le hle, hq, Nat.mod_eq_sub_div_mul]

theorem urem_vholds {ty : Clif.Ty} (hw : ty.width ≤ 64) {a b : BitVec ty.width} {A B : CV}
    (hA : DivOpnd false a A) (hB : DivOpnd false b B) :
    VHolds ⟨ty, a % b⟩ (resX (szOf ty.width) (opnd (szOf ty.width) A -
      opnd (szOf ty.width) (resX (szOf ty.width) (opnd (szOf ty.width) A / opnd (szOf ty.width) B)) *
        opnd (szOf ty.width) B)) := by
  apply vholds_resX_toNat hw
  rw [opnd_resX, BitVec.toNat_umod, urem_core, divOpnd_toNat hw hA, divOpnd_toNat hw hB]

section
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)

set_option maxHeartbeats 4000000 in
include hp hc in
theorem div_alu_rrr_ok {n : Nat} (hn : 40 ≤ n) {k : Nat} {op : ALUOp} (hk : ALUOp.ofIdx? k = some op)
    {w : Nat} (hw : w ≤ 64) {ra rb : Reg} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 362 [.data 59 k [], .ty (.int w), .reg ra, .reg rb] s v s') :
    v = .reg (s.1.fresh .int).1 ∧
      s'.1 = (s.1.fresh .int).2.emit (.aluRRR op (szOf w) (s.1.fresh .int).1 ra rb) := by
  isel_split' hp hc h 362
  all_goals isel_inv' hp [] at hm he
  obtain ⟨h305⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 93 305 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨hm1⟩ : Nonempty (MInst.ofV _ = some _) := ⟨‹_›⟩
  obtain ⟨hs, hsz⟩ := operand_size_ok hp hc (by omega) h305
  simp only [show (CTy.int w).bits = w from rfl] at hsz
  rcases hsz with ⟨hb, rfl⟩ | ⟨hb, -, rfl⟩
  · rw [ofV_aluRRR hk rfl] at hm1
    cases hm1
    rw [hs]
    simp [szOf, hb]
  · rw [ofV_aluRRR hk rfl] at hm1
    cases hm1
    rw [hs]
    simp [szOf, show ¬ w ≤ 32 by omega]

set_option maxHeartbeats 4000000 in
include hp hc in
theorem a64_udiv_ok {n : Nat} (hn : 60 ≤ n) {w : Nat} (hw : w ≤ 64) {ra rb : Reg}
    {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 492 [.ty (.int w), .reg ra, .reg rb] s v s') :
    v = .reg (s.1.fresh .int).1 ∧
      s'.1 = (s.1.fresh .int).2.emit (.aluRRR .uDiv (szOf w) (s.1.fresh .int).1 ra rb) := by
  isel_split' hp hc h 492
  all_goals isel_inv' hp [] at hm he
  obtain ⟨h362⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 362 _ _ _ _) := ⟨‹_›⟩
  exact div_alu_rrr_ok hp hc (by omega) rfl hw h362

set_option maxHeartbeats 4000000 in
include hp hc in
theorem a64_sdiv_ok {n : Nat} (hn : 60 ≤ n) {w : Nat} (hw : w ≤ 64) {ra rb : Reg}
    {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 493 [.ty (.int w), .reg ra, .reg rb] s v s') :
    v = .reg (s.1.fresh .int).1 ∧
      s'.1 = (s.1.fresh .int).2.emit (.aluRRR .sDiv (szOf w) (s.1.fresh .int).1 ra rb) := by
  isel_split' hp hc h 493
  all_goals isel_inv' hp [] at hm he
  obtain ⟨h362⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 362 _ _ _ _) := ⟨‹_›⟩
  exact div_alu_rrr_ok hp hc (by omega) rfl hw h362

set_option maxHeartbeats 4000000 in
include hp hc in
theorem msub_ok {n : Nat} (hn : 60 ≤ n) {w : Nat} (hw : w ≤ 64) {ra rb rc : Reg}
    {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 444 [.ty (.int w), .reg ra, .reg rb, .reg rc] s v s') :
    v = .reg (s.1.fresh .int).1 ∧
      s'.1 = (s.1.fresh .int).2.emit (.aluRRRR .mSub (szOf w) (s.1.fresh .int).1 ra rb rc) := by
  isel_split' hp hc h 444
  all_goals isel_inv' hp [] at hm he
  obtain ⟨h382⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 382 _ _ _ _) := ⟨‹_›⟩
  try clear hpre
  isel_split' hp hc h382 382
  all_goals isel_inv' hp [] at hm he
  obtain ⟨h305⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 93 305 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨hm1⟩ : Nonempty (MInst.ofV _ = some _) := ⟨‹_›⟩
  obtain ⟨hs, hsz⟩ := operand_size_ok hp hc (by omega) h305
  simp only [show (CTy.int w).bits = w from rfl] at hsz
  rcases hsz with ⟨hb, rfl⟩ | ⟨hb, -, rfl⟩
  · rw [ofV_aluRRRR rfl rfl] at hm1
    cases hm1
    rw [hs]
    simp [szOf, hb]
  · rw [ofV_aluRRRR rfl rfl] at hm1
    cases hm1
    rw [hs]
    simp [szOf, show ¬ w ≤ 32 by omega]

end

section Root
variable {p : Program} (hp : Data p)

set_option maxHeartbeats 8000000 in
include hp in
theorem udiv64_ruleOk (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOk isem MR env cp p rule_lower_1116 := by
  intro f ctx hctx ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _ hmatch heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 400 := ⟨n - 400, by omega⟩
  isel_inv' hp [] at hmatch heval
  trace_state
  sorry

end Root

end Backend.Proof
