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

/-! ## The dividend operand -/

theorem divOpnd_of_vholds64 {sg : Bool} {ty : Clif.Ty} (hw : ty.width = 64) {a : BitVec ty.width}
    {A : CV} (h : VHolds ⟨ty, a⟩ A) : DivOpnd sg a A := by
  cases ty <;> simp [Clif.Ty.width] at hw
  simp only [VHolds, Clif.Ty.width] at h
  unfold DivOpnd
  simp only [Clif.Ty.width, show ¬ (64 : Nat) ≤ 32 by decide, ↓reduceIte, lo64, BitVec.setWidth_eq]
  exact h

/-- **The dividend**: a `put_in_reg_*ext*` result (or the value's own register) holding the value
as a division operand. -/
theorem ext_divOpnd {F : BitVec 64 → Prop} {isem : Sem} (hR : Refines F isem) {f : Clif.Function}
    {ctx : Ctx} (hctx : CtxInv f ctx) {x : Nat} {sg : Bool} {toB w : Nat} {pass : List CTy}
    {s s' : LState} {v : V} (hvb : ValsBelow ctx s)
    (hcase : (toB = 32 ∧ pass = [.int 32, .int 64]) ∨ (toB = 64 ∧ pass = [.int 64] ∧ w = 64))
    (hw : w ≤ 32 ∨ w = 64) (h : ExtOut ctx x sg toB pass s s' v) :
    ∃ k ms, v = .reg (.vreg k .int) ∧ Frag s s' ms ∧ k < s'.nextVreg ∧ (s.nextVreg ≤ k ∨ k = x) ∧
      ∀ (fr : Clif.Frame) (ρ : Nat → CV) (ty : Clif.Ty) (a : BitVec ty.width), ty.width = w →
        ValsHeld fr ρ → DFGCons ctx fr → fr.regs x = some ⟨ty, a⟩ →
        UsesLo s.nextVreg fr ms ∧ ∀ wd, Runs F isem ms ρ wd (fun ρ' _ => DivOpnd sg a (ρ' k)) := by
  have hto : toB = 32 ∨ toB = 64 := by rcases hcase with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
  obtain ⟨k, ms, rfl, hf, hk, hkx, hsem⟩ := ExtOut.sem hR hctx hvb hto
    (by rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl, -⟩ <;> intro t ht <;> simp at ht <;>
      rcases ht with rfl | rfl <;> simp)
    (by rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl, -⟩ <;> simp) h
  refine ⟨k, ms, rfl, hf, hk, hkx, fun fr ρ ty a htw hh hdf hxv => ?_⟩
  obtain ⟨hu, hrun⟩ := hsem fr ρ _ (hh x _ hxv) hdf hxv
  refine ⟨hu, fun wd => (hrun wd).imp fun ρ' _ _ he => ?_⟩
  rcases hw with hw | hw
  · rcases hcase with ⟨rfl, -⟩ | ⟨-, -, rfl⟩
    · unfold DivOpnd
      simp only [show ty.width ≤ 32 by omega, ↓reduceIte]
      exact he.2 (by simp; omega)
    · omega
  · exact divOpnd_of_vholds64 (by omega) he.1

/-! ## Unsigned division and remainder: the code after the operands -/

theorem div_upd_ne {ρ : Nat → CV} {d k : Nat} {v : CV} (h : k ≠ d) : upd ρ d v k = ρ k := by
  simp [upd, h]

theorem vdefs_aluRRR' (op : ALUOp) (sz : OperandSize) (d x y : Nat) :
    vdefs (MInst.aluRRR op sz (.vreg d .int) (.vreg x .int) (.vreg y .int)) = [d] := rfl
theorem vuseNums_aluRRR' (op : ALUOp) (sz : OperandSize) (d x y : Nat) :
    vuseNums (MInst.aluRRR op sz (.vreg d .int) (.vreg x .int) (.vreg y .int)) = [x, y] := rfl
theorem vdefs_aluRRRR' (op : ALUOp3) (sz : OperandSize) (d x y z : Nat) :
    vdefs (MInst.aluRRRR op sz (.vreg d .int) (.vreg x .int) (.vreg y .int) (.vreg z .int)) = [d] := rfl
theorem vuseNums_aluRRRR' (op : ALUOp3) (sz : OperandSize) (d x y z : Nat) :
    vuseNums (MInst.aluRRRR op sz (.vreg d .int) (.vreg x .int) (.vreg y .int) (.vreg z .int)) =
      [x, y, z] := rfl

theorem udiv_trap {n : Nat} {a b : BitVec n} {c : Clif.TrapCode} (h : Clif.Sem.div .udiv a b = .error c) :
    b = 0#n ∧ c = .intDivz := by
  simp only [Clif.Sem.div, Clif.Sem.udiv] at h
  split at h
  · cases h; exact ⟨‹_›, rfl⟩
  · cases h

theorem udiv_ok {n : Nat} {a b q : BitVec n} (h : Clif.Sem.div .udiv a b = .ok q) :
    b ≠ 0#n ∧ q = a / b := by
  simp only [Clif.Sem.div, Clif.Sem.udiv] at h
  split at h
  · cases h
  · cases h; exact ⟨‹_›, rfl⟩

theorem urem_trap {n : Nat} {a b : BitVec n} {c : Clif.TrapCode} (h : Clif.Sem.div .urem a b = .error c) :
    b = 0#n ∧ c = .intDivz := by
  simp only [Clif.Sem.div, Clif.Sem.urem] at h
  split at h
  · cases h; exact ⟨‹_›, rfl⟩
  · cases h

theorem urem_ok {n : Nat} {a b q : BitVec n} (h : Clif.Sem.div .urem a b = .ok q) :
    b ≠ 0#n ∧ q = a % b := by
  simp only [Clif.Sem.div, Clif.Sem.urem] at h
  split at h
  · cases h
  · cases h; exact ⟨‹_›, rfl⟩

section Finish
variable {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
  {ctx : Ctx} {ty : Clif.Ty} {x y : Nat} {st s1 s2 : LState} {kx ky : Nat} {msX msY : List MInst}
  {sg : Bool}

/-- The operand codes of a division: the dividend (`msX`, into `kx`) then the divisor with its
zero check (`msY`, into `ky`). -/
structure DivOperands (F : BitVec 64 → Prop) (isem : Sem) (ctx : Ctx) (ty : Clif.Ty) (x y : Nat)
    (sg : Bool) (st s1 s2 : LState) (kx ky : Nat) (msX msY : List MInst) : Prop where
  xlt : x < st.nextVreg
  vb : ValsBelow ctx st
  fX : Frag st s1 msX
  kxlt : kx < s1.nextVreg
  kxl : st.nextVreg ≤ kx ∨ kx = x
  sX : ∀ (fr : Clif.Frame) (ρ : Nat → CV) (a : BitVec ty.width), ValsHeld fr ρ → DFGCons ctx fr →
    fr.regs x = some ⟨ty, a⟩ →
    UsesLo st.nextVreg fr msX ∧ ∀ wd, Runs F isem msX ρ wd (fun ρ' _ => DivOpnd sg a (ρ' kx))
  fY : Frag s1 s2 msY
  kyl : s1.nextVreg ≤ ky ∨ ky = y
  sY : ∀ (fr : Clif.Frame) (ρ : Nat → CV) (b : BitVec ty.width),
    ((∃ r, ctx.valueReg? y = some r) → VHolds ⟨ty, b⟩ (ρ y)) →
    DFGCons ctx fr → fr.regs y = some ⟨ty, b⟩ →
    UsesLo s1.nextVreg fr msY ∧ ∀ wd, ky < s2.nextVreg ∧
      (b = 0#ty.width → TrapRun isem msY ρ wd .intDivz) ∧
      (b ≠ 0#ty.width → Runs F isem msY ρ wd (fun ρ' _ => DivOpnd sg b (ρ' ky)))

theorem DivOperands.uses (h : DivOperands F isem ctx ty x y sg st s1 s2 kx ky msX msY)
    {fr : Clif.Frame} {ρ : Nat → CV} {a b : BitVec ty.width} (hh : ValsHeld fr ρ)
    (hdf : DFGCons ctx fr) (hxa : fr.regs x = some ⟨ty, a⟩) (hyb : fr.regs y = some ⟨ty, b⟩) :
    UsesLo st.nextVreg fr (msX ++ msY) ∧ (st.nextVreg ≤ kx ∨ (fr.regs kx).isSome) ∧
      (st.nextVreg ≤ ky ∨ (fr.regs ky).isSome) := by
  obtain ⟨huX, -⟩ := h.sX fr ρ a hh hdf hxa
  obtain ⟨huY, -⟩ := h.sY fr ρ b (fun _ => hh y _ hyb) hdf hyb
  refine ⟨huX.append (huY.mono h.fX.mono), ?_, ?_⟩
  · rcases h.kxl with h' | rfl
    · exact .inl h'
    · exact .inr (by simp [hxa])
  · rcases h.kyl with h' | rfl
    · exact .inl (Nat.le_trans h.fX.mono h')
    · exact .inr (by simp [hyb])

/-- Running both operand codes: `kx` and `ky` hold the operands (or the divisor check halts). -/
theorem DivOperands.run (h : DivOperands F isem ctx ty x y sg st s1 s2 kx ky msX msY)
    {fr : Clif.Frame} {ρ : Nat → CV} {a b : BitVec ty.width} (hh : ValsHeld fr ρ)
    (hdf : DFGCons ctx fr) (hxa : fr.regs x = some ⟨ty, a⟩) (hyb : fr.regs y = some ⟨ty, b⟩)
    (w : Arm.ArmState) :
    ky < s2.nextVreg ∧ (b = 0#ty.width → TrapRun isem (msX ++ msY) ρ w .intDivz) ∧
      (b ≠ 0#ty.width → Runs F isem (msX ++ msY) ρ w
        (fun ρ' _ => DivOpnd sg a (ρ' kx) ∧ DivOpnd sg b (ρ' ky))) := by
  obtain ⟨-, hrX⟩ := h.sX fr ρ a hh hdf hxa
  have hX := (hrX w).imp fun ρ1 w1 hr h1 => And.intro h1
    (fun (hy : ∃ r, ctx.valueReg? y = some r) => h.fX.frame hr (h.vb y _ hy.choose_spec))
  refine ⟨(h.sY fr ρ b (fun _ => hh y _ hyb) hdf hyb).2 w |>.1, fun h0 => ?_, fun h0 => ?_⟩
  · refine TrapRun.prefix hX fun ρ1 w1 ⟨_, hy1⟩ => ?_
    exact ((h.sY fr ρ1 b (fun hy => by rw [hy1 hy]; exact hh y _ hyb) hdf hyb).2 w1).2.1 h0
  · refine Runs.append hX fun ρ1 w1 ⟨h1, hy1⟩ => ?_
    refine (((h.sY fr ρ1 b (fun hy => by rw [hy1 hy]; exact hh y _ hyb) hdf hyb).2 w1).2.2 h0).imp
      fun ρ2 w2 hr h2 => ⟨?_, h2⟩
    rw [h.fY.frame hr h.kxlt]
    exact h1

theorem udiv_finish (hR : Refines F isem) (hMR : MRStable F MR) (hw : ty.width ≤ 64)
    {results : List Nat} (h : DivOperands F isem ctx ty x y false st s1 s2 kx ky msX msY) :
    LowerInstOk isem MR env cp ctx (.div .udiv ty x y) results st [[.vreg s2.nextVreg .int]]
      ((s2.fresh .int).2.emit
        (.aluRRR .uDiv (szOf ty.width) (.vreg s2.nextVreg .int) (.vreg kx .int) (.vreg ky .int)))
      (msX ++ msY ++ [.aluRRR .uDiv (szOf ty.width) (.vreg s2.nextVreg .int) (.vreg kx .int)
        (.vreg ky .int)]) ∧
    ((s2.fresh .int).2.emit
        (MInst.aluRRR .uDiv (szOf ty.width) (.vreg s2.nextVreg .int) (.vreg kx .int) (.vreg ky .int))).emitted =
      st.emitted ++ (msX ++ msY ++ [MInst.aluRRR .uDiv (szOf ty.width) (.vreg s2.nextVreg .int)
        (.vreg kx .int) (.vreg ky .int)]).toArray := by
  have hf := (h.fX.append h.fY).append (Frag.fresh_emit s2
    (m := MInst.aluRRR .uDiv (szOf ty.width) (.vreg s2.nextVreg .int) (.vreg kx .int) (.vreg ky .int))
    (by rw [vdefs_aluRRR']; simp))
  refine ⟨lowerInstOk_div hMR hf.mono hf.defs (h.fX.append h.fY).mono ?_, hf.emitted⟩
  intro fr ρ w a b _ hh hdf hxa hyb
  obtain ⟨hu, hukx, huky⟩ := h.uses hh hdf hxa hyb
  obtain ⟨hky, htr, hrun⟩ := h.run hh hdf hxa hyb w
  refine ⟨hu.append ?_, fun c hc => ?_, fun q hq => ?_⟩
  · intro m hm u hu'
    simp only [List.mem_singleton] at hm
    subst hm
    rw [vuseNums_aluRRR'] at hu'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu'
    rcases hu' with rfl | rfl
    · exact hukx
    · exact huky
  · obtain ⟨h0, rfl⟩ := udiv_trap hc
    exact (htr h0).append
  · obtain ⟨h0, rfl⟩ := udiv_ok hq
    refine Runs.append (hrun h0) fun ρ1 w1 ⟨h1, h2⟩ => ?_
    refine (runs_udiv hR _ _ _ _ ρ1 w1).imp fun ρ' _ _ e => ?_
    rw [e, upd_same]
    exact udiv_vholds hw h1 h2

theorem urem_finish (hR : Refines F isem) (hMR : MRStable F MR) (hw : ty.width ≤ 64)
    {results : List Nat} (h : DivOperands F isem ctx ty x y false st s1 s2 kx ky msX msY) :
    let m1 := MInst.aluRRR .uDiv (szOf ty.width) (.vreg s2.nextVreg .int) (.vreg kx .int) (.vreg ky .int)
    let s3 := (s2.fresh .int).2.emit m1
    let m2 := MInst.aluRRRR .mSub (szOf ty.width) (.vreg s3.nextVreg .int) (.vreg s2.nextVreg .int)
      (.vreg ky .int) (.vreg kx .int)
    LowerInstOk isem MR env cp ctx (.div .urem ty x y) results st [[.vreg s3.nextVreg .int]]
      ((s3.fresh .int).2.emit m2) (msX ++ msY ++ ([m1] ++ [m2])) ∧
    ((s3.fresh .int).2.emit m2).emitted = st.emitted ++ (msX ++ msY ++ ([m1] ++ [m2])).toArray := by
  intro m1 s3 m2
  have hf1 : Frag s2 s3 [m1] := Frag.fresh_emit s2 (by simp [m1, vdefs_aluRRR'])
  have hf2 : Frag s3 ((s3.fresh .int).2.emit m2) [m2] :=
    Frag.fresh_emit s3 (by simp [m2, vdefs_aluRRRR'])
  have hf := (h.fX.append h.fY).append (hf1.append hf2)
  have hs3 : s3.nextVreg = s2.nextVreg + 1 := by simp [s3, LState.emit, LState.fresh]
  refine ⟨lowerInstOk_div hMR hf.mono hf.defs (by have := (h.fX.append h.fY).mono; omega) ?_,
    hf.emitted⟩
  intro fr ρ w a b _ hh hdf hxa hyb
  obtain ⟨hu, hukx, huky⟩ := h.uses hh hdf hxa hyb
  obtain ⟨hky, htr, hrun⟩ := h.run hh hdf hxa hyb w
  have hkx := h.kxlt
  have hs12 := h.fY.mono
  refine ⟨hu.append ?_, fun c hc => ?_, fun q hq => ?_⟩
  · intro m hm u hu'
    simp only [List.mem_append, List.mem_singleton] at hm
    rcases hm with rfl | rfl
    · simp only [m1, vuseNums_aluRRR', List.mem_cons, List.not_mem_nil, or_false] at hu'
      rcases hu' with rfl | rfl
      · exact hukx
      · exact huky
    · simp only [m2, vuseNums_aluRRRR', List.mem_cons, List.not_mem_nil, or_false] at hu'
      rcases hu' with rfl | rfl | rfl
      · exact .inl (by have := (h.fX.append h.fY).mono; omega)
      · exact huky
      · exact hukx
  · obtain ⟨h0, rfl⟩ := urem_trap hc
    exact (htr h0).append
  · obtain ⟨h0, rfl⟩ := urem_ok hq
    refine Runs.append (hrun h0) fun ρ1 w1 ⟨h1, h2⟩ => ?_
    refine Runs.append (runs_udiv hR _ _ _ _ ρ1 w1) fun ρ2 w2 e2 => ?_
    refine (runs_msub hR _ _ _ _ _ ρ2 w2).imp fun ρ' _ _ e => ?_
    rw [e, upd_same, e2, upd_same, div_upd_ne (by omega : kx ≠ s2.nextVreg),
      div_upd_ne (by omega : ky ≠ s2.nextVreg)]
    exact urem_vholds hw h1 h2

end Finish

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
  obtain ⟨h172⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 25 172 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨h492⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 492 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨h698⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 698 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨hva⟩ : Nonempty (externExtract ctx T.value_array_2 _ st = _) := ⟨‹_›⟩
  obtain ⟨hpr⟩ : Nonempty (externCtor ctx T.put_in_reg _ st = _) := ⟨‹_›⟩
  obtain ⟨hins⟩ : Nonempty (ctx.insts[ii]? = some _) := ⟨‹_›⟩
  obtain ⟨hdd⟩ : Nonempty (V.data 152 2 _ = _) := ⟨‹_›⟩
  obtain ⟨hty⟩ : Nonempty (CTy.int 64 = _) := ⟨‹_›⟩
  rw [hi, Option.some.injEq] at hins
  subst hins
  have hdat := hctx.data ii _ inst hi hic
  rw [← hdd] at hdat
  obtain ⟨ty, x, y, rfl, hety, rfl⟩ := instData_div_inv (op := .udiv) rfl hdat
  rw [ext_value_array_2] at hva
  cases hva
  rw [ctor_put_in_reg_iff] at hpr
  obtain ⟨rx, hrx, rfl, rfl⟩ := hpr
  obtain ⟨tys, htys, hres, -⟩ := hctx.resTys ii _ _ hi hic
  simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
  subst htys
  rw [hres] at hty
  simp only [List.map_cons, List.map_nil, List.head?_cons, Option.getD_some, ofClif_int_width,
    CTy.int.injEq] at hty
  have hD := put_nonzero_in_reg_ok hp hco hR hctx (hn := by omega) (w := 64) (e := 1) (by decide)
    (by decide) h698
  dsimp only at hD
  obtain ⟨ky, msY, rfl, hfY, hky, hsemY⟩ := divisor_sem hR hctx (w := 64) (e := 1) (by decide) (by decide) hvb hD
  obtain ⟨hv2, hs2⟩ := a64_udiv_ok hp hco (by omega) (by decide) h492
  subst hv2
  obtain ⟨hs3, rfl⟩ := output_reg_ok hp hco (by omega) h172
  have hrx' := hctx.valueReg x rx hrx
  subst hrx'
  have hxlt := hvb x _ hrx
  have hdo : DivOperands F isem ctx ty x y false _ _ _ x ky [] msY :=
    { xlt := hxlt, vb := hvb, fX := Frag.nil _, kxlt := hxlt, kxl := .inr rfl,
      sX := fun fr ρ a hh hdf hxa =>
        ⟨UsesLo.nil _ _, fun wd => Runs.nil (divOpnd_of_vholds64 hty.symm (hh x _ hxa))⟩,
      fY := hfY, kyl := hky,
      sY := fun fr ρ b hv hdf hyb => hsemY fr ρ ty b hty.symm hv hdf hyb }
  obtain ⟨hok, hem⟩ := udiv_finish (env := env) (cp := cp) hR hMR (by omega) (results := info.results) hdo
  simp only at hs3
  rw [hs3, hs2]
  rw [show szOf 64 = szOf ty.width by rw [hty]]
  exact ⟨_, hem, _, rfl, hok⟩

set_option maxHeartbeats 8000000 in
include hp in
theorem udiv32_ruleOk (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOk isem MR env cp p rule_lower_1119 := by
  intro f ctx hctx ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _ hmatch heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 400 := ⟨n - 400, by omega⟩
  isel_inv' hp [] at hmatch heval
  obtain ⟨h172⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 25 172 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨h492⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 492 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨h698⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 698 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨h556⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 556 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨hva⟩ : Nonempty (externExtract ctx T.value_array_2 _ st = _) := ⟨‹_›⟩
  obtain ⟨hins⟩ : Nonempty (ctx.insts[ii]? = some _) := ⟨‹_›⟩
  obtain ⟨hdd⟩ : Nonempty (V.data 152 2 _ = _) := ⟨‹_›⟩
  have hb32 : (info.resTys.head?.getD CTy.invalid).bits ≤ 32 := by
    rw [hi, Option.some.injEq] at hins; subst hins; assumption
  rw [hi, Option.some.injEq] at hins
  subst hins
  have hdat := hctx.data ii _ inst hi hic
  rw [← hdd] at hdat
  obtain ⟨ty, x, y, rfl, hety, rfl⟩ := instData_div_inv (op := .udiv) rfl hdat
  rw [ext_value_array_2] at hva
  cases hva
  obtain ⟨tys, htys, hres, -⟩ := hctx.resTys ii _ _ hi hic
  simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
  subst htys
  rw [hres] at hb32 h698
  simp only [List.map_cons, List.map_nil, List.head?_cons, Option.getD_some, ofClif_int_width] at hb32 h698
  have hw32 : ty.width ≤ 32 := hb32
  have hwid := eTy_widths hety
  have hE := zext32_ok hp hco (hn := by omega) h556
  obtain ⟨_, -, rx, hrx, -⟩ := id hE
  have hxlt := hvb x _ hrx
  obtain ⟨kx, msX, rfl, hfX, hkx, hkxl, hsX⟩ :=
    ext_divOpnd hR hctx hvb (w := ty.width) (.inl ⟨rfl, rfl⟩) (.inl hw32) hE
  have hvb2 : ValsBelow ctx _ := fun z r hz => Nat.lt_of_lt_of_le (hvb z r hz) hfX.mono
  have hD := put_nonzero_in_reg_ok hp hco hR hctx (hn := by omega) (w := ty.width) (e := 1) hwid
    (by decide) h698
  try dsimp only at hD
  obtain ⟨ky, msY, rfl, hfY, hky, hsemY⟩ :=
    divisor_sem hR hctx (w := ty.width) (e := 1) hwid (by decide) hvb2 hD
  obtain ⟨hv2, hs2⟩ := a64_udiv_ok hp hco (by omega) (by decide) h492
  subst hv2
  obtain ⟨hs3, rfl⟩ := output_reg_ok hp hco (by omega) h172
  have hdo : DivOperands F isem ctx ty x y false _ _ _ kx ky msX msY :=
    { xlt := hxlt, vb := hvb, fX := hfX, kxlt := hkx, kxl := hkxl,
      sX := fun fr ρ a hh hdf hxa => hsX fr ρ ty a rfl hh hdf hxa,
      fY := hfY, kyl := hky,
      sY := fun fr ρ b hv hdf hyb => hsemY fr ρ ty b rfl hv hdf hyb }
  obtain ⟨hok, hem⟩ := udiv_finish (env := env) (cp := cp) hR hMR (by omega) (results := info.results) hdo
  simp only at hs3
  rw [hs3, hs2]
  rw [show szOf 32 = szOf ty.width by simp [szOf, hw32]]
  exact ⟨_, hem, _, rfl, hok⟩

set_option maxHeartbeats 8000000 in
include hp in
theorem urem64_ruleOk (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOk isem MR env cp p rule_lower_1190 := by
  intro f ctx hctx ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _ hmatch heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 400 := ⟨n - 400, by omega⟩
  isel_inv' hp [] at hmatch heval
  obtain ⟨h172⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 25 172 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨h492⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 492 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨h444⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 444 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨h698⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 698 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨h558⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 558 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨hva⟩ : Nonempty (externExtract ctx T.value_array_2 _ st = _) := ⟨‹_›⟩
  obtain ⟨hins⟩ : Nonempty (ctx.insts[ii]? = some _) := ⟨‹_›⟩
  obtain ⟨hdd⟩ : Nonempty (V.data 152 2 _ = _) := ⟨‹_›⟩
  obtain ⟨hty⟩ : Nonempty (CTy.int 64 = _) := ⟨‹_›⟩
  rw [hi, Option.some.injEq] at hins
  subst hins
  have hdat := hctx.data ii _ inst hi hic
  rw [← hdd] at hdat
  obtain ⟨ty, x, y, rfl, hety, rfl⟩ := instData_div_inv (op := .urem) rfl hdat
  rw [ext_value_array_2] at hva
  cases hva
  obtain ⟨tys, htys, hres, -⟩ := hctx.resTys ii _ _ hi hic
  simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
  subst htys
  rw [hres] at hty
  simp only [List.map_cons, List.map_nil, List.head?_cons, Option.getD_some, ofClif_int_width,
    CTy.int.injEq] at hty
  have hwid := eTy_widths hety
  have hE := zext64_ok hp hco (hn := by omega) h558
  obtain ⟨_, -, rx, hrx, -⟩ := id hE
  have hxlt := hvb x _ hrx
  obtain ⟨kx, msX, rfl, hfX, hkx, hkxl, hsX⟩ :=
    ext_divOpnd hR hctx hvb (w := ty.width) (.inr ⟨rfl, rfl, hty.symm⟩) (.inr hty.symm) hE
  have hvb2 : ValsBelow ctx _ := fun z r hz => Nat.lt_of_lt_of_le (hvb z r hz) hfX.mono
  have hD := put_nonzero_in_reg_ok hp hco hR hctx (hn := by omega) (w := 64) (e := 1) (by decide)
    (by decide) h698
  try dsimp only at hD
  obtain ⟨ky, msY, rfl, hfY, hky, hsemY⟩ :=
    divisor_sem hR hctx (w := 64) (e := 1) (by decide) (by decide) hvb2 hD
  obtain ⟨hv2, hs2⟩ := a64_udiv_ok hp hco (by omega) (by decide) h492
  subst hv2
  obtain ⟨hv4, hs4⟩ := msub_ok hp hco (by omega) (by decide) h444
  subst hv4
  obtain ⟨hs3, rfl⟩ := output_reg_ok hp hco (by omega) h172
  have hdo : DivOperands F isem ctx ty x y false _ _ _ kx ky msX msY :=
    { xlt := hxlt, vb := hvb, fX := hfX, kxlt := hkx, kxl := hkxl,
      sX := fun fr ρ a hh hdf hxa => hsX fr ρ ty a rfl hh hdf hxa,
      fY := hfY, kyl := hky,
      sY := fun fr ρ b hv hdf hyb => hsemY fr ρ ty b hty.symm hv hdf hyb }
  obtain ⟨hok, hem⟩ := urem_finish (env := env) (cp := cp) hR hMR (by omega) (results := info.results) hdo
  simp only at hs3
  rw [hs3, hs4, hs2]
  rw [show szOf 64 = szOf ty.width by rw [hty]]
  exact ⟨_, hem, _, rfl, hok⟩

end Root

end Backend.Proof
