import FV.Backend.Proof.IselCmpEmit

/-!
# Family C root rules: `icmp` (2215), `uextend (icmp)` (1281)

The right-hand side is `output_reg (lower_cond_result_bool (emit_icmp cc x y))`: the
condition code (`emit_icmp_ok`), then the flag instruction and `cset` into a fresh vreg
(`lcrb_ok`, `lcrb_run`).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-! ## `LowerInstOk` from a `Runs` fact -/

/-- **`LowerInstOk` for a pure one-result instruction** whose code runs (`Runs`, per world) to
a vreg file holding the result in `d`. -/
theorem lowerInstOk_runs {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT} {env : Clif.Env}
    {cp : Clif.Program} {ctx : Ctx} {inst : Clif.Inst} {results : List Nat} {st st' : LState}
    {ms : List MInst} {d : Nat} (hMR : MRStable F MR)
    (hmono : st.nextVreg ≤ st'.nextVreg)
    (hdefs : ∀ m ∈ ms, ∀ d ∈ vdefs m, st.nextVreg ≤ d ∧ d < st'.nextVreg)
    (htrap : explicitTrapInst inst = false)
    (hrun : ∀ (fr : Clif.Frame) (cm : Clif.Mem) (ρ : Nat → CV) (w : Arm.ArmState) vals cm',
      fr.func = ctx.func → ValsHeld fr ρ → DFGCons ctx fr →
      instOutcome env cp fr cm inst = .ok (vals, cm') →
      cm' = cm ∧ UsesOk st fr ms ∧ (st.nextVreg ≤ d ∨ (fr.regs d).isSome) ∧
        ∃ v, vals = [v] ∧ Runs F isem ms ρ w (fun ρ' _ => VHolds v (ρ' d))) :
    LowerInstOk isem MR env cp ctx inst results st [[.vreg d .int]] st' ms := by
  refine ⟨hmono, hdefs, ?_⟩
  intro fr cm ρ w hf hv hdfg hmr
  split
  · rename_i vals cm' ho
    obtain ⟨rfl, hu, hd, v, rfl, ρ', w', hs, hw, hh⟩ := hrun fr cm ρ w vals cm' hf hv hdfg ho
    refine ⟨hu, ρ', w', hs, .inr ⟨rfl, ?_⟩, hMR _ _ _ _ hw hmr⟩
    intro j rs val hrs hval
    match j, hrs, hval with
    | 0, hrs, hval =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hrs hval
      subst hrs; subst hval
      exact ⟨d, .int, rfl, hd, hh⟩
    | _ + 1, hrs, _ => simp at hrs
  · intro h; rw [htrap] at h; cases h
  · trivial

/-! ## A condition turned into a 0/1 register -/

theorem vholds_bool8 (b : Bool) :
    VHolds ⟨.i8, Clif.Sem.bool8 b⟩ (ofX (if b then 1#64 else 0#64)) := by
  cases b <;> rfl

/-- **Condition code followed by `lower_cond_result_bool`**: the fresh vreg `st1.nextVreg`
holds the condition as 0/1. -/
theorem condCode_lcrb {F : BitVec 64 → Prop} {isem : Sem} (hR : Refines F isem) {ctx : Ctx}
    {st st1 : LState} {c : V} {T : Clif.Frame → Bool → Prop} (hcc : CondCode F isem ctx st st1 c T)
    {m : MInst} {cond : Cond} (hflag : CondFlag cmpImm0 c m cond) :
    st.nextVreg ≤ st1.nextVreg ∧
    ∃ ms, Frag st (((st1.fresh .int).2.emit m).emit (.cset (.vreg st1.nextVreg .int) cond)) ms ∧
      ∀ (fr : Clif.Frame) (ρ : Nat → CV) (b : Bool), ValsHeld fr ρ → DFGCons ctx fr → T fr b →
        UsesOk st fr ms ∧ ∀ w, Runs F isem ms ρ w
          (fun ρ' _ => ρ' st1.nextVreg = ofX (if b then 1#64 else 0#64)) := by
  obtain ⟨ms, hf, hsh, hr⟩ := hcc
  refine ⟨hf.mono, ms ++ [m, .cset (.vreg st1.nextVreg .int) cond],
    hf.append (condFlag_cset_code cmpImm0_regs hflag hsh st1).1, fun fr ρ b hh hdf hT => ?_⟩
  obtain ⟨hu, hsh', hrun⟩ := hr fr ρ b hh hdf hT
  refine ⟨UsesLo.append hu (condFlag_cset_code cmpImm0_regs hflag hsh' st1).2, fun w => ?_⟩
  refine Runs.append (hrun w) fun ρ1 w1 hs => (lcrb_run hR hflag hsh' hs st1.nextVreg w1).imp ?_
  intro ρ' _ _ h
  rw [h]; simp [upd]

section
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)

set_option maxHeartbeats 2000000 in
include hp hc in
theorem cmp_output_reg_ok {n : Nat} (hn : 40 ≤ n) {r : Reg} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 25 172 [.reg r] s v s') :
    s'.1 = s.1 ∧ v = .regsVec [[r]] := by
  isel_split' hp hc h 172
  all_goals (try (isel_refute hp at hm; done))
  all_goals isel_inv' hp [] at hm he
  all_goals simp_all

end

/-! ## The `icmp` instruction -/

set_option maxRecDepth 20000 in
theorem variantNames_IntCompare : (variantNames 152)[14]? = some "IntCompare" := rfl
set_option maxRecDepth 20000 in
theorem variantNames_Icmp : (variantNames 151)[72]? = some "Icmp" := rfl

theorem instData_icmp_inv {f : Clif.Function} {cl : Clif.Inst} {w1 w2 : V}
    (h : instData f cl = .ok (.data 152 14 [.data 151 72 [], w1, w2])) :
    ∃ cc ty x y, cl = .icmp cc ty x y ∧ w1 = .values [x, y] ∧ w2 = .data 145 (ccIdx cc) [] := by
  obtain ⟨hf, -⟩ := instData_inv_names h
  rw [variantNames_IntCompare] at hf
  cases cl <;> simp [instNames] at hf
  rename_i cc ty x y
  refine ⟨cc, ty, x, y, rfl, ?_⟩
  simp only [instData] at h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨-, -, h3⟩ := mkVariant_eq_data h
    simp only [List.cons.injEq, mkVariant_intcc] at h3
    exact ⟨h3.2.1, h3.2.2.1⟩
  · cases h

theorem evalInst_icmp_ok {fr : Clif.Frame} {cm cm' : Clif.Mem} {cc : Clif.IntCC} {ty : Clif.Ty}
    {x y : Nat} {vals : List Clif.Val}
    (h : Clif.evalInst fr cm (.icmp cc ty x y) = .ok (vals, cm')) :
    ∃ a b, fr.getAs x ty = .ok a ∧ fr.getAs y ty = .ok b ∧
      vals = [⟨.i8, Clif.Sem.icmp cc a b⟩] ∧ cm' = cm := by
  simp only [Clif.evalInst] at h
  cases hx : fr.getAs x ty with
  | ok a =>
    cases hy : fr.getAs y ty with
    | ok b =>
      rw [hx, hy] at h
      simp only [bind, Clif.Res.bind, pure] at h
      cases h
      exact ⟨a, b, rfl, rfl, rfl, rfl⟩
    | trap c => rw [hx, hy] at h; cases h
    | stuck m => rw [hx, hy] at h; cases h
  | trap c => rw [hx] at h; cases h
  | stuck m => rw [hx] at h; cases h

set_option maxRecDepth 20000 in
theorem cmp_variantNames_Unary : (variantNames 152)[29]? = some "Unary" := rfl
set_option maxRecDepth 20000 in
theorem cmp_variantNames_Uextend : (variantNames 151)[141]? = some "Uextend" := rfl

theorem instData_uextend_inv {f : Clif.Function} {cl : Clif.Inst} {w : V}
    (h : instData f cl = .ok (.data 152 29 [.data 151 141 [], w])) :
    ∃ ty z, cl = .extend .uextend ty z ∧ eTy ty = true ∧ w = .value z := by
  obtain ⟨hf, ho⟩ := instData_inv_names h
  rw [cmp_variantNames_Unary] at hf
  rw [cmp_variantNames_Uextend] at ho
  cases cl <;> simp [instNames] at hf ho
  · rename_i op _ _
    cases op <;> simp [unaryOpcode] at ho
  · rename_i op ty z
    cases op <;> simp at ho
    refine ⟨ty, z, rfl, ?_⟩
    simp only [instData] at h
    split at h
    · rename_i he
      simp only [pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨-, -, h3⟩ := mkVariant_eq_data h
      simp only [List.cons.injEq] at h3
      exact ⟨he, h3.2.1⟩
    · cases h

theorem evalInst_uextend_ok {fr : Clif.Frame} {cm cm' : Clif.Mem} {ty : Clif.Ty} {z : Nat}
    {vals : List Clif.Val} (h : Clif.evalInst fr cm (.extend .uextend ty z) = .ok (vals, cm')) :
    ∃ v, fr.regs z = some v ∧ v.ty.width < ty.width ∧
      vals = [⟨ty, Clif.Sem.uextend ty.width v.bits⟩] ∧ cm' = cm := by
  simp only [Clif.evalInst] at h
  cases hz : fr.get z with
  | ok v =>
    rw [hz] at h
    simp only [bind, Clif.Res.bind, Clif.Res.check] at h
    split at h
    · rename_i hc
      simp only [pure] at h
      cases h
      refine ⟨v, ?_, ?_, rfl, rfl⟩
      rotate_left
      · split at hc
        · exact of_decide_eq_true ‹_›
        · cases hc
      unfold Clif.Frame.get at hz
      cases hr : fr.regs z <;> simp [hr, Clif.Res.ofOption] at hz
      rw [hz]
    all_goals cases h
  | trap c => rw [hz] at h; cases h
  | stuck m => rw [hz] at h; cases h

theorem vholds_uextend_bool8 {ty : Clif.Ty} (he : eTy ty = true) (b : Bool) :
    VHolds ⟨ty, Clif.Sem.uextend ty.width (Clif.Sem.bool8 b)⟩ (ofX (if b then 1#64 else 0#64)) := by
  cases ty <;> simp [eTy] at he <;> cases b <;> rfl

/-! ## `is_nonzero_cmp` -/

theorem truthy_bool8 (c : Bool) : Clif.Sem.truthy (Clif.Sem.bool8 c) = c := by cases c <;> rfl

theorem truthy_uextend8 {w : Nat} (hw : 8 ≤ w) (x : BitVec 8) :
    Clif.Sem.truthy (Clif.Sem.uextend w x) = Clif.Sem.truthy x := by
  simp only [Clif.Sem.truthy, Clif.Sem.uextend, bne]
  congr 1
  have hlt := x.isLt
  have : 2 ^ 8 ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) hw
  cases h : x == 0 <;> simp only [beq_iff_eq, beq_eq_false_iff_ne, ne_eq] at h ⊢
  · intro h'; apply h; apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat h'
    simp [BitVec.toNat_setWidth] at this
    rw [Nat.mod_eq_of_lt (by omega)] at this; simpa using this
  · subst h; simp

/-- A value defined by `icmp cc ty a b` is the truth of `cc` on `a`, `b`. -/
theorem icmp_truthy {ctx : Ctx} {fr : Clif.Frame} (hdf : DFGCons ctx fr) {z j : Nat} {info : IInfo}
    {cc : Clif.IntCC} {ty : Clif.Ty} {a b : Nat} {v : Clif.Val} (hj : ctx.defInst? z = some j)
    (hi : ctx.insts[j]? = some info) (hcl : info.clif = some (.icmp cc ty a b))
    (hv : fr.regs z = some v) : v.ty = .i8 ∧ IcmpT cc a b fr (Clif.Sem.truthy v.bits) := by
  obtain ⟨vals, hev, hl⟩ := hdf.1 z j info _ v hj hi hcl rfl hv
  obtain ⟨a', b', hx, hy, rfl, -⟩ := evalInst_icmp_ok (hev default)
  have := lookup_zip_single hl
  subst this
  exact ⟨rfl, ty, a', b', getAs_ok hx, getAs_ok hy, truthy_bool8 _⟩

theorem cmp_defClif_inv {ctx : Ctx} {x : Nat} {cl : Clif.Inst} (h : ctx.defClif? x = some cl) :
    ∃ j info, ctx.defInst? x = some j ∧ ctx.insts[j]? = some info ∧ info.clif = some cl := by
  unfold Ctx.defClif? at h
  cases hd : ctx.defInst? x with
  | none => simp [hd] at h
  | some j =>
    cases hi : ctx.insts[j]? with
    | none => simp [hd, hi] at h
    | some info =>
      simp [hd, hi] at h
      exact ⟨j, info, rfl, hi, h⟩

section
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)

set_option maxHeartbeats 8000000 in
include hp hc in
/-- **`is_nonzero_cmp`** on an integer value: the condition is the value's truth. -/
theorem is_nonzero_cmp_ok {F : BitVec 64 → Prop} {isem : Sem} (hR : Refines F isem)
    {f : Clif.Function} (hctx : CtxInv f ctx) {n : Nat} (hn : 300 ≤ n) {x : Nat}
    {s s' : LState × Array RuleId} {c : V} (hvb : ValsBelow ctx s.1)
    (h : ApplyInternal p (sem ctx) cfg n 123 650 [.value x] s c s') :
    CondCode F isem ctx s.1 s'.1 c
      (fun fr b => ∃ v, fr.regs x = some v ∧ b = Clif.Sem.truthy v.bits) := by
  isel_split' hp hc h 650
  all_goals (try (isel_refute hp at hm; done))
  all_goals isel_inv' hp [] at hm he
  · -- 4965 (fcmp): no `fcmp` in E
    rcases ‹(∃ _ _, _) ∨ _› with ⟨_, _, _, rfl⟩ | ⟨-, rfl⟩ <;> isel_inv_simp [] at * <;> isel_destruct <;>
      subst_vars <;> isel_inv_simp [] at * <;> isel_destruct <;> subst_vars
    all_goals
      obtain ⟨hj⟩ : Nonempty (ctx.defInst? _ = some _) := ⟨‹_›⟩
      obtain ⟨hi⟩ : Nonempty (ctx.insts[_]? = some _) := ⟨‹_›⟩
      obtain ⟨hd⟩ : Nonempty (V.data 152 11 _ = _) := ⟨‹_›⟩
      exact (opcode_absurd hctx hj hi hd rfl (by decide)).elim
  · -- 4966 (maybe_uextend (icmp …)): `emit_icmp`
    rcases ‹(∃ _ _, _) ∨ _› with ⟨uty, z, hdc, rfl⟩ | ⟨-, rfl⟩ <;> isel_inv_simp [] at * <;>
      isel_destruct <;> subst_vars <;> isel_inv_simp [] at * <;> isel_destruct <;> subst_vars
    all_goals
      obtain ⟨hj⟩ : Nonempty (ctx.defInst? _ = some _) := ⟨‹_›⟩
      obtain ⟨hi⟩ : Nonempty (ctx.insts[_]? = some _) := ⟨‹_›⟩
      obtain ⟨hd⟩ : Nonempty (V.data 152 14 _ = _) := ⟨‹_›⟩
      obtain ⟨cl, hcl, hdat⟩ := ctxInv_clif hctx hj hi
      rw [← hd] at hdat
      obtain ⟨cc, ty, a, b, rfl, rfl, rfl⟩ := instData_icmp_inv hdat
      isel_inv_simp [] at *
      isel_destruct
      subst_vars
      obtain ⟨h652⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 123 652 _ _ _ _) := ⟨‹_›⟩
      refine (emit_icmp_ok hp hc hR hctx (hn := by omega) hvb h652).weaken ?_
      rintro fr ρ bb hh hdf ⟨v, hv, rfl⟩
    · obtain ⟨jx, infox, hjx, hix, hclx⟩ := cmp_defClif_inv hdc
      obtain ⟨vals, hev, hl⟩ := hdf.1 x jx infox _ v hjx hix hclx rfl hv
      obtain ⟨vz, hzv, hlt, rfl, -⟩ := evalInst_uextend_ok (hev default)
      have := lookup_zip_single hl
      subst this
      obtain ⟨hty8, hT⟩ := icmp_truthy hdf hj hi hcl hzv
      obtain ⟨vt, vb⟩ := vz
      simp only at hty8
      subst hty8
      change BitVec 8 at vb
      have h8 : 8 < uty.width := hlt
      have e := truthy_uextend8 (w := uty.width) (by omega) vb
      show IcmpT cc a b fr (Clif.Sem.truthy (Clif.Sem.uextend (w := 8) uty.width vb))
      rw [e]
      exact hT
    · exact (icmp_truthy hdf hj hi hcl hv).2
  · -- 4967: `is_nonzero`
    obtain ⟨h651⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 123 651 _ _ _ _) := ⟨‹_›⟩
    exact is_nonzero_ok hp hc hR hctx (hn := by omega) hvb h651

end

section Root
variable {p : Program} (hp : Data p)

set_option maxHeartbeats 8000000 in
include hp in
theorem icmp_ruleOk (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOk isem MR env cp p rule_lower_2215 := by
  intro f ctx hctx ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _ hmatch heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 400 := ⟨n - 400, by omega⟩
  isel_inv' hp [] at hmatch heval
  rename_i hins hdd h652
  rw [hi, Option.some.injEq] at hins
  subst hins
  have hdat := hctx.data ii _ inst hi hic
  rw [← hdd] at hdat
  obtain ⟨cc, ty, x, y, rfl, rfl, rfl⟩ := instData_icmp_inv hdat
  isel_inv_simp [] at *
  isel_destruct
  subst_vars
  obtain ⟨h715⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 715 _ _ _ _) := ⟨‹_›⟩
  have hE := emit_icmp_ok hp hco hR hctx (hn := by omega) hvb h652
  obtain ⟨m0, cond, hflag, rfl, hst⟩ := lcrb_ok hp hco (hn := by omega) hE.shape h715
  isel_call hp hco [cmp_output_reg_ok]
  obtain ⟨hmono, ms, hf, hsem⟩ := condCode_lcrb hR hE hflag
  rw [hst]
  refine ⟨ms, hf.emitted, _, rfl, lowerInstOk_runs hMR hf.mono hf.defs rfl ?_⟩
  intro fr cm ρ w vals cm' _ hh hdf ho
  obtain ⟨a, b, hx, hy, rfl, rfl⟩ := evalInst_icmp_ok ho
  obtain ⟨hu, hr⟩ := hsem fr ρ _ hh hdf ⟨ty, a, b, getAs_ok hx, getAs_ok hy, rfl⟩
  exact ⟨rfl, hu, .inl hmono, _, rfl, (hr w).imp fun ρ' _ _ h => by
    rw [h]; exact vholds_bool8 _⟩

set_option maxHeartbeats 8000000 in
include hp in
theorem uextend_icmp_ruleOk (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOk isem MR env cp p rule_lower_1281 := by
  intro f ctx hctx ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _ hmatch heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 400 := ⟨n - 400, by omega⟩
  isel_inv' hp [] at hmatch heval
  rename_i hins hdd h652 hres
  rw [hi, Option.some.injEq] at hins
  subst hins
  have hdat := hctx.data ii _ inst hi hic
  rw [← hdd] at hdat
  obtain ⟨ty, z, rfl, hety, rfl⟩ := instData_uextend_inv hdat
  isel_inv_simp [] at *
  isel_destruct
  subst_vars
  isel_inv_simp [] at *
  isel_destruct
  subst_vars
  rename_i hj _ hi2 hd2
  obtain ⟨cl, hcl, hdat2⟩ := ctxInv_clif hctx hj hi2
  rw [← hd2] at hdat2
  obtain ⟨cc, ty', x, y, rfl, rfl, rfl⟩ := instData_icmp_inv hdat2
  isel_inv_simp [] at *
  isel_destruct
  subst_vars
  obtain ⟨h652⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 123 652 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨h715⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 715 _ _ _ _) := ⟨‹_›⟩
  have hE := emit_icmp_ok hp hco hR hctx (hn := by omega) hvb h652
  obtain ⟨m0, cond, hflag, rfl, hst⟩ := lcrb_ok hp hco (hn := by omega) hE.shape h715
  isel_call hp hco [cmp_output_reg_ok]
  obtain ⟨hmono, ms, hf, hsem⟩ := condCode_lcrb hR hE hflag
  rw [hst]
  refine ⟨ms, hf.emitted, _, rfl, lowerInstOk_runs hMR hf.mono hf.defs rfl ?_⟩
  intro fr cm ρ w vals cm' _ hh hdf ho
  obtain ⟨v, hzv, -, rfl, rfl⟩ := evalInst_uextend_ok ho
  obtain ⟨vals2, hev, hl⟩ := hdf.1 z _ _ _ v hj hi2 hcl rfl hzv
  obtain ⟨a, b, hx, hy, rfl, -⟩ := evalInst_icmp_ok (hev default)
  have hv := lookup_zip_single hl
  subst hv
  obtain ⟨hu, hr⟩ := hsem fr ρ _ hh hdf ⟨ty', a, b, getAs_ok hx, getAs_ok hy, rfl⟩
  exact ⟨rfl, hu, .inl hmono, _, rfl, (hr w).imp fun ρ' _ _ h => by
    rw [h]; exact vholds_uextend_bool8 hety _⟩

end Root

end Backend.Proof
