import FV.Backend.Proof.IselCmpRoot

/-!
# Family C: `select` (2267) and integer min/max (1222/1224/1226/1228)

`lower_select ty c x y` on a condition of E: the flag instruction of `c` then `csel` into a
fresh vreg (`lower_select_cond`, integer types only).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

theorem ofV_csel' (rd rn rm : Reg) (c : V) :
    MInst.ofV (.data 58 31 [.reg rd, c, .reg rn, .reg rm]) = c.cond?.map (.csel rd rn rm) := by
  have e1 : MInst.ofV (.data 58 31 [.reg rd, c, .reg rn, .reg rm]) =
      (do return .csel rd rn rm (← c.cond?)) := rfl
  rw [e1]; cases c.cond? <;> rfl

theorem ofV_cmpXzr {i : Nat} {sz : OperandSize} (hi : OperandSize.ofIdx? i = some sz) (k : Nat) :
    MInst.ofV (.data 58 2 [.data 59 10 [], .data 93 i [], .reg .xzr, .reg (.vreg k .int), .reg .xzr]) =
      some (cmpXzr sz k) := by
  have e : (V.data 93 i []).size? = OperandSize.ofIdx? i := rfl
  have e1 : MInst.ofV (.data 58 2 [.data 59 10 [], .data 93 i [], .reg .xzr, .reg (.vreg k .int), .reg .xzr]) =
      (do return .aluRRR .subS (← (V.data 93 i []).size?) .xzr (.vreg k .int) .xzr) := rfl
  rw [e1, e, hi]; rfl

section
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)

set_option maxHeartbeats 4000000 in
include hp hc in
theorem lower_select_cond_ok {n : Nat} (hn : 60 ≤ n) {w : Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64)
    {mi cd : V} {x y : Nat} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 22 660 [.ty (.int w), .data 47 1 [mi], cd, .value x, .value y]
      s v s') :
    ∃ m1 rx ry c, MInst.ofV mi = some m1 ∧ ctx.valueReg? x = some rx ∧ ctx.valueReg? y = some ry ∧
      cd.cond? = some c ∧ v = .regs [(s.1.fresh .int).1] ∧
      s'.1 = (((s.1.fresh .int).2.emit m1).emit (.csel (s.1.fresh .int).1 rx ry c)) := by
  rcases hw with rfl | rfl | rfl | rfl <;>
  isel_split' hp hc h 660 <;>
  (try (isel_refute hp at hm; done))
  all_goals (try isel_refute hp at hm)
  all_goals try (exact absurd hm.1 (by decide))
  all_goals try (obtain ⟨_, _, ⟨_, h1, _⟩, _⟩ := hm; cases h1; done)
  all_goals isel_inv' hp [] at hm he
  all_goals
    obtain ⟨h0⟩ : Nonempty (externCtor ctx T.ty_int_ref_scalar_64 _ _ = _) := ⟨‹_›⟩
    cases h0
    isel_call hp hc [csel_ok, with_flags_ok]
    obtain ⟨h1⟩ : Nonempty (MInst.ofV (.data 58 31 _) = _) := ⟨‹_›⟩
    rw [ofV_csel', Option.map_eq_some_iff] at h1
    obtain ⟨c, hcd, rfl⟩ := h1
    obtain ⟨h2⟩ : Nonempty ((_ : LState × Array RuleId).fst = ((_ : LState × Array RuleId).fst.fresh RegClass.int).snd) := ⟨‹_›⟩
    exact ⟨_, ‹_›, _, ‹_›, _, ‹_›, c, hcd, rfl, by rw [h2]⟩

set_option maxHeartbeats 8000000 in
include hp hc in
theorem lower_select_ok {n : Nat} (hn : 100 ≤ n) {w : Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64)
    {c : V} {P : Nat → Prop} (hsh : CondShape c P) {x y : Nat} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 22 659 [.ty (.int w), c, .value x, .value y] s v s') :
    ∃ m cond rx ry, CondFlag cmpXzr c m cond ∧ ctx.valueReg? x = some rx ∧ ctx.valueReg? y = some ry ∧
      v = .regs [(s.1.fresh .int).1] ∧
      s'.1 = (((s.1.fresh .int).2.emit m).emit (.csel (s.1.fresh .int).1 rx ry cond)) := by
  rcases hsh with ⟨k, i, sz, rfl, hi, -⟩ | ⟨k, i, sz, rfl, hi, -⟩ | ⟨mi, m, cond, rfl, hm0, -⟩ <;>
  isel_split' hp hc h 659 <;>
  (try (isel_refute hp at hm; done))
  all_goals try (first
    | (obtain ⟨m', s1, h2⟩ := hpre rule_inst_5320 (List.mem_cons_self ..)
       revert h2
       isel_eval [rule_inst_5320, hp.t2236, hp.t2237, hp.t2238]
       simp
       done)
    | (obtain ⟨m', s1, h2⟩ := hpre rule_inst_5322 (List.mem_cons_of_mem _ (List.mem_cons_self ..))
       revert h2
       isel_eval [rule_inst_5322, hp.t2236, hp.t2237, hp.t2238]
       simp
       done)
    | (obtain ⟨m', s1, h2⟩ := hpre rule_inst_5324 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
       revert h2
       isel_eval [rule_inst_5324, hp.t2236, hp.t2237, hp.t2238]
       simp
       done)
    )
  all_goals isel_inv' hp [] at hm he
  all_goals isel_call hp hc [cmp_ok]
  all_goals
    obtain ⟨h660⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 22 660 _ _ _ _) := ⟨‹_›⟩
    obtain ⟨m1, rx, ry, c, hm1, hrx, hry, hc', rfl, hs⟩ :=
      lower_select_cond_ok hp hc (hn := by omega) (by decide) h660
    try simp only at hs
    clear h660
    subst_vars
    first
      | (rw [ofV_cmpXzr hi] at hm1; cases hm1
         rw [V.cond?_data, cond_ofIdx_0] at hc'; cases hc'
         exact ⟨_, _, .inl ⟨k, i, sz, rfl, hi, rfl, rfl⟩, _, hrx, _, hry, by simp_all, by simp_all⟩)
      | (rw [ofV_cmpXzr hi] at hm1; cases hm1
         rw [V.cond?_data, cond_ofIdx_1] at hc'; cases hc'
         exact ⟨_, _, .inr (.inl ⟨k, i, sz, rfl, hi, rfl, rfl⟩), _, hrx, _, hry, by simp_all, by simp_all⟩)
      | (rw [hm0] at hm1; cases hm1
         rw [V.cond?_data, cond_ofIdx_idx] at hc'; cases hc'
         exact ⟨_, _, .inr (.inr ⟨mi, rfl, hm0⟩), _, hrx, _, hry, by simp_all, by simp_all⟩)

end

/-! ## The code of `lower_select`: condition, flag instruction, `csel` -/

theorem vdefs_csel (d a b : Nat) (c : Cond) :
    vdefs (.csel (.vreg d .int) (.vreg a .int) (.vreg b .int) c) = [d] := rfl
theorem vuseNums_csel (d a b : Nat) (c : Cond) :
    vuseNums (.csel (.vreg d .int) (.vreg a .int) (.vreg b .int) c) = [a, b] := rfl

theorem setWidth_ofX_lo64 {w : Nat} (hw : w ≤ 64) (z : CV) :
    (ofX (lo64 z)).setWidth w = z.setWidth w := by
  simp only [ofX, lo64]
  rw [BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_setWidth_of_le _ hw]

/-- **Condition code, then `lower_select`'s flag instruction and `csel`**: the fresh vreg
`st1.nextVreg` holds `x` if the condition holds, else `y`. -/
theorem condCode_csel {F : BitVec 64 → Prop} {isem : Sem} (hR : Refines F isem) {ctx : Ctx}
    {st st1 : LState} {c : V} {T : Clif.Frame → Bool → Prop} (hcc : CondCode F isem ctx st st1 c T)
    {m : MInst} {cond : Cond} (hflag : CondFlag cmpXzr c m cond) {x y : Nat}
    (hx : x < st.nextVreg) (hy : y < st.nextVreg) :
    st.nextVreg ≤ st1.nextVreg ∧
    ∃ ms, Frag st (((st1.fresh .int).2.emit m).emit
        (.csel (.vreg st1.nextVreg .int) (.vreg x .int) (.vreg y .int) cond)) ms ∧
      ∀ (fr : Clif.Frame) (ρ : Nat → CV) (b : Bool), ValsHeld fr ρ → DFGCons ctx fr → T fr b →
        (fr.regs x).isSome → (fr.regs y).isSome →
        UsesOk st fr ms ∧ ∀ w, Runs F isem ms ρ w
          (fun ρ' _ => ρ' st1.nextVreg = ofX (if b then lo64 (ρ x) else lo64 (ρ y))) := by
  obtain ⟨ms, hf, hsh, hr⟩ := hcc
  obtain ⟨-, -, hd, -⟩ := hflag.shape cmpXzr_regs hsh
  refine ⟨hf.mono, ms ++ [m, .csel (.vreg st1.nextVreg .int) (.vreg x .int) (.vreg y .int) cond],
    hf.append (Frag.fresh_emit2 st1 hd (by rw [vdefs_csel]; exact List.Subset.refl _)),
    fun fr ρ b hh hdf hT hxs hys => ?_⟩
  obtain ⟨hu, hsh', hrun⟩ := hr fr ρ b hh hdf hT
  obtain ⟨-, -, -, hum⟩ := hflag.shape cmpXzr_regs hsh'
  refine ⟨UsesLo.append hu ?_, fun w => ?_⟩
  · intro i hi u hu'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact hum u hu'
    · rw [vuseNums_csel] at hu'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu'
      rcases hu' with rfl | rfl
      · exact .inr hxs
      · exact .inr hys
  refine Runs.append ((hrun w).imp fun ρ1 w1 hs1 hc1 => And.intro hs1 hc1) fun ρ1 w1 ⟨hs1, hc1⟩ => ?_
  obtain ⟨ps, hps, hb⟩ := hflag.sem setsFlags_cmpXzr hc1
  refine (runs_flags_csel hR hps hb st1.nextVreg x y w1).imp fun ρ' _ _ h => ?_
  rw [h, hf.frame hs1 hx, hf.frame hs1 hy]
  simp [upd]

/-! ## The `select` instruction -/

set_option maxRecDepth 20000 in
theorem variantNames_Ternary : (variantNames 152)[24]? = some "Ternary" := rfl
set_option maxRecDepth 20000 in
theorem variantNames_Select : (variantNames 151)[65]? = some "Select" := rfl

theorem instData_select_inv {f : Clif.Function} {cl : Clif.Inst} {w : V}
    (h : instData f cl = .ok (.data 152 24 [.data 151 65 [], w])) :
    ∃ ty c x y, cl = .select ty c x y ∧ eTy ty = true ∧ w = .values [c, x, y] := by
  obtain ⟨hf, ho⟩ := instData_inv_names h
  rw [variantNames_Ternary] at hf
  rw [variantNames_Select] at ho
  cases cl <;> simp [instNames] at hf ho
  all_goals first
    | (rename_i op _ _; cases op <;> simp [unaryOpcode, binaryOpcode] at ho)
    | (rename_i op _ _ _; cases op <;> simp [unaryOpcode, binaryOpcode] at ho)
    | skip
  rename_i ty c x y
  refine ⟨ty, c, x, y, rfl, ?_⟩
  simp only [instData] at h
  split at h
  · rename_i he
    simp only [pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨-, -, h3⟩ := mkVariant_eq_data h
    simp only [List.cons.injEq] at h3
    exact ⟨he, h3.2.1⟩
  · cases h

theorem evalInst_select_ok {fr : Clif.Frame} {cm cm' : Clif.Mem} {ty : Clif.Ty} {c x y : Nat}
    {vals : List Clif.Val} (h : Clif.evalInst fr cm (.select ty c x y) = .ok (vals, cm')) :
    ∃ cv a b, fr.regs c = some cv ∧ fr.getAs x ty = .ok a ∧ fr.getAs y ty = .ok b ∧
      vals = [⟨ty, Clif.Sem.select cv.bits a b⟩] ∧ cm' = cm := by
  simp only [Clif.evalInst] at h
  cases hc : fr.get c with
  | ok cv =>
    cases hx : fr.getAs x ty with
    | ok a =>
      cases hy : fr.getAs y ty with
      | ok b =>
        rw [hc, hx, hy] at h
        simp only [bind, Clif.Res.bind, pure] at h
        cases h
        refine ⟨cv, a, b, ?_, rfl, rfl, rfl, rfl⟩
        unfold Clif.Frame.get at hc
        cases hr : fr.regs c <;> simp [hr, Clif.Res.ofOption] at hc
        rw [hc]
      | trap _ => rw [hc, hx, hy] at h; cases h
      | stuck _ => rw [hc, hx, hy] at h; cases h
    | trap _ => rw [hc, hx] at h; cases h
    | stuck _ => rw [hc, hx] at h; cases h
  | trap _ => rw [hc] at h; cases h
  | stuck _ => rw [hc] at h; cases h

theorem ext_value_array_3 (ctx : Ctx) (st : LState) (a b c : Nat) :
    externExtract ctx T.value_array_3 (.values [a, b, c]) st = .ok [.value a, .value b, .value c] := rfl

theorem eTy_widths {ty : Clif.Ty} (h : eTy ty = true) :
    ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64 := by
  cases ty <;> simp [eTy, Clif.Ty.width] at h ⊢

theorem vholds_select {ty : Clif.Ty} (hety : eTy ty = true) (t : Bool) {a b : BitVec ty.width}
    {zx zy : CV} (hx : VHolds ⟨ty, a⟩ zx) (hy : VHolds ⟨ty, b⟩ zy) :
    VHolds ⟨ty, if t then a else b⟩ (ofX (if t then lo64 zx else lo64 zy)) := by
  have hw := eTy_width hety
  cases t
  · simp only [VHolds, Bool.false_eq_true, ↓reduceIte] at hx hy ⊢
    rw [setWidth_ofX_lo64 hw, hy]
  · simp only [VHolds, ↓reduceIte] at hx hy ⊢
    rw [setWidth_ofX_lo64 hw, hx]

section Root
variable {p : Program} (hp : Data p)

set_option maxHeartbeats 8000000 in
include hp in
theorem select_ruleOk (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOk isem MR env cp p rule_lower_2267 := by
  intro f ctx hctx ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _ hmatch heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 400 := ⟨n - 400, by omega⟩
  isel_inv' hp [] at hmatch heval
  rename_i hins hdd h650 h659
  obtain ⟨hout⟩ : Nonempty (externCtor ctx T.output _ _ = _) := ⟨‹_›⟩
  obtain ⟨hva⟩ : Nonempty (externExtract ctx T.value_array_3 _ st = _) := ⟨‹_›⟩
  rw [hi, Option.some.injEq] at hins
  subst hins
  have hdat := hctx.data ii _ inst hi hic
  rw [← hdd] at hdat
  obtain ⟨ty, c, x, y, rfl, hety, rfl⟩ := instData_select_inv hdat
  rw [ext_value_array_3] at hva
  cases hva
  obtain ⟨tys, htys, hres, -⟩ := hctx.resTys ii _ _ hi hic
  simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
  subst htys
  rw [hres] at h659
  simp only [List.map_cons, List.map_nil, List.head?_cons, Option.getD_some, ofClif_int_width] at h659
  have hC := is_nonzero_cmp_ok hp hco hR hctx (hn := by omega) hvb h650
  obtain ⟨mf, cond, rx, ry, hflag, hrx, hry, rfl, hs⟩ :=
    lower_select_ok hp hco (hn := by omega) (eTy_widths hety) hC.shape h659
  rw [ctor_output'] at hout
  obtain ⟨rfl, rfl⟩ := hout
  have hx := hvb x rx hrx
  have hy := hvb y ry hry
  rw [hctx.valueReg x rx hrx] at hs
  rw [hctx.valueReg y ry hry] at hs
  obtain ⟨hmono, ms, hf, hsem⟩ := condCode_csel hR hC hflag hx hy
  rw [hs]
  refine ⟨ms, hf.emitted, _, rfl, lowerInstOk_runs hMR hf.mono hf.defs rfl ?_⟩
  intro fr cm ρ w vals cm' _ hh hdf ho
  obtain ⟨cv, a, b, hcv, hxa, hyb, rfl, rfl⟩ := evalInst_select_ok ho
  have hxv := getAs_ok hxa
  have hyv := getAs_ok hyb
  obtain ⟨hu, hr⟩ := hsem fr ρ _ hh hdf ⟨cv, hcv, rfl⟩ (by simp [hxv]) (by simp [hyv])
  exact ⟨rfl, hu, .inl hmono, _, rfl, (hr w).imp fun ρ' _ _ h => by
    rw [h]; exact vholds_select hety _ (hh _ _ hxv) (hh _ _ hyv)⟩

end Root

end Backend.Proof
