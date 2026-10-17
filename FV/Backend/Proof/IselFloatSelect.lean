import FV.Backend.Proof.IselCmpSelect
import FV.Backend.Proof.IselFloatBitcast

/-!
# S11e4: the float arm of `select` (`rule_lower_2267`, id 971) over float-capable contexts

`lower_select ty c x y` at `f32`/`f64`: the condition (`is_nonzero_cmp`, on an integer
operand, `is_nonzero_cmp_okT`), its flag instruction, then `fcsel` (`fpu_csel`, rule 5341 of
`lower_select_cond`) of the operands' registers into a fresh float vreg.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-- The `fcsel` size of `f32`/`f64`. -/
def fselSz (w : Nat) : ScalarSize := if w = 32 then .size32 else .size64

theorem ofV_fpuCSel32' (rd rn rm : Reg) (c : V) :
    MInst.ofV (.data 58 72 [.reg rd, .reg rn, .reg rm, c]) = c.cond?.map (.fpuCSel .size32 rd rn rm) := by
  have e1 : MInst.ofV (.data 58 72 [.reg rd, .reg rn, .reg rm, c]) =
      (do return .fpuCSel .size32 rd rn rm (← c.cond?)) := rfl
  rw [e1]; cases c.cond? <;> rfl

theorem ofV_fpuCSel64' (rd rn rm : Reg) (c : V) :
    MInst.ofV (.data 58 73 [.reg rd, .reg rn, .reg rm, c]) = c.cond?.map (.fpuCSel .size64 rd rn rm) := by
  have e1 : MInst.ofV (.data 58 73 [.reg rd, .reg rn, .reg rm, c]) =
      (do return .fpuCSel .size64 rd rn rm (← c.cond?)) := rfl
  rw [e1]; cases c.cond? <;> rfl

section Terms
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)

set_option maxHeartbeats 2000000 in
include hp hc in
/-- **`fpu_csel`** at `f32`/`f64`: a fresh float destination and `fcsel s/d`. -/
theorem fpu_csel_ok {n : Nat} (hn : 30 ≤ n) {w : Nat} (hw : w = 32 ∨ w = 64) {c a b : V}
    {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 49 406 [.ty (.float w), c, a, b] s v s') :
    s'.1 = (s.1.fresh .float).2 ∧
      v = .data 49 3 [.data 58 (if w = 32 then 72 else 73) [.reg (s.1.fresh .float).1, a, b, c],
        .reg (s.1.fresh .float).1] := by
  rcases hw with rfl | rfl <;>
  isel_split' hp hc h 406 <;>
  (try (isel_refute hp at hm; done))
  all_goals isel_inv' hp [ctor_temp_writable_reg_f32_iff, ctor_temp_writable_reg_f64_iff] at hm he
  all_goals first
    | done
    | exact absurd ‹CTy.float _ = CTy.float _› (by simp)

set_option maxHeartbeats 4000000 in
include hp hc in
/-- **`lower_select_cond`** at `f32`/`f64` (rule 5341): the flag instruction, then `fcsel` into a
fresh float vreg. -/
theorem lower_select_cond_okF {n : Nat} (hn : 60 ≤ n) {w : Nat} (hw : w = 32 ∨ w = 64)
    {mi cd : V} {x y : Nat} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 22 660 [.ty (.float w), .data 47 1 [mi], cd, .value x, .value y]
      s v s') :
    ∃ m1 rx ry c, MInst.ofV mi = some m1 ∧ ctx.valueReg? x = some rx ∧ ctx.valueReg? y = some ry ∧
      cd.cond? = some c ∧ v = .regs [(s.1.fresh .float).1] ∧
      s'.1 = (((s.1.fresh .float).2.emit m1).emit (.fpuCSel (fselSz w) (s.1.fresh .float).1 rx ry c)) := by
  rcases hw with rfl | rfl <;>
  isel_split' hp hc h 660 <;>
  (try (isel_refute hp at hm; done))
  all_goals (try isel_refute hp at hm)
  all_goals try (exact absurd hm.1 (by decide))
  all_goals try (obtain ⟨_, _, ⟨_, h1, _⟩, _⟩ := hm; cases h1; done)
  all_goals isel_inv' hp [] at hm he
  all_goals
    obtain ⟨h406⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 49 406 _ _ _ _) := ⟨‹_›⟩
    obtain ⟨hs1, rfl⟩ := fpu_csel_ok hp hc (by omega) (by decide) h406
    obtain ⟨h254⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 22 254 _ _ _ _) := ⟨‹_›⟩
    obtain ⟨m1, m2, hm1, hm2, rfl, hs2⟩ := with_flags_ok hp hc (by omega) h254
    simp only [↓reduceIte, Nat.reduceEqDiff] at hm2
    first
      | rw [ofV_fpuCSel32', Option.map_eq_some_iff] at hm2
      | rw [ofV_fpuCSel64', Option.map_eq_some_iff] at hm2
    obtain ⟨c, hcd, rfl⟩ := hm2
    refine ⟨_, hm1, _, ‹_›, _, ‹_›, c, hcd, rfl, ?_⟩
    simp only at hs1 hs2
    rw [hs2, hs1]; rfl

set_option maxHeartbeats 8000000 in
include hp hc in
/-- **`lower_select`** at `f32`/`f64` on a condition of E: the condition's flag instruction, then
`fcsel` into a fresh float vreg. -/
theorem lower_select_okF {n : Nat} (hn : 100 ≤ n) {w : Nat} (hw : w = 32 ∨ w = 64)
    {c : V} {P : Nat → Prop} (hsh : CondShape c P) {x y : Nat} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 22 659 [.ty (.float w), c, .value x, .value y] s v s') :
    ∃ m cond rx ry, CondFlag cmpXzr c m cond ∧ ctx.valueReg? x = some rx ∧ ctx.valueReg? y = some ry ∧
      v = .regs [(s.1.fresh .float).1] ∧
      s'.1 = (((s.1.fresh .float).2.emit m).emit (.fpuCSel (fselSz w) (s.1.fresh .float).1 rx ry cond)) := by
  rcases hw with rfl | rfl <;>
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
      lower_select_cond_okF hp hc (hn := by omega) (by decide) h660
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

end Terms

/-! ## The code of `lower_select` at `f32`/`f64`: condition, flag instruction, `fcsel` -/

theorem vdefs_fcsel (sz : ScalarSize) (d a b : Nat) (ca cb : RegClass) (c : Cond) :
    vdefs (.fpuCSel sz (.vreg d .float) (.vreg a ca) (.vreg b cb) c) = [d] := rfl
theorem vuseNums_fcsel (sz : ScalarSize) (d a b : Nat) (ca cb : RegClass) (c : Cond) :
    vuseNums (.fpuCSel sz (.vreg d .float) (.vreg a ca) (.vreg b cb) c) = [a, b] := rfl

section Sem
variable {F : BitVec 64 → Prop} {isem : Sem}

/-- `fcsel s/d`: the low `w` bits of the first or second operand, zero-extended (`write_sfp`). -/
theorem Runs.fcsel (hR : Refines F isem) {w : Nat} (hw : w = 32 ∨ w = 64) (d a b : Nat)
    (ca cb : RegClass) (c : Cond) (ρ : Nat → CV) (s : Arm.ArmState) :
    Runs F isem [.fpuCSel (fselSz w) (.vreg d .float) (.vreg a ca) (.vreg b cb) c] ρ s (fun ρ' _ =>
      ρ' = upd ρ d ((if Arm.ConditionHolds c.bits s then (ρ a).setWidth w else (ρ b).setWidth w).setWidth 128)) := by
  rcases hw with rfl | rfl
  · exact Runs.one hR rfl rfl rfl (SameWorldNF.refl F s) fun _ _ => rfl
  · exact Runs.one hR rfl rfl rfl (SameWorldNF.refl F s) fun _ _ => rfl

/-- A flag producer then `fcsel`. -/
theorem runs_flags_fcsel (hR : Refines F isem) {m : MInst} {ρ : Nat → CV} {ps : Arm.PState}
    {cond : Cond} {b : Bool} (hm : SetsFlags m ρ ps) (hb : condOn cond.bits ps = b) {w : Nat}
    (hw : w = 32 ∨ w = 64) (d x y : Nat) (ca cb : RegClass) (s : Arm.ArmState) :
    Runs F isem [m, .fpuCSel (fselSz w) (.vreg d .float) (.vreg x ca) (.vreg y cb) cond] ρ s (fun ρ' _ =>
      ρ' = upd ρ d ((if b then (ρ x).setWidth w else (ρ y).setWidth w).setWidth 128)) := by
  refine Runs.append (ms1 := [m]) (Runs.flags hR hm s) fun ρ1 w1 ⟨h1, h2⟩ => ?_
  subst h1
  refine (Runs.fcsel hR hw d x y ca cb cond ρ1 w1).imp fun ρ' _ _ h => ?_
  rw [h, h2, hb]

/-- **Condition code, then `lower_select`'s flag instruction and `fcsel`**: the fresh float vreg
`st1.nextVreg` holds the low `w` bits of `x` if the condition holds, else of `y`. -/
theorem condCode_fcsel (hR : Refines F isem) {ctx : Ctx} {st st1 : LState} {c : V}
    {T : Clif.Frame → Bool → Prop} (hcc : CondCode F isem ctx st st1 c T) {m : MInst} {cond : Cond}
    (hflag : CondFlag cmpXzr c m cond) {w : Nat} (hw : w = 32 ∨ w = 64) {x y : Nat}
    {ca cb : RegClass} (hx : x < st.nextVreg) (hy : y < st.nextVreg) :
    st.nextVreg ≤ st1.nextVreg ∧
    ∃ ms, Frag st (((st1.fresh .float).2.emit m).emit
        (.fpuCSel (fselSz w) (.vreg st1.nextVreg .float) (.vreg x ca) (.vreg y cb) cond)) ms ∧
      ∀ (fr : Clif.Frame) (ρ : Nat → CV) (b : Bool), ValsHeld fr ρ → DFGCons ctx fr → T fr b →
        (fr.regs x).isSome → (fr.regs y).isSome →
        UsesOk st fr ms ∧ ∀ s, Runs F isem ms ρ s
          (fun ρ' _ => ρ' st1.nextVreg = (if b then (ρ x).setWidth w else (ρ y).setWidth w).setWidth 128) := by
  obtain ⟨ms, hf, hsh, hr⟩ := hcc
  obtain ⟨-, -, hd, -⟩ := hflag.shape cmpXzr_regs hsh
  refine ⟨hf.mono, ms ++ [m, .fpuCSel (fselSz w) (.vreg st1.nextVreg .float) (.vreg x ca) (.vreg y cb) cond],
    hf.append (Frag.fresh_emit2_c st1 .float hd (by rw [vdefs_fcsel]; exact List.Subset.refl _)),
    fun fr ρ b hh hdf hT hxs hys => ?_⟩
  obtain ⟨hu, hsh', hrun⟩ := hr fr ρ b hh hdf hT
  obtain ⟨-, -, -, hum⟩ := hflag.shape cmpXzr_regs hsh'
  refine ⟨UsesLo.append hu ?_, fun s => ?_⟩
  · intro i hi u hu'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact hum u hu'
    · rw [vuseNums_fcsel] at hu'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu'
      rcases hu' with rfl | rfl
      · exact .inr hxs
      · exact .inr hys
  refine Runs.append ((hrun s).imp fun ρ1 w1 hs1 hc1 => And.intro hs1 hc1) fun ρ1 w1 ⟨hs1, hc1⟩ => ?_
  obtain ⟨ps, hps, hb⟩ := hflag.sem setsFlags_cmpXzr hc1
  refine (runs_flags_fcsel hR hps hb hw st1.nextVreg x y ca cb w1).imp fun ρ' _ _ h => ?_
  rw [h, hf.frame hs1 hx, hf.frame hs1 hy]
  simp [upd]

end Sem

/-! ## The `select` of floats -/

theorem float_ty_cases {ty : Clif.Ty} (h : ty.isFloat = true) :
    ∃ w, (w = 32 ∨ w = 64) ∧ CTy.ofClif ty = .float w ∧ ty.width = w := by
  cases ty <;> simp_all [Clif.Ty.isFloat, CTy.ofClif, Clif.Ty.width]

theorem vholds_fselect {ty : Clif.Ty} {w : Nat} (hwid : ty.width = w) (hw : w = 32 ∨ w = 64)
    (t : Bool) {a b : BitVec ty.width} {zx zy : CV} (hx : VHolds ⟨ty, a⟩ zx) (hy : VHolds ⟨ty, b⟩ zy) :
    VHolds ⟨ty, if t then a else b⟩ ((if t then zx.setWidth w else zy.setWidth w).setWidth 128) := by
  subst hwid
  have hle : ty.width ≤ 128 := by omega
  cases t
  · simp only [VHolds, Bool.false_eq_true, ↓reduceIte] at hx hy ⊢
    rw [BitVec.setWidth_setWidth_of_le _ hle, hy, BitVec.setWidth_eq]
  · simp only [VHolds, ↓reduceIte] at hx hy ⊢
    rw [BitVec.setWidth_setWidth_of_le _ hle, hx, BitVec.setWidth_eq]

section Root
variable {p : Program} (hp : Data p)

set_option maxHeartbeats 8000000 in
include hp in
/-- **The float arm of `select`** (`rule_lower_2267`, `lower.isle:2267`) over float-capable
contexts: on a `select` of `f32`/`f64` values, the condition (an integer, `intArgs`), its flag
instruction, then `fcsel` into a fresh float vreg. -/
theorem select_float_okT (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTP (fun i => ∃ ty c x y, i = .select ty c x y ∧ ty.isFloat = true) isem MR env cp p
      rule_lower_2267 := by
  intro f ctx hctx ii info inst hi hic hP cfg hco m n st tr env' s1 out st' tr' hm hn hvb _ hmatch heval
  obtain ⟨ty, c, x, y, rfl, hfl⟩ := hP
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 400 := ⟨n - 400, by omega⟩
  isel_inv' hp [] at hmatch heval
  rename_i hins hdd h650 h659
  obtain ⟨hout⟩ : Nonempty (externCtor ctx T.output _ _ = _) := ⟨‹_›⟩
  obtain ⟨hva⟩ : Nonempty (externExtract ctx T.value_array_3 _ st = _) := ⟨‹_›⟩
  rw [hi, Option.some.injEq] at hins
  subst hins
  have hdat := hctx.data ii _ _ hi hic
  rw [← hdd] at hdat
  obtain ⟨ty', c', x', y', he, -, rfl⟩ := instData_select_inv hdat
  simp only [Clif.Inst.select.injEq] at he
  obtain ⟨rfl, rfl, rfl, rfl⟩ := he
  obtain ⟨w, hw, hof, hwid⟩ := float_ty_cases hfl
  rw [ext_value_array_3] at hva
  cases hva
  obtain ⟨tys, htys, hres, -⟩ := hctx.resTys ii _ _ hi hic
  simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
  subst htys
  rw [hres] at h659
  simp only [List.map_cons, List.map_nil, List.head?_cons, Option.getD_some, hof] at h659
  have hci : IntPos ctx c := hctx.intOps ii _ _ hi hic c
    (show c ∈ intArgs (.select ty c x y) by simp only [intArgs, hfl, ite_true, List.mem_singleton])
  have hC := is_nonzero_cmp_okT hp hco hR hctx (hn := by omega) hci hvb h650
  obtain ⟨mf, cond, rx, ry, hflag, hrx, hry, rfl, hs⟩ :=
    lower_select_okF hp hco (hn := by omega) hw hC.shape h659
  rw [ctor_output'] at hout
  obtain ⟨rfl, rfl⟩ := hout
  have hx := hvb x rx hrx
  have hy := hvb y ry hry
  rw [hctx.valueReg x rx hrx] at hs
  rw [hctx.valueReg y ry hry] at hs
  obtain ⟨hmono, ms, hf, hsem⟩ := condCode_fcsel hR hC hflag hw hx hy
  rw [hs]
  refine ⟨ms, hf.emitted, _, rfl, lowerInstOk_runs_c hMR hf.mono hf.defs rfl ?_⟩
  intro fr cm ρ s vals cm' _ hh hdf ho
  obtain ⟨cv, a, b, hcv, hxa, hyb, rfl, rfl⟩ := evalInst_select_ok ho
  have hxv := getAs_ok hxa
  have hyv := getAs_ok hyb
  obtain ⟨hu, hr⟩ := hsem fr ρ _ hh hdf ⟨cv, hcv, rfl⟩ (by simp [hxv]) (by simp [hyv])
  exact ⟨rfl, hu, .inl hmono, _, rfl, (hr s).imp fun ρ' _ _ h => by
    rw [h]; exact vholds_fselect hwid hw _ (hh _ _ hxv) (hh _ _ hyv)⟩

end Root

end Backend.Proof
