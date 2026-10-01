import FV.Backend.Proof.IselMemRoots
import FV.Backend.Proof.IselCtlCall

/-!
# Memory family: `func_addr` (rule id 1026) and `MemRulesCorrect`

`rule_lower_2486` lowers `func_addr.i64 fnN` to `load_ext_name` of the declaration's name at
offset 0 (the GOT load under `is_pic`), as `symbol_value` (`symbol_value_ok`) does for a data
symbol: the result is the declaration's link-time address (`MemRefines`: a GOT load of a linked
symbol; `MemRelOk.symbols`: CLIF's `func_addr` reads the same `symbols`).
`memRulesCorrect_program` collects the memory root rules (`memRootRule`).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

@[isel_data] theorem term_2296_kind : T.«Opcode.FuncAddr».kind = (.enumVariant 12) := rfl
@[isel_data] theorem term_2296_name : T.«Opcode.FuncAddr».name = "Opcode.FuncAddr" := rfl
@[isel_data] theorem term_2459_kind : T.«InstructionData.FuncAddr».kind = (.enumVariant 12) := rfl
@[isel_data] theorem term_2459_name :
    T.«InstructionData.FuncAddr».name = "InstructionData.FuncAddr" := rfl

/-- The term facts of the `func_addr` rule beyond `Data`. -/
structure FAData (p : Program) : Prop where
  t2296 : Interp.termOf p 2296 = pure T.«Opcode.FuncAddr»
  t2459 : Interp.termOf p 2459 = pure T.«InstructionData.FuncAddr»

theorem faData_program : FAData program := ⟨rfl, rfl⟩

theorem mem_variantNames_FuncAddr : (variantNames 152)[12]? = some "FuncAddr" := rfl
theorem mem_variantNames_FuncAddrOp : (variantNames 151)[12]? = some "FuncAddr" := rfl

theorem inv_funcAddr_root {f : Clif.Function} {cl : Clif.Inst} {w : V}
    (h : instData f cl = .ok (.data 152 12 [.data 151 12 [], w])) :
    ∃ fn, cl = .funcAddr .i64 fn ∧ w = .op (.funcRef fn) := by
  have hn := instData_names_eq h mem_variantNames_FuncAddr mem_variantNames_FuncAddrOp
  cases cl <;> simp only [instNames, Prod.mk.injEq] at hn
  all_goals try (simp at hn; done)
  rename_i ty fn
  simp only [instData] at h
  split at h
  · cases h
  · rename_i hty
    simp only [pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨-, -, h3⟩ := mkVariant_eq_data h
    simp only [List.cons.injEq, and_true] at h3
    refine ⟨fn, ?_, h3.2⟩
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hty
    rw [hty]

section Builders
variable {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat} {isem : Sem}
  {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} {f : Clif.Function} {ctx : Ctx}

theorem instOutcome_funcAddr (fr : Clif.Frame) (cm : Clif.Mem) (ty : Clif.Ty) (fn : Nat) :
    instOutcome env cp fr cm (.funcAddr ty fn) = Clif.evalInst fr cm (.funcAddr ty fn) := rfl

theorem evalInst_funcAddr_inv {fr : Clif.Frame} {cm cm' : Clif.Mem} {ty : Clif.Ty} {fn : Nat}
    {vals : List Clif.Val} (h : Clif.evalInst fr cm (.funcAddr ty fn) = .ok (vals, cm')) :
    ∃ ext base, fr.func.extern? fn = some ext ∧ cm.symbols ext.name = some base ∧
      vals = [Clif.Val.ofInt ty base] ∧ cm' = cm := by
  simp only [Clif.evalInst] at h
  obtain ⟨ext, he, h⟩ := res_bind_eq_ok h
  obtain ⟨base, hb, h⟩ := res_bind_eq_ok h
  simp only [Clif.Res.pure_eq, Clif.Res.ok.injEq, Prod.mk.injEq] at h
  exact ⟨ext, base, res_ofOption_ok he, res_ofOption_ok hb, h.1.symm, h.2.symm⟩

/-- **`func_addr`** through `load_ext_name` at offset 0 (`SymOk`). -/
theorem funcAddr_lower_ok (hMR : MRStable F MR) (hMRo : MemRelOk F sb syms f MR)
    {st st' : LState} {ms : List MInst} {d fn : Nat} {ext : Clif.ExtFunc} {results : List Nat}
    (hsym : SymOk F isem syms st st' ms d ext.name 0) (hext : ctx.func.extern? fn = some ext) :
    LowerInstOk isem MR env cp ctx (.funcAddr .i64 fn) results st [[.vreg d .int]] st' ms := by
  refine ⟨hsym.frag.mono, hsym.frag.defs, ?_⟩
  intro fr cm ρ w hf hv hdfg hmr
  rw [instOutcome_funcAddr]
  cases he : Clif.evalInst fr cm (.funcAddr .i64 fn) with
  | trap c => intro h; simp [explicitTrapInst] at h
  | stuck _ => trivial
  | ok r =>
  obtain ⟨vals, cm'⟩ := r
  obtain ⟨ext', base, hx, hb, rfl, rfl⟩ := evalInst_funcAddr_inv he
  dsimp only
  rw [hf, hext] at hx
  cases hx
  rw [hMRo.symbols _ _ _ hmr] at hb
  obtain ⟨ρ', w', hr, hw', hd⟩ := hsym.run base ρ w hb
  refine ⟨fun m hm u hu => .inl (hsym.uses m hm u hu), ρ', w', hr, .inr ⟨rfl, ?_⟩,
    hMR _ _ _ _ hw' hmr⟩
  intro j rs v hrs hv'
  cases j with
  | succ j => simp at hrs
  | zero =>
  simp only [List.getElem?_cons_zero, Option.some.injEq] at hrs hv'
  subst hrs hv'
  refine ⟨d, .int, rfl, .inl hsym.res, ?_⟩
  show lo64 (ρ' d) = _
  rw [hd, ← addr_nat_off base 0, Int.add_zero]
  rfl

end Builders

variable {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat} {isem : Sem}
  {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}

set_option maxHeartbeats 2000000 in
/-- **`func_addr`** (`lower.isle:2486`, rule id 1026). -/
theorem func_addr_ok {p : Program} (hp : Data p) (hpF : FAData p) (hR : Refines F isem) (hMR : MRStable F MR)
    (hM : MemRefines F sb syms isem) : MemRuleOk F sb syms isem MR env cp p rule_lower_2486 := by
  intro f ctx hctx hMRo ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
    hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  mem_inv hp [ext_func_ref_data_iff, hpF.t2296, hpF.t2459] at hmatch heval
  have hdat0 := CtxInv.data hctx _ _ _ hi hic
  simp only [hi, Option.some.injEq] at *
  isel_destruct; subst_vars
  have hdat := data_trans hdat0 ‹_›
  obtain ⟨fn, rfl, rfl⟩ := inv_funcAddr_root hdat
  simp only [ext_func_ref_data_iff] at *
  isel_destruct; subst_vars
  simp only [List.cons.injEq, and_true] at *
  isel_destruct; subst_vars
  have hL := ‹ApplyInternal _ _ _ _ 27 570 _ _ _ _›
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  obtain ⟨ms, d, rfl, hsym⟩ := load_ext_name_ok hp ctx hco hR hM (by omega) hL
  obtain ⟨rfl, hs'⟩ := output_reg_inv hp ctx hco (by omega) hO
  simp only at hs'
  subst hs'
  exact ⟨ms, hsym.frag.emitted, _, rfl, funcAddr_lower_ok hMR hMRo hsym ‹_›⟩

/-! ## `MemRulesCorrect` -/

/-- The memory root rules of `lower`, in order. -/
theorem lower_memRoot_filter : (program.rulesOf TId.lower).filter memRootRule =
    [rule_lower_1300, rule_lower_1359, rule_lower_2486, rule_lower_2491, rule_lower_2604, rule_lower_2607, rule_lower_2610, rule_lower_2613, rule_lower_2647, rule_lower_2650, rule_lower_2653, rule_lower_2656, rule_lower_2659, rule_lower_2662, rule_lower_2705, rule_lower_2709, rule_lower_2713, rule_lower_2717, rule_lower_2722, rule_lower_2726, rule_lower_2730, rule_lower_2849] := by
  rw [program_rulesOf_686]
  rfl

/-- **The memory family (M4)**: every memory root rule of `lower` is correct under
`MemRefines`, for every function whose memory relation is `MemRelOk`. -/
theorem memRulesCorrect_program : MemRulesCorrect program := by
  intro F sb syms isem MR env cp hR hMR hM r hr hmem
  have hsub : r ∈ (program.rulesOf TId.lower).filter memRootRule := List.mem_filter.2 ⟨hr, hmem⟩
  rw [lower_memRoot_filter] at hsub
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hsub
  rcases hsub with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact uextend_load_ok data_program
  · exact sextend_load_ok data_program
  · exact func_addr_ok data_program faData_program hR hMR hM
  · exact symbol_value_ok data_program hR hMR hM
  · exact load_i8_ok data_program hR hMR hM
  · exact load_i16_ok data_program hR hMR hM
  · exact load_i32_ok data_program hR hMR hM
  · exact load_i64_ok data_program hR hMR hM
  · exact uload8_ok data_program hR hMR hM
  · exact sload8_ok data_program hR hMR hM
  · exact uload16_ok data_program hR hMR hM
  · exact sload16_ok data_program hR hMR hM
  · exact uload32_ok data_program hR hMR hM
  · exact sload32_ok data_program hR hMR hM
  · exact store_i8_ok data_program hR hMR hM
  · exact store_i16_ok data_program hR hMR hM
  · exact store_i32_ok data_program hR hMR hM
  · exact store_i64_ok data_program hR hMR hM
  · exact istore8_ok data_program hR hMR hM
  · exact istore16_ok data_program hR hMR hM
  · exact istore32_ok data_program hR hMR hM
  · exact stack_addr_ok data_program hMR hM

end Backend.Proof
