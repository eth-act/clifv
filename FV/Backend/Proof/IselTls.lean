import FV.Backend.Proof.IselMemRoots

/-!
# `tls_value` (agent/stack-tls-proof): the root rules of `lower`

`MemRuleOk` for the two `tls_value` root rules (`memRootRule`):

* `rule_lower_3217` (rule id 1129, `tls_model` `elf_gd`): `elf_tls_get_addr name` defines two
  fresh vregs and emits `ElfTlsGetAddr name dst tmp` (the TLSDESC sequence), whose first def is
  the variable's address. With `MemRefines` (the TLSDESC clause: the address of a linked
  symbol, a world agreeing up to the flags) this is `tls_value`'s result in `Clif.run`, whose one
  thread's instance of the variable is its link-time symbol (`Clif.Mem.symbols`).
* `rule_lower_3220` (rule id 1130, `tls_model` `macho`): never matches, since the backend's
  `tls_model` is `elf_gd` (cg_clif's ELF setting).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-! ## Extractors -/

section Extern
variable (ctx : Ctx) (st : LState)

theorem ext_tls_model_iff (t : CTy) (fs : List V) :
    externExtract ctx T.tls_model (.ty t) st = .ok fs ↔
      fs = [.data tyTlsModel VIdx.TlsModel.ElfGd []] := by
  have : externExtract ctx T.tls_model (.ty t) st = .ok [.data tyTlsModel VIdx.TlsModel.ElfGd []] :=
    rfl
  rw [this]; simp [eq_comm]

theorem ext_symbol_value_data_tls_iff (gv : Nat) (fs : List V) :
    externExtract ctx T.symbol_value_data (.op (.tlsGlobalValue gv)) st = .ok fs ↔
      ∃ name off colocated, ctx.func.globals.lookup gv = some (.tlsSymbol name off colocated) ∧
        fs = [.op (.extName name),
          .data tyRelocDistance (if colocated then VIdx.RelocDistance.Near else VIdx.RelocDistance.Far) [],
          .int off] := by
  have : externExtract ctx T.symbol_value_data (.op (.tlsGlobalValue gv)) st =
    match ctx.func.globals.lookup gv with
    | some (.tlsSymbol name off colocated) =>
      .ok [.op (.extName name),
           .data tyRelocDistance (if colocated then VIdx.RelocDistance.Near else VIdx.RelocDistance.Far) [],
           .int off]
    | _ => .fail := rfl
  rw [this]
  split
  · rename_i name off col h
    simp only [ExtResult.ok.injEq, h, Option.some.injEq]
    constructor
    · intro e; exact ⟨name, off, col, rfl, e.symm⟩
    · rintro ⟨n', o', c', he, rfl⟩
      cases he; rfl
  · rename_i hne
    simp only [reduceCtorEq, false_iff, not_exists, not_and]
    intro n o c h; exact absurd h (hne n o c)

end Extern

/-! ## The instruction data and the emitted instruction -/

theorem mem_variantNames_TlsValue : (variantNames 151)[50]? = some "TlsValue" := rfl

theorem inv_tlsValue_root {f : Clif.Function} {cl : Clif.Inst} {w : V}
    (h : instData f cl = .ok (.data 152 31 [.data 151 50 [], w])) :
    ∃ ty gv name col, cl = .tlsValue ty gv ∧ ty = .i64 ∧ w = .op (.tlsGlobalValue gv) ∧
      f.globals.lookup gv = some (.tlsSymbol name 0 col) := by
  have hn := instData_names_eq h mem_variantNames_UGV mem_variantNames_TlsValue
  cases cl <;> simp only [instNames, Prod.mk.injEq] at hn
  all_goals try (simp at hn; done)
  rename_i ty gv
  simp only [instData] at h
  split at h
  · cases h
  · rename_i hty
    split at h
    · rename_i name col hg
      simp only [pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨-, -, h3⟩ := mkVariant_eq_data h
      simp only [List.cons.injEq, and_true] at h3
      exact ⟨ty, gv, name, col, rfl, by simpa using hty, h3.2, hg⟩
    all_goals cases h

theorem ofV_elfTlsGetAddr (nm : String) (rd t : Reg) :
    MInst.ofV (.data 58 137 [.op (.extName nm), .reg rd, .reg t]) =
      some (.elfTlsGetAddr nm rd t) := rfl

section
variable {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config} (hc : cfg.checkOverlap = false)

include hp hc in
/-- **`elf_tls_get_addr name`**: two fresh destinations and the TLSDESC sequence. -/
theorem elf_tls_get_addr_ok {n : Nat} (hn : 40 ≤ n) {nm : String}
    {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 647 [.op (.extName nm)] s v s') :
    v = .reg (s.1.fresh .int).1 ∧
      s'.1 = ((s.1.fresh .int).2.fresh .int).2.emit
        (.elfTlsGetAddr nm (s.1.fresh .int).1 ((s.1.fresh .int).2.fresh .int).1) := by
  obtain ⟨st, tr⟩ := s
  mem_split hp hc h 647
  mem_inv hp [] at hm he
  rw [ofV_elfTlsGetAddr] at *
  simp only [Option.some.injEq] at *
  subst_vars
  first | exact ⟨rfl, rfl⟩ | rfl | trivial

end

/-! ## The lowering -/

theorem operands_elfTlsGetAddr (nm : String) (d t : Nat) :
    (MInst.elfTlsGetAddr nm (.vreg d .int) (.vreg t .int)).operands =
      .ok #[⟨d, .int, .def, .late, .fixed (.x 0)⟩, ⟨t, .int, .def, .early, .reg⟩] := rfl

theorem vdefs_elfTlsGetAddr (nm : String) (d t : Nat) :
    vdefs (.elfTlsGetAddr nm (.vreg d .int) (.vreg t .int)) = [d, t] := rfl

theorem vuseNums_elfTlsGetAddr (nm : String) (d t : Nat) :
    vuseNums (.elfTlsGetAddr nm (.vreg d .int) (.vreg t .int)) = [] := rfl

theorem evalInst_tlsValue_inv {fr : Clif.Frame} {cm cm' : Clif.Mem} {ty : Clif.Ty} {gv : Nat}
    {vals : List Clif.Val} (h : Clif.evalInst fr cm (.tlsValue ty gv) = .ok (vals, cm')) :
    ∃ name o col base, fr.func.globals.lookup gv = some (.tlsSymbol name o col) ∧
      cm.symbols name = some base ∧ vals = [Clif.Val.ofInt ty (base + o)] ∧ cm' = cm := by
  simp only [Clif.evalInst] at h
  obtain ⟨g, hg, h⟩ := res_bind_eq_ok h
  cases g with
  | tlsSymbol name o col =>
    obtain ⟨base, hb, h⟩ := res_bind_eq_ok h
    simp only [Clif.Res.pure_eq, Clif.Res.ok.injEq, Prod.mk.injEq] at h
    exact ⟨name, o, col, base, res_ofOption_ok hg, res_ofOption_ok hb, h.1.symm, h.2.symm⟩
  | _ => cases h

section Builders
variable {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat} {isem : Sem}
  {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} {ctx : Ctx}

theorem instOutcome_tlsValue (fr : Clif.Frame) (cm : Clif.Mem) (ty : Clif.Ty) (gv : Nat) :
    instOutcome env cp fr cm (.tlsValue ty gv) = Clif.evalInst fr cm (.tlsValue ty gv) := rfl

/-- **`tls_value`** through `ElfTlsGetAddr` (the TLSDESC clause of `MemRefines`). -/
theorem tls_lower_ok (hMR : MRStable F MR) (hM : MemRefines F sb syms isem)
    {f : Clif.Function} (hMRo : MemRelOk F sb syms f MR) (st : LState) {gv : Nat} {name : String}
    {col : Bool} {results : List Nat}
    (hg : ctx.func.globals.lookup gv = some (.tlsSymbol name 0 col)) :
    LowerInstOk isem MR env cp ctx (.tlsValue .i64 gv) results st [[(st.fresh .int).1]]
      (((st.fresh .int).2.fresh .int).2.emit
        (.elfTlsGetAddr name (st.fresh .int).1 ((st.fresh .int).2.fresh .int).1))
      [.elfTlsGetAddr name (st.fresh .int).1 ((st.fresh .int).2.fresh .int).1] := by
  have h1 : (st.fresh .int).1 = .vreg st.nextVreg .int := fresh_fst st
  have h2 : ((st.fresh .int).2.fresh .int).1 = .vreg (st.nextVreg + 1) .int := by
    simp [LState.fresh]
  have hn : (((st.fresh .int).2.fresh .int).2.emit
      (.elfTlsGetAddr name (st.fresh .int).1 ((st.fresh .int).2.fresh .int).1)).nextVreg =
      st.nextVreg + 2 := by
    simp [LState.emit, LState.fresh]
  rw [h1, h2] at *
  refine ⟨by rw [hn]; omega, ?_, ?_⟩
  · intro m hm d hd
    simp only [List.mem_singleton] at hm; subst hm
    rw [vdefs_elfTlsGetAddr] at hd
    rw [hn]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl <;> omega
  intro fr cm ρ w hf hv hdfg hmr
  rw [instOutcome_tlsValue]
  cases he : Clif.evalInst fr cm (.tlsValue .i64 gv) with
  | trap c => intro h; simp [explicitTrapInst] at h
  | stuck _ => trivial
  | ok r =>
  obtain ⟨vals, cm'⟩ := r
  obtain ⟨name', o', col', base, hg', hb, rfl, rfl⟩ := evalInst_tlsValue_inv he
  dsimp only
  rw [hf, hg] at hg'
  cases hg'
  rw [hMRo.symbols _ _ _ hmr] at hb
  obtain ⟨w', o, hs, hsw⟩ := hM.2.2.2.2.2.2.2.2 st.nextVreg (st.nextVreg + 1) name base w hb
  have hrun := seqRun_isem_one (operands_elfTlsGetAddr name st.nextVreg (st.nextVreg + 1))
    (ρ := ρ) hs rfl
  refine ⟨fun m hm u hu => ?_, _, w', hrun, .inr ⟨rfl, ?_⟩, hMR _ _ _ _ hsw hmr⟩
  · simp only [List.mem_singleton] at hm; subst hm
    simp [vuseNums_elfTlsGetAddr] at hu
  intro j rs v hrs hv'
  cases j with
  | succ j => simp at hrs
  | zero =>
  simp only [List.getElem?_cons_zero, Option.some.injEq] at hrs hv'
  subst hrs hv'
  refine ⟨st.nextVreg, .int, rfl, .inl (Nat.le_refl _), ?_⟩
  have hne : st.nextVreg + 1 ≠ st.nextVreg := by omega
  show VHolds _ (vdefUpd _ _ ρ st.nextVreg)
  simp [vdefUpd, writeV, Operand.isDef, Operand.isEarly, Operand.isLate, upd, hne]
  simp [VHolds, Clif.Val.ofInt, ofX, Clif.Ty.width]

end Builders

/-! ## The root rules -/

variable {p : Program} (hp : Data p) {F : BitVec 64 → Prop} {sb : Nat}
  {syms : String → Option Nat} {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}

set_option maxHeartbeats 2000000 in
include hp in
/-- **`tls_value`** (`lower.isle:3217`, rule id 1129, `tls_model` `elf_gd`). -/
theorem tls_value_ok (hMR : MRStable F MR) (hM : MemRefines F sb syms isem) :
    MemRuleOk F sb syms isem MR env cp p rule_lower_3217 := by
  intro f ctx hctx hMRo ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
    hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  mem_inv hp [ext_tls_model_iff, ext_symbol_value_data_tls_iff] at hmatch heval
  have hdat0 := CtxInv.data hctx _ _ _ hi hic
  simp only [hi, Option.some.injEq] at *
  isel_destruct; subst_vars
  have hdat := data_trans hdat0 ‹_›
  have := inv_tlsValue_root hdat
  isel_destruct; subst_vars
  repeat (mem_inv_simp [ext_tls_model_iff, ext_symbol_value_data_tls_iff] at * <;> isel_destruct <;>
    subst_vars)
  have hE := ‹ApplyInternal _ _ _ _ 27 647 _ _ _ _›
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  obtain ⟨rfl, hs⟩ := elf_tls_get_addr_ok hp ctx hco (by omega) hE
  obtain ⟨rfl, hs'⟩ := output_reg_inv hp ctx hco (by omega) hO
  simp only at hs'
  rw [hs] at hs'
  subst hs'
  have hg1 := ‹List.lookup _ ctx.func.globals = some (Clif.GlobalValue.tlsSymbol _ _ _)›
  have hg2 := ‹List.lookup _ f.globals = some (Clif.GlobalValue.tlsSymbol _ 0 _)›
  rw [hctx.func, hg2] at hg1
  cases hg1
  refine ⟨[_], ?_, _, rfl, tls_lower_ok hMR hM hMRo _ (hctx.func ▸ hg2)⟩
  exact Array.push_eq_append

include hp in
/-- **`tls_value`** with `tls_model` `macho` (rule id 1130): never matches (`tls_model` is
`elf_gd`). -/
theorem tls_value_macho_ok : MemRuleOk F sb syms isem MR env cp p rule_lower_3220 := by
  intro f ctx hctx hMRo ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
    hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  mem_inv hp [ext_tls_model_iff] at hmatch
  exact absurd ‹2 = VIdx.TlsModel.ElfGd› (by decide)

end Backend.Proof
