import FV.Backend.Proof.IselMemSem

/-!
# Memory family (M4Mem2): the memory root rules of `lower`

`MemRuleOk` for the 19 memory root rules (`memRootRule`): the loads (1041–1044 `load`,
1052–1057 `uload*`/`sload*`), the stores (1064–1067 `store`, 1068–1070 `istore*`),
`stack_addr` (1093), `symbol_value` (1027), and the never-matching `uextend`/`sextend` of a
load (815, 824: `is_sinkable_inst` fails). Each proof inverts the match and the right-hand
side (`mem_inv`), the instruction data (`CtxInv.data`, `inv_*_root`), then the helper
contracts (`amode_ok`, `*_helper_ok`, …) and ends in a builder of `IselMemSem`.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-! ## Instruction data of the root instructions -/

theorem mem_variantNames_Load : (variantNames 152)[16]? = some "Load" := rfl
theorem mem_variantNames_Store : (variantNames 152)[22]? = some "Store" := rfl
theorem mem_variantNames_UGV : (variantNames 152)[31]? = some "UnaryGlobalValue" := rfl
theorem mem_variantNames_SymbolValue : (variantNames 151)[49]? = some "SymbolValue" := rfl

theorem inv_load_root {f : Clif.Function} {cl : Clif.Inst} {k : Nat} {w1 w2 w3 : V}
    (h : instData f cl = .ok (.data 152 16 [.data 151 k [], w1, w2, w3])) :
    ∃ op ty fl p off, cl = .load op ty fl p off ∧ (variantNames 151)[k]? = some (loadOpcode op) ∧
      w1 = .value p ∧ w2 = .op (.memFlags fl) ∧ w3 = .int off ∧ eTy ty = true ∧
      fl.endianness ≠ some .big := by
  obtain ⟨hf, ho⟩ := instData_inv_names h
  rw [mem_variantNames_Load] at hf
  cases cl <;> simp only [instNames, Option.some.injEq] at hf
  all_goals try (simp at hf; done)
  rename_i op ty fl p off
  simp only [instData] at h
  split at h
  · cases h
  · rename_i he
    split at h
    · cases h
    · rename_i hb
      simp only [pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨-, -, h3⟩ := mkVariant_eq_data h
      simp only [List.cons.injEq, and_true] at h3
      obtain ⟨h0, rfl, rfl, rfl⟩ := h3
      obtain ⟨h4, -, -⟩ := mkVariant_eq_data h0.symm
      refine ⟨op, ty, fl, p, off, rfl, h4, rfl, rfl, rfl, by simpa using he, by simpa using hb⟩

theorem inv_store_root {f : Clif.Function} {cl : Clif.Inst} {k : Nat} {w1 w2 w3 : V}
    (h : instData f cl = .ok (.data 152 22 [.data 151 k [], w1, w2, w3])) :
    ∃ op ty fl x p off, cl = .store op ty fl x p off ∧
      (variantNames 151)[k]? = some (storeOpcode op) ∧ w1 = .values [x, p] ∧
      w2 = .op (.memFlags fl) ∧ w3 = .int off ∧ eTy ty = true ∧ fl.endianness ≠ some .big := by
  obtain ⟨hf, ho⟩ := instData_inv_names h
  rw [mem_variantNames_Store] at hf
  cases cl <;> simp only [instNames, Option.some.injEq] at hf
  all_goals try (simp at hf; done)
  rename_i op ty fl x p off
  simp only [instData] at h
  split at h
  · cases h
  · rename_i he
    split at h
    · cases h
    · rename_i hb
      simp only [pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨-, -, h3⟩ := mkVariant_eq_data h
      simp only [List.cons.injEq, and_true] at h3
      obtain ⟨h0, rfl, rfl, rfl⟩ := h3
      obtain ⟨h4, -, -⟩ := mkVariant_eq_data h0.symm
      refine ⟨op, ty, fl, x, p, off, rfl, h4, rfl, rfl, rfl, by simpa using he, by simpa using hb⟩

theorem inv_symbolValue_root {f : Clif.Function} {cl : Clif.Inst} {w : V}
    (h : instData f cl = .ok (.data 152 31 [.data 151 49 [], w])) :
    ∃ ty gv name off col, cl = .symbolValue ty gv ∧ ty = .i64 ∧ w = .op (.globalValue gv) ∧
      f.globals.lookup gv = some (.symbol name off col) := by
  have hn := instData_names_eq h mem_variantNames_UGV mem_variantNames_SymbolValue
  cases cl <;> simp only [instNames, Prod.mk.injEq] at hn
  all_goals try (simp at hn; done)
  rename_i ty gv
  simp only [instData] at h
  split at h
  · cases h
  · rename_i hty
    split at h
    · rename_i name off col hg
      simp only [pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨-, -, h3⟩ := mkVariant_eq_data h
      simp only [List.cons.injEq, and_true] at h3
      exact ⟨ty, gv, name, off, col, rfl, by simpa using hty, h3.2, hg⟩
    · cases h
    · cases h

theorem data_trans {f : Clif.Function} {inst : Clif.Inst} {info : IInfo} {v : V}
    (hdat : instData f inst = .ok info.data) (hd : v = info.data) : instData f inst = .ok v := by
  rw [hd]; exact hdat

/-- `mem_root hctx hi hic`: identify the matched instruction with `info` (`hi`) and invert its
data (`CtxInv.data`, `inv_*_root`), then the extern calls to a fixpoint. -/
macro "mem_root " hctx:ident hi:ident hic:ident : tactic => `(tactic| (
  have hdat0 := CtxInv.data $hctx _ _ _ $hi $hic
  have $(Lean.mkIdent `hA64) := fun x => CtxInv.addr64 $hctx _ _ _ x $hi $hic
  have hRT := CtxInv.resTys $hctx _ _ _ $hi $hic
  have $(Lean.mkIdent `hRE) := CtxInv.resTysE $hctx _ _ $hi
  simp only [$hi:ident, Option.some.injEq] at *
  isel_destruct; subst_vars
  have hdat := data_trans hdat0 ‹_›
  first
    | have := inv_load_root hdat
    | have := inv_store_root hdat
    | have := inv_symbolValue_root hdat
    | have := inv_stackAddr hdat
  isel_destruct; subst_vars
  repeat (mem_inv_simp [] at * <;> isel_destruct <;> subst_vars)))

section
variable {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config} (hc : cfg.checkOverlap = false)

include hp hc in
theorem output_reg_inv {n : Nat} (hn : 20 ≤ n) {r : Reg} {s s' : LState × Array RuleId} {out : V}
    (h : ApplyInternal p (sem ctx) cfg n 25 172 [.reg r] s out s') :
    out = .regsVec [[r]] ∧ s'.1 = s.1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 9 := ⟨n - 9, by omega⟩
  obtain ⟨st, tr⟩ := s
  unfold ApplyInternal at h
  rw [output_reg_run hp ctx hc st tr k r] at h
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨rfl, rfl⟩

end

variable {p : Program} (hp : Data p) {F : BitVec 64 → Prop} {sb : Nat}
  {syms : String → Option Nat} {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}

include hp in
theorem load_root_finish (hR : Refines F isem) (hMR : MRStable F MR) (hM : MemRefines F sb syms isem)
    {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) (hMRo : MemRelOk F sb syms f MR)
    {cfg : Config} (hc : cfg.checkOverlap = false) {n1 n2 : Nat} (hn1 : 300 ≤ n1) (hn2 : 20 ≤ n2)
    {st st' : LState} {tr tr' : Array RuleId} (hvb : ValsBelow ctx st)
    {op : Clif.LoadOp} {ty : Clif.Ty} {fl : Clif.MemFlags} {x : Nat} {off : Int} {results : List Nat}
    (hety : eTy ty = true) (hfl : fl.endianness ≠ some .big)
    (hp64 : ctx.valueType? x = some (.int 64)) {t : CTy} {aop : LoadOp} {kidx : Nat}
    (htb : t.bytes = aop.bytes) (hb : t.bytes = 1 ∨ t.bytes = 2 ∨ t.bytes = 4 ∨ t.bytes = 8)
    (haop : aop ≠ .fpuLoad128) (hsz : aop.bytes = op.size ty) (hsg : loadSigned aop = op.signed)
    (hofV : ∀ rd amv am, amv.amode? = some am →
      MInst.ofV (.data 58 kidx [.reg rd, amv, .op (.memFlags fl)]) = some (.load aop rd am fl))
    {amv rv out : V} {s2 s3 : LState × Array RuleId}
    (hA : ApplyInternal p (sem ctx) cfg n1 89 574 [.ty t, .value x, .int off] (st, tr) amv s2)
    (hH : ∃ m, MInst.ofV (.data 58 kidx [.reg (s2.1.fresh .int).1, amv, .op (.memFlags fl)]) = some m ∧
      rv = .reg (s2.1.fresh .int).1 ∧ s3.1 = (s2.1.fresh .int).2.emit m)
    (hO : ApplyInternal p (sem ctx) cfg n2 25 172 [rv] s3 out (st', tr')) :
    ∃ ms, st'.emitted = st.emitted ++ ms.toArray ∧ ∃ rss, out = .regsVec rss ∧
      LowerInstOk isem MR env cp ctx (.load op ty fl x off) results st rss st' ms := by
  obtain ⟨ms, am, ham, hok⟩ := amode_ok hp ctx hc hR hctx hn1 hvb hb hA (sb := sb)
  obtain ⟨mi, hmi, rfl, hs3⟩ := hH
  rw [hofV _ _ _ ham, Option.some.injEq] at hmi
  subst hmi
  obtain ⟨rfl, hs'⟩ := output_reg_inv hp ctx hc hn2 hO
  simp only at hs'
  rw [hs3] at hs'
  subst hs'
  rw [htb] at hok
  have hL := load_lower_ok (env := env) (cp := cp) (results := results) hMR hM hctx hMRo hok haop
    hsz hsg (eTy_width hety) hfl hp64
  refine ⟨_, ?_, _, rfl, hL⟩
  have hfr := hok.frag.append (frag_one s2.1 _ (load_ops aop s2.1.nextVreg hok.vregs fl).defs)
  rw [fresh_fst]
  exact hfr.emitted

/-! ## Per-rule size and sign conditions -/

theorem loadOpcode_inj {a b : Clif.LoadOp} (h : loadOpcode a = loadOpcode b) : a = b := by
  cases a <;> cases b <;> simp_all [loadOpcode]

theorem storeOpcode_inj {a b : Clif.StoreOp} (h : storeOpcode a = storeOpcode b) : a = b := by
  cases a <;> cases b <;> simp_all [storeOpcode]

theorem width_of_resTy {g : Nat → Option Clif.Signature} {inst : Clif.Inst} {ty : Clif.Ty}
    (hr : inst.resultTypes g (fun _ => none) = some [ty]) {info : IInfo} {tys : List Clif.Ty} {w : Nat}
    (h2 : CTy.int w = info.resTys.head?.getD .invalid) (h3 : info.resTys = tys.map CTy.ofClif)
    (h4 : inst.resultTypes g (fun _ => none) = some tys) : ty.width = w := by
  rw [hr, Option.some.injEq] at h4
  subst h4
  rw [h3] at h2
  simp only [List.map_cons, List.map_nil, List.head?_cons, Option.getD_some, ofClif_int_width,
    CTy.int.injEq] at h2
  exact h2.symm

theorem ty_bytes8 (ty : Clif.Ty) : ty.bytes * 8 = ty.width := by cases ty <;> rfl

/-- `load.ty` with `ty` of `w` bits, lowered by an unsigned load of `w / 8` bytes. -/
theorem cond_load {g : Nat → Option Clif.Signature} {op : Clif.LoadOp} {ty : Clif.Ty}
    {fl : Clif.MemFlags} {x : Nat} {off : Int} {info : IInfo} {tys : List Clif.Ty} {w : Nat}
    {aop : LoadOp} (h1 : (variantNames 151)[29]? = some (loadOpcode op))
    (h2 : CTy.int w = info.resTys.head?.getD .invalid) (h3 : info.resTys = tys.map CTy.ofClif)
    (h4 : Clif.Inst.resultTypes g (fun _ => none) (Clif.Inst.load op ty fl x off) = some tys) (haw : aop.bytes * 8 = w)
    (hsg : loadSigned aop = false) : aop.bytes = op.size ty ∧ loadSigned aop = op.signed := by
  have h29 : (variantNames 151)[29]? = some (loadOpcode .load) := rfl
  rw [h29, Option.some.injEq] at h1
  obtain rfl := loadOpcode_inj h1.symm
  have hw := width_of_resTy rfl h2 h3 h4
  have := ty_bytes8 ty
  exact ⟨by simp only [Clif.LoadOp.size]; omega, hsg⟩

theorem load_op_of {k : Nat} {cop op : Clif.LoadOp}
    (hk : (variantNames 151)[k]? = some (loadOpcode cop))
    (h1 : (variantNames 151)[k]? = some (loadOpcode op)) : op = cop := by
  rw [hk, Option.some.injEq] at h1
  exact loadOpcode_inj h1.symm

/-- `uload*`/`sload*` (opcode `k`, i.e. `cop`), lowered by `aop`. -/
theorem cond_ext {k : Nat} {cop op : Clif.LoadOp} {ty : Clif.Ty} {aop : LoadOp}
    (hk : (variantNames 151)[k]? = some (loadOpcode cop))
    (hsz : aop.bytes = cop.size ty) (hsg : loadSigned aop = cop.signed)
    (h1 : (variantNames 151)[k]? = some (loadOpcode op)) :
    aop.bytes = op.size ty ∧ loadSigned aop = op.signed := by
  rw [hk, Option.some.injEq] at h1
  obtain rfl := loadOpcode_inj h1
  exact ⟨hsz, hsg⟩

include hp in
theorem store_root_finish (hR : Refines F isem) (hMR : MRStable F MR) (hM : MemRefines F sb syms isem)
    {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) (hMRo : MemRelOk F sb syms f MR)
    {cfg : Config} (hc : cfg.checkOverlap = false) {n1 n3 : Nat} (hn1 : 300 ≤ n1) (hn3 : 60 ≤ n3)
    {st st' : LState} {tr tr' : Array RuleId} (hvb : ValsBelow ctx st)
    {op : Clif.StoreOp} {ty : Clif.Ty} {fl : Clif.MemFlags} {x y : Nat} {off : Int}
    {results : List Nat} (hety : eTy ty = true) (hfl : fl.endianness ≠ some .big)
    (hp64 : ctx.valueType? y = some (.int 64)) (hxr : ctx.valueReg? x = some (.vreg x .int))
    {t : CTy} {aop : StoreOp} {kidx : Nat}
    (htb : t.bytes = aop.bytes) (hb : t.bytes = 1 ∨ t.bytes = 2 ∨ t.bytes = 4 ∨ t.bytes = 8)
    (haop : aop ≠ .fpuStore128)
    (hsz : ∀ (fr : Clif.Frame) (a : BitVec ty.width), DFGCons ctx fr → fr.getAs x ty = .ok a →
      aop.bytes = op.size ty)
    (hofV : ∀ rd amv am, amv.amode? = some am →
      MInst.ofV (.data 58 kidx [.reg rd, amv, .op (.memFlags fl)]) = some (.store aop rd am fl))
    {amv sv out : V} {s2 s4 : LState × Array RuleId}
    (hA : ApplyInternal p (sem ctx) cfg n1 89 574 [.ty t, .value y, .int off] (st, tr) amv s2)
    (hH : sv = .data 46 0 [.data 58 kidx [.reg (.vreg x .int), amv, .op (.memFlags fl)]] ∧
      s4.1 = s2.1)
    (hS : ApplyInternal p (sem ctx) cfg n3 25 243 [sv] s4 out (st', tr')) :
    ∃ ms, st'.emitted = st.emitted ++ ms.toArray ∧ ∃ rss, out = .regsVec rss ∧
      LowerInstOk isem MR env cp ctx (.store op ty fl x y off) results st rss st' ms := by
  obtain ⟨ms, am, ham, hok⟩ := amode_ok hp ctx hc hR hctx hn1 hvb hb hA (sb := sb)
  obtain ⟨rfl, hs4⟩ := hH
  obtain ⟨mi, hmi, hs', rfl⟩ := side_effect_inst_ok hp hc (ctx := ctx) hn3 hS
  rw [hofV _ _ _ ham, Option.some.injEq] at hmi
  subst hmi
  simp only at hs'
  rw [hs4] at hs'
  subst hs'
  rw [htb] at hok
  have hL := store_lower_ok (env := env) (cp := cp) (results := results) hMR hM hctx hMRo hok haop
    hsz (eTy_width hety) hfl hp64 (hvb x _ hxr)
  refine ⟨_, ?_, _, rfl, hL⟩
  exact (hok.frag.append (frag_emit0 s2.1 _ (store_ops aop x hok.vregs fl).defs)).emitted

theorem store_op_of {k : Nat} {cop op : Clif.StoreOp}
    (hk : (variantNames 151)[k]? = some (storeOpcode cop))
    (h1 : (variantNames 151)[k]? = some (storeOpcode op)) : op = cop := by
  rw [hk, Option.some.injEq] at h1
  exact storeOpcode_inj h1.symm

/-- `store` of a `w`-bit value, lowered by a store of `w / 8` bytes. -/
theorem cond_store {ctx : Ctx} {x w : Nat} {ty : Clif.Ty} {aop : StoreOp}
    (hvt : ctx.valueType? x = some (.int w)) (haw : aop.bytes * 8 = w) :
    ∀ (fr : Clif.Frame) (a : BitVec ty.width), DFGCons ctx fr → fr.getAs x ty = .ok a →
      aop.bytes = Clif.StoreOp.size ty .store := by
  intro fr a hd hax
  have h := hd.2 x _ _ hvt (getAs_ok hax)
  rw [ofClif_int_width] at h
  injection h with h
  dsimp only at h
  have := ty_bytes8 ty
  simp only [Clif.StoreOp.size]
  omega

theorem width_stackAddr {g : Nat → Option Clif.Signature} {info : IInfo} {tys : List Clif.Ty}
    {ty : Clif.Ty} {sl : Nat} {o : Int} (hRE : ∀ t ∈ info.resTys, t ∈ eCTys)
    (h3 : info.resTys = tys.map CTy.ofClif)
    (h4 : Clif.Inst.resultTypes g (fun _ => none) (Clif.Inst.stackAddr ty sl o) = some tys) : ty.width ≤ 64 := by
  simp only [Clif.Inst.resultTypes, Option.some.injEq] at h4
  subst h4
  have := hRE (CTy.ofClif ty) (by rw [h3]; simp)
  rw [ofClif_int_width] at this
  simp only [eCTys, List.mem_cons, CTy.int.injEq, List.not_mem_nil, or_false] at this
  omega

set_option maxHeartbeats 2000000 in
include hp in
theorem load_i8_ok (hR : Refines F isem) (hMR : MRStable F MR) (hM : MemRefines F sb syms isem) :
    MemRuleOk F sb syms isem MR env cp p rule_lower_2604 := by
  intro f ctx hctx hMRo ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
    hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  mem_inv hp [] at hmatch heval
  mem_root hctx hi hic
  have hcnd := cond_load (aop := .uload8) ‹_› ‹_› ‹_› ‹_› rfl rfl
  have hA := ‹ApplyInternal _ _ _ _ 89 574 _ _ _ _›
  have hH := ‹ApplyInternal _ _ _ _ 27 529 _ _ _ _›
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  exact load_root_finish hp hR hMR hM hctx hMRo hco (by omega) (by omega) hvb ‹_› ‹_›
    (hA64 _ rfl) (t := .int 8) rfl (.inl rfl) (by decide) hcnd.1 hcnd.2
    (fun rd amv am h => by rw [ofV_uload8', h]; rfl) hA (uload8_helper_ok hp ctx hco (by omega) hH) hO

set_option maxHeartbeats 2000000 in
include hp in
theorem load_i16_ok (hR : Refines F isem) (hMR : MRStable F MR) (hM : MemRefines F sb syms isem) :
    MemRuleOk F sb syms isem MR env cp p rule_lower_2607 := by
  intro f ctx hctx hMRo ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
    hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  mem_inv hp [] at hmatch heval
  mem_root hctx hi hic
  have hcnd := cond_load (aop := .uload16) ‹_› ‹_› ‹_› ‹_› rfl rfl
  have hA := ‹ApplyInternal _ _ _ _ 89 574 _ _ _ _›
  have hH := ‹ApplyInternal _ _ _ _ 27 531 _ _ _ _›
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  exact load_root_finish hp hR hMR hM hctx hMRo hco (by omega) (by omega) hvb ‹_› ‹_›
    (hA64 _ rfl) (t := .int 16) rfl (.inr (.inl rfl)) (by decide) hcnd.1 hcnd.2
    (fun rd amv am h => by rw [ofV_uload16', h]; rfl) hA (uload16_helper_ok hp ctx hco (by omega) hH) hO

set_option maxHeartbeats 2000000 in
include hp in
theorem load_i32_ok (hR : Refines F isem) (hMR : MRStable F MR) (hM : MemRefines F sb syms isem) :
    MemRuleOk F sb syms isem MR env cp p rule_lower_2610 := by
  intro f ctx hctx hMRo ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
    hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  mem_inv hp [] at hmatch heval
  mem_root hctx hi hic
  have hcnd := cond_load (aop := .uload32) ‹_› ‹_› ‹_› ‹_› rfl rfl
  have hA := ‹ApplyInternal _ _ _ _ 89 574 _ _ _ _›
  have hH := ‹ApplyInternal _ _ _ _ 27 533 _ _ _ _›
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  exact load_root_finish hp hR hMR hM hctx hMRo hco (by omega) (by omega) hvb ‹_› ‹_›
    (hA64 _ rfl) (t := .int 32) rfl (.inr (.inr (.inl rfl))) (by decide) hcnd.1 hcnd.2
    (fun rd amv am h => by rw [ofV_uload32', h]; rfl) hA (uload32_helper_ok hp ctx hco (by omega) hH) hO

set_option maxHeartbeats 2000000 in
include hp in
theorem load_i64_ok (hR : Refines F isem) (hMR : MRStable F MR) (hM : MemRefines F sb syms isem) :
    MemRuleOk F sb syms isem MR env cp p rule_lower_2613 := by
  intro f ctx hctx hMRo ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
    hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  mem_inv hp [] at hmatch heval
  mem_root hctx hi hic
  have hcnd := cond_load (aop := .uload64) ‹_› ‹_› ‹_› ‹_› rfl rfl
  have hA := ‹ApplyInternal _ _ _ _ 89 574 _ _ _ _›
  have hH := ‹ApplyInternal _ _ _ _ 27 535 _ _ _ _›
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  exact load_root_finish hp hR hMR hM hctx hMRo hco (by omega) (by omega) hvb ‹_› ‹_›
    (hA64 _ rfl) (t := .int 64) rfl (.inr (.inr (.inr rfl))) (by decide) hcnd.1 hcnd.2
    (fun rd amv am h => by rw [ofV_uload64', h]; rfl) hA (uload64_helper_ok hp ctx hco (by omega) hH) hO

set_option maxHeartbeats 2000000 in
include hp in
theorem uload8_ok (hR : Refines F isem) (hMR : MRStable F MR) (hM : MemRefines F sb syms isem) :
    MemRuleOk F sb syms isem MR env cp p rule_lower_2647 := by
  intro f ctx hctx hMRo ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
    hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  mem_inv hp [] at hmatch heval
  mem_root hctx hi hic
  obtain rfl := load_op_of (k := 31) (cop := .uload8) rfl (by assumption)
  have hA := ‹ApplyInternal _ _ _ _ 89 574 _ _ _ _›
  have hH := ‹ApplyInternal _ _ _ _ 27 529 _ _ _ _›
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  exact load_root_finish hp hR hMR hM hctx hMRo hco (by omega) (by omega) hvb ‹_› ‹_›
    (hA64 _ rfl) (t := .int 8) (aop := .uload8) rfl (.inl rfl) (by decide) rfl rfl
    (fun rd amv am h => by rw [ofV_uload8', h]; rfl) hA (uload8_helper_ok hp ctx hco (by omega) hH) hO

set_option maxHeartbeats 2000000 in
include hp in
theorem sload8_ok (hR : Refines F isem) (hMR : MRStable F MR) (hM : MemRefines F sb syms isem) :
    MemRuleOk F sb syms isem MR env cp p rule_lower_2650 := by
  intro f ctx hctx hMRo ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
    hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  mem_inv hp [] at hmatch heval
  mem_root hctx hi hic
  obtain rfl := load_op_of (k := 32) (cop := .sload8) rfl (by assumption)
  have hA := ‹ApplyInternal _ _ _ _ 89 574 _ _ _ _›
  have hH := ‹ApplyInternal _ _ _ _ 27 530 _ _ _ _›
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  exact load_root_finish hp hR hMR hM hctx hMRo hco (by omega) (by omega) hvb ‹_› ‹_›
    (hA64 _ rfl) (t := .int 8) (aop := .sload8) rfl (.inl rfl) (by decide) rfl rfl
    (fun rd amv am h => by rw [ofV_sload8', h]; rfl) hA (sload8_helper_ok hp ctx hco (by omega) hH) hO

set_option maxHeartbeats 2000000 in
include hp in
theorem uload16_ok (hR : Refines F isem) (hMR : MRStable F MR) (hM : MemRefines F sb syms isem) :
    MemRuleOk F sb syms isem MR env cp p rule_lower_2653 := by
  intro f ctx hctx hMRo ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
    hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  mem_inv hp [] at hmatch heval
  mem_root hctx hi hic
  obtain rfl := load_op_of (k := 34) (cop := .uload16) rfl (by assumption)
  have hA := ‹ApplyInternal _ _ _ _ 89 574 _ _ _ _›
  have hH := ‹ApplyInternal _ _ _ _ 27 531 _ _ _ _›
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  exact load_root_finish hp hR hMR hM hctx hMRo hco (by omega) (by omega) hvb ‹_› ‹_›
    (hA64 _ rfl) (t := .int 16) (aop := .uload16) rfl (.inr (.inl rfl)) (by decide) rfl rfl
    (fun rd amv am h => by rw [ofV_uload16', h]; rfl) hA (uload16_helper_ok hp ctx hco (by omega) hH) hO

set_option maxHeartbeats 2000000 in
include hp in
theorem sload16_ok (hR : Refines F isem) (hMR : MRStable F MR) (hM : MemRefines F sb syms isem) :
    MemRuleOk F sb syms isem MR env cp p rule_lower_2656 := by
  intro f ctx hctx hMRo ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
    hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  mem_inv hp [] at hmatch heval
  mem_root hctx hi hic
  obtain rfl := load_op_of (k := 35) (cop := .sload16) rfl (by assumption)
  have hA := ‹ApplyInternal _ _ _ _ 89 574 _ _ _ _›
  have hH := ‹ApplyInternal _ _ _ _ 27 532 _ _ _ _›
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  exact load_root_finish hp hR hMR hM hctx hMRo hco (by omega) (by omega) hvb ‹_› ‹_›
    (hA64 _ rfl) (t := .int 16) (aop := .sload16) rfl (.inr (.inl rfl)) (by decide) rfl rfl
    (fun rd amv am h => by rw [ofV_sload16', h]; rfl) hA (sload16_helper_ok hp ctx hco (by omega) hH) hO

set_option maxHeartbeats 2000000 in
include hp in
theorem uload32_ok (hR : Refines F isem) (hMR : MRStable F MR) (hM : MemRefines F sb syms isem) :
    MemRuleOk F sb syms isem MR env cp p rule_lower_2659 := by
  intro f ctx hctx hMRo ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
    hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  mem_inv hp [] at hmatch heval
  mem_root hctx hi hic
  obtain rfl := load_op_of (k := 37) (cop := .uload32) rfl (by assumption)
  have hA := ‹ApplyInternal _ _ _ _ 89 574 _ _ _ _›
  have hH := ‹ApplyInternal _ _ _ _ 27 533 _ _ _ _›
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  exact load_root_finish hp hR hMR hM hctx hMRo hco (by omega) (by omega) hvb ‹_› ‹_›
    (hA64 _ rfl) (t := .int 32) (aop := .uload32) rfl (.inr (.inr (.inl rfl))) (by decide) rfl rfl
    (fun rd amv am h => by rw [ofV_uload32', h]; rfl) hA (uload32_helper_ok hp ctx hco (by omega) hH) hO

set_option maxHeartbeats 2000000 in
include hp in
theorem sload32_ok (hR : Refines F isem) (hMR : MRStable F MR) (hM : MemRefines F sb syms isem) :
    MemRuleOk F sb syms isem MR env cp p rule_lower_2662 := by
  intro f ctx hctx hMRo ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
    hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  mem_inv hp [] at hmatch heval
  mem_root hctx hi hic
  obtain rfl := load_op_of (k := 38) (cop := .sload32) rfl (by assumption)
  have hA := ‹ApplyInternal _ _ _ _ 89 574 _ _ _ _›
  have hH := ‹ApplyInternal _ _ _ _ 27 534 _ _ _ _›
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  exact load_root_finish hp hR hMR hM hctx hMRo hco (by omega) (by omega) hvb ‹_› ‹_›
    (hA64 _ rfl) (t := .int 32) (aop := .sload32) rfl (.inr (.inr (.inl rfl))) (by decide) rfl rfl
    (fun rd amv am h => by rw [ofV_sload32', h]; rfl) hA (sload32_helper_ok hp ctx hco (by omega) hH) hO

set_option maxHeartbeats 2000000 in
include hp in
theorem store_i8_ok (hR : Refines F isem) (hMR : MRStable F MR) (hM : MemRefines F sb syms isem) :
    MemRuleOk F sb syms isem MR env cp p rule_lower_2705 := by
  intro f ctx hctx hMRo ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
    hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  mem_inv hp [] at hmatch heval
  mem_root hctx hi hic
  mem_vregs hctx
  obtain rfl := store_op_of (k := 30) (cop := .store) rfl (by assumption)
  have hA := ‹ApplyInternal _ _ _ _ 89 574 _ _ _ _›
  have hH := ‹ApplyInternal _ _ _ _ 46 541 _ _ _ _›
  have hS := ‹ApplyInternal _ _ _ _ 25 243 _ _ _ _›
  exact store_root_finish hp hR hMR hM hctx hMRo hco (by omega) (by omega) hvb ‹_› ‹_›
    (hA64 _ rfl) ‹_› (t := .int 8) (aop := .store8) rfl (.inl rfl) (by decide) (cond_store ‹_› rfl)
    (fun rd amv am h => by rw [ofV_store8', h]; rfl) hA (store8_helper_ok hp ctx hco (by omega) hH) hS

set_option maxHeartbeats 2000000 in
include hp in
theorem store_i16_ok (hR : Refines F isem) (hMR : MRStable F MR) (hM : MemRefines F sb syms isem) :
    MemRuleOk F sb syms isem MR env cp p rule_lower_2709 := by
  intro f ctx hctx hMRo ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
    hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  mem_inv hp [] at hmatch heval
  mem_root hctx hi hic
  mem_vregs hctx
  obtain rfl := store_op_of (k := 30) (cop := .store) rfl (by assumption)
  have hA := ‹ApplyInternal _ _ _ _ 89 574 _ _ _ _›
  have hH := ‹ApplyInternal _ _ _ _ 46 542 _ _ _ _›
  have hS := ‹ApplyInternal _ _ _ _ 25 243 _ _ _ _›
  exact store_root_finish hp hR hMR hM hctx hMRo hco (by omega) (by omega) hvb ‹_› ‹_›
    (hA64 _ rfl) ‹_› (t := .int 16) (aop := .store16) rfl (.inr (.inl rfl)) (by decide) (cond_store ‹_› rfl)
    (fun rd amv am h => by rw [ofV_store16', h]; rfl) hA (store16_helper_ok hp ctx hco (by omega) hH) hS

set_option maxHeartbeats 2000000 in
include hp in
theorem store_i32_ok (hR : Refines F isem) (hMR : MRStable F MR) (hM : MemRefines F sb syms isem) :
    MemRuleOk F sb syms isem MR env cp p rule_lower_2713 := by
  intro f ctx hctx hMRo ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
    hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  mem_inv hp [] at hmatch heval
  mem_root hctx hi hic
  mem_vregs hctx
  obtain rfl := store_op_of (k := 30) (cop := .store) rfl (by assumption)
  have hA := ‹ApplyInternal _ _ _ _ 89 574 _ _ _ _›
  have hH := ‹ApplyInternal _ _ _ _ 46 543 _ _ _ _›
  have hS := ‹ApplyInternal _ _ _ _ 25 243 _ _ _ _›
  exact store_root_finish hp hR hMR hM hctx hMRo hco (by omega) (by omega) hvb ‹_› ‹_›
    (hA64 _ rfl) ‹_› (t := .int 32) (aop := .store32) rfl (.inr (.inr (.inl rfl))) (by decide) (cond_store ‹_› rfl)
    (fun rd amv am h => by rw [ofV_store32', h]; rfl) hA (store32_helper_ok hp ctx hco (by omega) hH) hS

set_option maxHeartbeats 2000000 in
include hp in
theorem store_i64_ok (hR : Refines F isem) (hMR : MRStable F MR) (hM : MemRefines F sb syms isem) :
    MemRuleOk F sb syms isem MR env cp p rule_lower_2717 := by
  intro f ctx hctx hMRo ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
    hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  mem_inv hp [] at hmatch heval
  mem_root hctx hi hic
  mem_vregs hctx
  obtain rfl := store_op_of (k := 30) (cop := .store) rfl (by assumption)
  have hA := ‹ApplyInternal _ _ _ _ 89 574 _ _ _ _›
  have hH := ‹ApplyInternal _ _ _ _ 46 544 _ _ _ _›
  have hS := ‹ApplyInternal _ _ _ _ 25 243 _ _ _ _›
  exact store_root_finish hp hR hMR hM hctx hMRo hco (by omega) (by omega) hvb ‹_› ‹_›
    (hA64 _ rfl) ‹_› (t := .int 64) (aop := .store64) rfl (.inr (.inr (.inr rfl))) (by decide) (cond_store ‹_› rfl)
    (fun rd amv am h => by rw [ofV_store64', h]; rfl) hA (store64_helper_ok hp ctx hco (by omega) hH) hS

set_option maxHeartbeats 2000000 in
include hp in
theorem istore8_ok (hR : Refines F isem) (hMR : MRStable F MR) (hM : MemRefines F sb syms isem) :
    MemRuleOk F sb syms isem MR env cp p rule_lower_2722 := by
  intro f ctx hctx hMRo ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
    hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  mem_inv hp [] at hmatch heval
  mem_root hctx hi hic
  mem_vregs hctx
  obtain rfl := store_op_of (k := 33) (cop := .istore8) rfl (by assumption)
  have hA := ‹ApplyInternal _ _ _ _ 89 574 _ _ _ _›
  have hH := ‹ApplyInternal _ _ _ _ 46 541 _ _ _ _›
  have hS := ‹ApplyInternal _ _ _ _ 25 243 _ _ _ _›
  exact store_root_finish hp hR hMR hM hctx hMRo hco (by omega) (by omega) hvb ‹_› ‹_›
    (hA64 _ rfl) ‹_› (t := .int 8) (aop := .store8) rfl (.inl rfl) (by decide) (fun _ _ _ _ => rfl)
    (fun rd amv am h => by rw [ofV_store8', h]; rfl) hA (store8_helper_ok hp ctx hco (by omega) hH) hS

set_option maxHeartbeats 2000000 in
include hp in
theorem istore16_ok (hR : Refines F isem) (hMR : MRStable F MR) (hM : MemRefines F sb syms isem) :
    MemRuleOk F sb syms isem MR env cp p rule_lower_2726 := by
  intro f ctx hctx hMRo ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
    hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  mem_inv hp [] at hmatch heval
  mem_root hctx hi hic
  mem_vregs hctx
  obtain rfl := store_op_of (k := 36) (cop := .istore16) rfl (by assumption)
  have hA := ‹ApplyInternal _ _ _ _ 89 574 _ _ _ _›
  have hH := ‹ApplyInternal _ _ _ _ 46 542 _ _ _ _›
  have hS := ‹ApplyInternal _ _ _ _ 25 243 _ _ _ _›
  exact store_root_finish hp hR hMR hM hctx hMRo hco (by omega) (by omega) hvb ‹_› ‹_›
    (hA64 _ rfl) ‹_› (t := .int 16) (aop := .store16) rfl (.inr (.inl rfl)) (by decide) (fun _ _ _ _ => rfl)
    (fun rd amv am h => by rw [ofV_store16', h]; rfl) hA (store16_helper_ok hp ctx hco (by omega) hH) hS

set_option maxHeartbeats 2000000 in
include hp in
theorem istore32_ok (hR : Refines F isem) (hMR : MRStable F MR) (hM : MemRefines F sb syms isem) :
    MemRuleOk F sb syms isem MR env cp p rule_lower_2730 := by
  intro f ctx hctx hMRo ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
    hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  mem_inv hp [] at hmatch heval
  mem_root hctx hi hic
  mem_vregs hctx
  obtain rfl := store_op_of (k := 39) (cop := .istore32) rfl (by assumption)
  have hA := ‹ApplyInternal _ _ _ _ 89 574 _ _ _ _›
  have hH := ‹ApplyInternal _ _ _ _ 46 543 _ _ _ _›
  have hS := ‹ApplyInternal _ _ _ _ 25 243 _ _ _ _›
  exact store_root_finish hp hR hMR hM hctx hMRo hco (by omega) (by omega) hvb ‹_› ‹_›
    (hA64 _ rfl) ‹_› (t := .int 32) (aop := .store32) rfl (.inr (.inr (.inl rfl))) (by decide) (fun _ _ _ _ => rfl)
    (fun rd amv am h => by rw [ofV_store32', h]; rfl) hA (store32_helper_ok hp ctx hco (by omega) hH) hS

set_option maxHeartbeats 2000000 in
include hp in
/-- **`stack_addr`** (`lower.isle:2849`, rule id 1093). -/
theorem stack_addr_ok (hMR : MRStable F MR) (hM : MemRefines F sb syms isem) :
    MemRuleOk F sb syms isem MR env cp p rule_lower_2849 := by
  intro f ctx hctx hMRo ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
    hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  mem_inv hp [] at hmatch heval
  mem_root hctx hi hic
  have hC := ‹ApplyInternal _ _ _ _ 27 643 _ _ _ _›
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  obtain ⟨base, hbase, rfl, hs3⟩ := compute_stack_addr_ok hp ctx hco (by omega) hC
  obtain ⟨rfl, hs'⟩ := output_reg_inv hp ctx hco (by omega) hO
  simp only at hs'
  rw [hs3] at hs'
  subst hs'
  refine ⟨_, ?_, _, rfl, stackAddr_lower_ok hMR hM hctx hMRo hbase
    (width_stackAddr hRE (by assumption) (by assumption))⟩
  rw [fresh_fst]
  exact (frag_one _ (.loadAddr (.vreg _ .int) (.slotOffset _)) rfl).emitted

set_option maxHeartbeats 2000000 in
include hp in
/-- **`symbol_value`** (`lower.isle:2491`, rule id 1027). -/
theorem symbol_value_ok (hR : Refines F isem) (hMR : MRStable F MR)
    (hM : MemRefines F sb syms isem) : MemRuleOk F sb syms isem MR env cp p rule_lower_2491 := by
  intro f ctx hctx hMRo ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
    hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  mem_inv hp [] at hmatch heval
  mem_root hctx hi hic
  have hL := ‹ApplyInternal _ _ _ _ 27 570 _ _ _ _›
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  obtain ⟨ms, d, rfl, hsym⟩ := load_ext_name_ok hp ctx hco hR hM (by omega) hL
  obtain ⟨rfl, hs'⟩ := output_reg_inv hp ctx hco (by omega) hO
  simp only at hs'
  subst hs'
  exact ⟨ms, hsym.frag.emitted, _, rfl, symbol_lower_ok hMR hMRo hsym ‹_›⟩

include hp in
/-- **`uextend_load`** (rule id 815): never matches (`is_sinkable_inst` fails). -/
theorem uextend_load_ok : MemRuleOk F sb syms isem MR env cp p rule_lower_1300 := by
  intro f ctx hctx hMRo ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
    hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  mem_inv hp [ctor_is_sinkable_inst] at hmatch

include hp in
/-- **`sextend_load`** (rule id 824): never matches (`is_sinkable_inst` fails). -/
theorem sextend_load_ok : MemRuleOk F sb syms isem MR env cp p rule_lower_1359 := by
  intro f ctx hctx hMRo ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
    hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  mem_inv hp [ctor_is_sinkable_inst] at hmatch

/-! ## `MemRulesCorrect` -/

/-- The memory root rules of `lower`, in order. -/
theorem lower_memRoot_filter : (program.rulesOf TId.lower).filter memRootRule =
    [rule_lower_1300, rule_lower_1359, rule_lower_2491, rule_lower_2604, rule_lower_2607, rule_lower_2610, rule_lower_2613, rule_lower_2647, rule_lower_2650, rule_lower_2653, rule_lower_2656, rule_lower_2659, rule_lower_2662, rule_lower_2705, rule_lower_2709, rule_lower_2713, rule_lower_2717, rule_lower_2722, rule_lower_2726, rule_lower_2730, rule_lower_2849] := by
  rw [program_rulesOf_686]
  rfl

/-- **The memory family (M4)**: every memory root rule of `lower` is correct under
`MemRefines`, for every function whose memory relation is `MemRelOk`. -/
theorem memRulesCorrect_program : MemRulesCorrect program := by
  intro F sb syms isem MR env cp hR hMR hM r hr hmem
  have hsub : r ∈ (program.rulesOf TId.lower).filter memRootRule := List.mem_filter.2 ⟨hr, hmem⟩
  rw [lower_memRoot_filter] at hsub
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hsub
  rcases hsub with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact uextend_load_ok data_program
  · exact sextend_load_ok data_program
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
