import FV.Backend.Proof.IselMemRoots
import FV.Backend.Proof.IselBaseTI
import FV.Backend.Proof.IselMemBaseTI
import FV.Backend.Proof.IselMemSemMemTI

/-!
# `IselMemRoots` over typed contexts (S11e5 Stage C, slice 7)

The `CtxInv` proofs of `IselMemRoots`, restated over float-capable contexts (`CtxT`, `LowerRuleOkTI`):
the values whose registers they use are in integer positions (`CtxInvT.valueRegI`, `int_posA`).
-/

namespace Backend.Proof
open Backend Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
section
variable {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config} (hc : cfg.checkOverlap = false)
end
variable {p : Program} (hp : Data p) {Rd : BitVec 64 → Prop} {F : BitVec 64 → Prop} {sb : Nat}
  {syms : String → Option Nat} {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
include hp in
theorem load_root_finishTI (hR : Refines F isem) (hMR : MRStable F MR) (hM : MemRefinesR Rd F sb syms isem)
    {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) (hMRo : MemRelOk F sb syms f MR)
    {cfg : Config} (hc : cfg.checkOverlap = false) {n1 n2 : Nat} (hn1 : 300 ≤ n1) (hn2 : 20 ≤ n2)
    {st st' : LState} {tr tr' : Array RuleId} (hvb : ValsBelow ctx st)
    {op : Clif.LoadOp} {ty : Clif.Ty} {fl : Clif.MemFlags} {x : Nat} {off : Int} {results : List Nat}
    (hety : valTyOk ty = true) (hfl : fl.endianness ≠ some .big)
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
      LowerInstOkR Rd isem MR env cp ctx (.load op ty fl x off) results st rss st' ms := by
  obtain ⟨ms, am, ham, hok⟩ := amode_okT hp ctx hc hR hctx (hx := by int_posA) hn1 hvb hb hA (sb := sb)
  obtain ⟨mi, hmi, rfl, hs3⟩ := hH
  rw [hofV _ _ _ ham, Option.some.injEq] at hmi
  subst hmi
  obtain ⟨rfl, hs'⟩ := output_reg_inv hp ctx hc hn2 hO
  simp only at hs'
  rw [hs3] at hs'
  subst hs'
  rw [htb] at hok
  have hL := load_lower_okTI (env := env) (cp := cp) (results := results) hMR hM hctx hMRo hok haop
    hsz hsg (valTyOk_width hety) hfl hp64
  refine ⟨_, ?_, _, rfl, hL⟩
  have hfr := hok.frag.append (frag_one s2.1 _ (load_ops aop s2.1.nextVreg hok.vregs fl).defs)
  rw [fresh_fst]
  exact hfr.emitted

include hp in
theorem store_root_finishTI (hR : Refines F isem) (hMR : MRStable F MR) (hM : MemRefinesR Rd F sb syms isem)
    {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) (hMRo : MemRelOk F sb syms f MR)
    {cfg : Config} (hc : cfg.checkOverlap = false) {n1 n3 : Nat} (hn1 : 300 ≤ n1) (hn3 : 60 ≤ n3)
    {st st' : LState} {tr tr' : Array RuleId} (hvb : ValsBelow ctx st)
    {op : Clif.StoreOp} {ty : Clif.Ty} {fl : Clif.MemFlags} {x y : Nat} {off : Int}
    {results : List Nat} (hety : valTyOk ty = true) (hfl : fl.endianness ≠ some .big)
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
      LowerInstOkR Rd isem MR env cp ctx (.store op ty fl x y off) results st rss st' ms := by
  obtain ⟨ms, am, ham, hok⟩ := amode_okT hp ctx hc hR hctx (hx := by int_posA) hn1 hvb hb hA (sb := sb)
  obtain ⟨rfl, hs4⟩ := hH
  obtain ⟨mi, hmi, hs', rfl⟩ := side_effect_inst_ok hp hc (ctx := ctx) hn3 hS
  rw [hofV _ _ _ ham, Option.some.injEq] at hmi
  subst hmi
  simp only at hs'
  rw [hs4] at hs'
  subst hs'
  rw [htb] at hok
  have hL := store_lower_okTI (env := env) (cp := cp) (results := results) hMR hM hctx hMRo hok haop
    hsz (valTyOk_width hety) hfl hp64 (hvb x _ hxr)
  refine ⟨_, ?_, _, rfl, hL.toR⟩
  exact (hok.frag.append (frag_emit0 s2.1 _ (store_ops aop x hok.vregs fl).defs)).emitted

set_option maxHeartbeats 2000000 in
include hp in
theorem load_i8_okTI (hR : Refines F isem) (hMR : MRStable F MR) (hM : MemRefinesR Rd F sb syms isem) :
    MemRuleOkRTX Rd F sb syms isem MR env cp p rule_lower_2604 := by
  intro f ctx hctxT hMRo ii info inst hi hic hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hic
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  mem_inv hp [] at hmatch heval
  mem_rootTI hctx hi hic
  have hcnd := cond_load (aop := .uload8) ‹_› ‹_› ‹_› ‹_› rfl rfl
  have hA := ‹ApplyInternal _ _ _ _ 89 574 _ _ _ _›
  have hH := ‹ApplyInternal _ _ _ _ 27 529 _ _ _ _›
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  exact load_root_finishTI hp hR hMR hM hctx hMRo hco (by omega) (by omega) hvb ‹_› ‹_›
    (hA64 _ rfl) (t := .int 8) rfl (.inl rfl) (by decide) hcnd.1 hcnd.2
    (fun rd amv am h => by rw [ofV_uload8', h]; rfl) hA (uload8_helper_ok hp ctx hco (by omega) hH) hO

set_option maxHeartbeats 2000000 in
include hp in
theorem load_i16_okTI (hR : Refines F isem) (hMR : MRStable F MR) (hM : MemRefinesR Rd F sb syms isem) :
    MemRuleOkRTX Rd F sb syms isem MR env cp p rule_lower_2607 := by
  intro f ctx hctxT hMRo ii info inst hi hic hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hic
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  mem_inv hp [] at hmatch heval
  mem_rootTI hctx hi hic
  have hcnd := cond_load (aop := .uload16) ‹_› ‹_› ‹_› ‹_› rfl rfl
  have hA := ‹ApplyInternal _ _ _ _ 89 574 _ _ _ _›
  have hH := ‹ApplyInternal _ _ _ _ 27 531 _ _ _ _›
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  exact load_root_finishTI hp hR hMR hM hctx hMRo hco (by omega) (by omega) hvb ‹_› ‹_›
    (hA64 _ rfl) (t := .int 16) rfl (.inr (.inl rfl)) (by decide) hcnd.1 hcnd.2
    (fun rd amv am h => by rw [ofV_uload16', h]; rfl) hA (uload16_helper_ok hp ctx hco (by omega) hH) hO

set_option maxHeartbeats 2000000 in
include hp in
theorem load_i32_okTI (hR : Refines F isem) (hMR : MRStable F MR) (hM : MemRefinesR Rd F sb syms isem) :
    MemRuleOkRTX Rd F sb syms isem MR env cp p rule_lower_2610 := by
  intro f ctx hctxT hMRo ii info inst hi hic hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hic
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  mem_inv hp [] at hmatch heval
  mem_rootTI hctx hi hic
  have hcnd := cond_load (aop := .uload32) ‹_› ‹_› ‹_› ‹_› rfl rfl
  have hA := ‹ApplyInternal _ _ _ _ 89 574 _ _ _ _›
  have hH := ‹ApplyInternal _ _ _ _ 27 533 _ _ _ _›
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  exact load_root_finishTI hp hR hMR hM hctx hMRo hco (by omega) (by omega) hvb ‹_› ‹_›
    (hA64 _ rfl) (t := .int 32) rfl (.inr (.inr (.inl rfl))) (by decide) hcnd.1 hcnd.2
    (fun rd amv am h => by rw [ofV_uload32', h]; rfl) hA (uload32_helper_ok hp ctx hco (by omega) hH) hO

set_option maxHeartbeats 2000000 in
include hp in
theorem load_i64_okTI (hR : Refines F isem) (hMR : MRStable F MR) (hM : MemRefinesR Rd F sb syms isem) :
    MemRuleOkRTX Rd F sb syms isem MR env cp p rule_lower_2613 := by
  intro f ctx hctxT hMRo ii info inst hi hic hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hic
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  mem_inv hp [] at hmatch heval
  mem_rootTI hctx hi hic
  have hcnd := cond_load (aop := .uload64) ‹_› ‹_› ‹_› ‹_› rfl rfl
  have hA := ‹ApplyInternal _ _ _ _ 89 574 _ _ _ _›
  have hH := ‹ApplyInternal _ _ _ _ 27 535 _ _ _ _›
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  exact load_root_finishTI hp hR hMR hM hctx hMRo hco (by omega) (by omega) hvb ‹_› ‹_›
    (hA64 _ rfl) (t := .int 64) rfl (.inr (.inr (.inr rfl))) (by decide) hcnd.1 hcnd.2
    (fun rd amv am h => by rw [ofV_uload64', h]; rfl) hA (uload64_helper_ok hp ctx hco (by omega) hH) hO

set_option maxHeartbeats 2000000 in
include hp in
theorem uload8_okTI (hR : Refines F isem) (hMR : MRStable F MR) (hM : MemRefinesR Rd F sb syms isem) :
    MemRuleOkRTX Rd F sb syms isem MR env cp p rule_lower_2647 := by
  intro f ctx hctxT hMRo ii info inst hi hic hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hic
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  mem_inv hp [] at hmatch heval
  mem_rootTI hctx hi hic
  obtain rfl := load_op_of (k := 31) (cop := .uload8) rfl (by assumption)
  have hA := ‹ApplyInternal _ _ _ _ 89 574 _ _ _ _›
  have hH := ‹ApplyInternal _ _ _ _ 27 529 _ _ _ _›
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  exact load_root_finishTI hp hR hMR hM hctx hMRo hco (by omega) (by omega) hvb ‹_› ‹_›
    (hA64 _ rfl) (t := .int 8) (aop := .uload8) rfl (.inl rfl) (by decide) rfl rfl
    (fun rd amv am h => by rw [ofV_uload8', h]; rfl) hA (uload8_helper_ok hp ctx hco (by omega) hH) hO

set_option maxHeartbeats 2000000 in
include hp in
theorem sload8_okTI (hR : Refines F isem) (hMR : MRStable F MR) (hM : MemRefinesR Rd F sb syms isem) :
    MemRuleOkRTX Rd F sb syms isem MR env cp p rule_lower_2650 := by
  intro f ctx hctxT hMRo ii info inst hi hic hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hic
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  mem_inv hp [] at hmatch heval
  mem_rootTI hctx hi hic
  obtain rfl := load_op_of (k := 32) (cop := .sload8) rfl (by assumption)
  have hA := ‹ApplyInternal _ _ _ _ 89 574 _ _ _ _›
  have hH := ‹ApplyInternal _ _ _ _ 27 530 _ _ _ _›
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  exact load_root_finishTI hp hR hMR hM hctx hMRo hco (by omega) (by omega) hvb ‹_› ‹_›
    (hA64 _ rfl) (t := .int 8) (aop := .sload8) rfl (.inl rfl) (by decide) rfl rfl
    (fun rd amv am h => by rw [ofV_sload8', h]; rfl) hA (sload8_helper_ok hp ctx hco (by omega) hH) hO

set_option maxHeartbeats 2000000 in
include hp in
theorem uload16_okTI (hR : Refines F isem) (hMR : MRStable F MR) (hM : MemRefinesR Rd F sb syms isem) :
    MemRuleOkRTX Rd F sb syms isem MR env cp p rule_lower_2653 := by
  intro f ctx hctxT hMRo ii info inst hi hic hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hic
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  mem_inv hp [] at hmatch heval
  mem_rootTI hctx hi hic
  obtain rfl := load_op_of (k := 34) (cop := .uload16) rfl (by assumption)
  have hA := ‹ApplyInternal _ _ _ _ 89 574 _ _ _ _›
  have hH := ‹ApplyInternal _ _ _ _ 27 531 _ _ _ _›
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  exact load_root_finishTI hp hR hMR hM hctx hMRo hco (by omega) (by omega) hvb ‹_› ‹_›
    (hA64 _ rfl) (t := .int 16) (aop := .uload16) rfl (.inr (.inl rfl)) (by decide) rfl rfl
    (fun rd amv am h => by rw [ofV_uload16', h]; rfl) hA (uload16_helper_ok hp ctx hco (by omega) hH) hO

set_option maxHeartbeats 2000000 in
include hp in
theorem sload16_okTI (hR : Refines F isem) (hMR : MRStable F MR) (hM : MemRefinesR Rd F sb syms isem) :
    MemRuleOkRTX Rd F sb syms isem MR env cp p rule_lower_2656 := by
  intro f ctx hctxT hMRo ii info inst hi hic hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hic
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  mem_inv hp [] at hmatch heval
  mem_rootTI hctx hi hic
  obtain rfl := load_op_of (k := 35) (cop := .sload16) rfl (by assumption)
  have hA := ‹ApplyInternal _ _ _ _ 89 574 _ _ _ _›
  have hH := ‹ApplyInternal _ _ _ _ 27 532 _ _ _ _›
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  exact load_root_finishTI hp hR hMR hM hctx hMRo hco (by omega) (by omega) hvb ‹_› ‹_›
    (hA64 _ rfl) (t := .int 16) (aop := .sload16) rfl (.inr (.inl rfl)) (by decide) rfl rfl
    (fun rd amv am h => by rw [ofV_sload16', h]; rfl) hA (sload16_helper_ok hp ctx hco (by omega) hH) hO

set_option maxHeartbeats 2000000 in
include hp in
theorem uload32_okTI (hR : Refines F isem) (hMR : MRStable F MR) (hM : MemRefinesR Rd F sb syms isem) :
    MemRuleOkRTX Rd F sb syms isem MR env cp p rule_lower_2659 := by
  intro f ctx hctxT hMRo ii info inst hi hic hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hic
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  mem_inv hp [] at hmatch heval
  mem_rootTI hctx hi hic
  obtain rfl := load_op_of (k := 37) (cop := .uload32) rfl (by assumption)
  have hA := ‹ApplyInternal _ _ _ _ 89 574 _ _ _ _›
  have hH := ‹ApplyInternal _ _ _ _ 27 533 _ _ _ _›
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  exact load_root_finishTI hp hR hMR hM hctx hMRo hco (by omega) (by omega) hvb ‹_› ‹_›
    (hA64 _ rfl) (t := .int 32) (aop := .uload32) rfl (.inr (.inr (.inl rfl))) (by decide) rfl rfl
    (fun rd amv am h => by rw [ofV_uload32', h]; rfl) hA (uload32_helper_ok hp ctx hco (by omega) hH) hO

set_option maxHeartbeats 2000000 in
include hp in
theorem sload32_okTI (hR : Refines F isem) (hMR : MRStable F MR) (hM : MemRefinesR Rd F sb syms isem) :
    MemRuleOkRTX Rd F sb syms isem MR env cp p rule_lower_2662 := by
  intro f ctx hctxT hMRo ii info inst hi hic hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hic
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  mem_inv hp [] at hmatch heval
  mem_rootTI hctx hi hic
  obtain rfl := load_op_of (k := 38) (cop := .sload32) rfl (by assumption)
  have hA := ‹ApplyInternal _ _ _ _ 89 574 _ _ _ _›
  have hH := ‹ApplyInternal _ _ _ _ 27 534 _ _ _ _›
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  exact load_root_finishTI hp hR hMR hM hctx hMRo hco (by omega) (by omega) hvb ‹_› ‹_›
    (hA64 _ rfl) (t := .int 32) (aop := .sload32) rfl (.inr (.inr (.inl rfl))) (by decide) rfl rfl
    (fun rd amv am h => by rw [ofV_sload32', h]; rfl) hA (sload32_helper_ok hp ctx hco (by omega) hH) hO

set_option maxHeartbeats 2000000 in
include hp in
theorem store_i8_okTI (hR : Refines F isem) (hMR : MRStable F MR) (hM : MemRefinesR Rd F sb syms isem) :
    MemRuleOkRTX Rd F sb syms isem MR env cp p rule_lower_2705 := by
  intro f ctx hctxT hMRo ii info inst hi hic hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hic
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  mem_inv hp [] at hmatch heval
  mem_rootTI hctx hi hic
  mem_vregsT hctx
  obtain rfl := store_op_of (k := 30) (cop := .store) rfl (by assumption)
  have hA := ‹ApplyInternal _ _ _ _ 89 574 _ _ _ _›
  have hH := ‹ApplyInternal _ _ _ _ 46 541 _ _ _ _›
  have hS := ‹ApplyInternal _ _ _ _ 25 243 _ _ _ _›
  exact store_root_finishTI hp hR hMR hM hctx hMRo hco (by omega) (by omega) hvb ‹_› ‹_›
    (hA64 _ rfl) ‹_› (t := .int 8) (aop := .store8) rfl (.inl rfl) (by decide) (cond_store ‹_› rfl)
    (fun rd amv am h => by rw [ofV_store8', h]; rfl) hA (store8_helper_ok hp ctx hco (by omega) hH) hS

set_option maxHeartbeats 2000000 in
include hp in
theorem store_i16_okTI (hR : Refines F isem) (hMR : MRStable F MR) (hM : MemRefinesR Rd F sb syms isem) :
    MemRuleOkRTX Rd F sb syms isem MR env cp p rule_lower_2709 := by
  intro f ctx hctxT hMRo ii info inst hi hic hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hic
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  mem_inv hp [] at hmatch heval
  mem_rootTI hctx hi hic
  mem_vregsT hctx
  obtain rfl := store_op_of (k := 30) (cop := .store) rfl (by assumption)
  have hA := ‹ApplyInternal _ _ _ _ 89 574 _ _ _ _›
  have hH := ‹ApplyInternal _ _ _ _ 46 542 _ _ _ _›
  have hS := ‹ApplyInternal _ _ _ _ 25 243 _ _ _ _›
  exact store_root_finishTI hp hR hMR hM hctx hMRo hco (by omega) (by omega) hvb ‹_› ‹_›
    (hA64 _ rfl) ‹_› (t := .int 16) (aop := .store16) rfl (.inr (.inl rfl)) (by decide) (cond_store ‹_› rfl)
    (fun rd amv am h => by rw [ofV_store16', h]; rfl) hA (store16_helper_ok hp ctx hco (by omega) hH) hS

set_option maxHeartbeats 2000000 in
include hp in
theorem store_i32_okTI (hR : Refines F isem) (hMR : MRStable F MR) (hM : MemRefinesR Rd F sb syms isem) :
    MemRuleOkRTX Rd F sb syms isem MR env cp p rule_lower_2713 := by
  intro f ctx hctxT hMRo ii info inst hi hic hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hic
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  mem_inv hp [] at hmatch heval
  mem_rootTI hctx hi hic
  mem_vregsT hctx
  obtain rfl := store_op_of (k := 30) (cop := .store) rfl (by assumption)
  have hA := ‹ApplyInternal _ _ _ _ 89 574 _ _ _ _›
  have hH := ‹ApplyInternal _ _ _ _ 46 543 _ _ _ _›
  have hS := ‹ApplyInternal _ _ _ _ 25 243 _ _ _ _›
  exact store_root_finishTI hp hR hMR hM hctx hMRo hco (by omega) (by omega) hvb ‹_› ‹_›
    (hA64 _ rfl) ‹_› (t := .int 32) (aop := .store32) rfl (.inr (.inr (.inl rfl))) (by decide) (cond_store ‹_› rfl)
    (fun rd amv am h => by rw [ofV_store32', h]; rfl) hA (store32_helper_ok hp ctx hco (by omega) hH) hS

set_option maxHeartbeats 2000000 in
include hp in
theorem store_i64_okTI (hR : Refines F isem) (hMR : MRStable F MR) (hM : MemRefinesR Rd F sb syms isem) :
    MemRuleOkRTX Rd F sb syms isem MR env cp p rule_lower_2717 := by
  intro f ctx hctxT hMRo ii info inst hi hic hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hic
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  mem_inv hp [] at hmatch heval
  mem_rootTI hctx hi hic
  mem_vregsT hctx
  obtain rfl := store_op_of (k := 30) (cop := .store) rfl (by assumption)
  have hA := ‹ApplyInternal _ _ _ _ 89 574 _ _ _ _›
  have hH := ‹ApplyInternal _ _ _ _ 46 544 _ _ _ _›
  have hS := ‹ApplyInternal _ _ _ _ 25 243 _ _ _ _›
  exact store_root_finishTI hp hR hMR hM hctx hMRo hco (by omega) (by omega) hvb ‹_› ‹_›
    (hA64 _ rfl) ‹_› (t := .int 64) (aop := .store64) rfl (.inr (.inr (.inr rfl))) (by decide) (cond_store ‹_› rfl)
    (fun rd amv am h => by rw [ofV_store64', h]; rfl) hA (store64_helper_ok hp ctx hco (by omega) hH) hS

set_option maxHeartbeats 2000000 in
include hp in
theorem istore8_okTI (hR : Refines F isem) (hMR : MRStable F MR) (hM : MemRefinesR Rd F sb syms isem) :
    MemRuleOkRTX Rd F sb syms isem MR env cp p rule_lower_2722 := by
  intro f ctx hctxT hMRo ii info inst hi hic hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hic
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  mem_inv hp [] at hmatch heval
  mem_rootTI hctx hi hic
  mem_vregsT hctx
  obtain rfl := store_op_of (k := 33) (cop := .istore8) rfl (by assumption)
  have hA := ‹ApplyInternal _ _ _ _ 89 574 _ _ _ _›
  have hH := ‹ApplyInternal _ _ _ _ 46 541 _ _ _ _›
  have hS := ‹ApplyInternal _ _ _ _ 25 243 _ _ _ _›
  exact store_root_finishTI hp hR hMR hM hctx hMRo hco (by omega) (by omega) hvb ‹_› ‹_›
    (hA64 _ rfl) ‹_› (t := .int 8) (aop := .store8) rfl (.inl rfl) (by decide) (fun _ _ _ _ => rfl)
    (fun rd amv am h => by rw [ofV_store8', h]; rfl) hA (store8_helper_ok hp ctx hco (by omega) hH) hS

set_option maxHeartbeats 2000000 in
include hp in
theorem istore16_okTI (hR : Refines F isem) (hMR : MRStable F MR) (hM : MemRefinesR Rd F sb syms isem) :
    MemRuleOkRTX Rd F sb syms isem MR env cp p rule_lower_2726 := by
  intro f ctx hctxT hMRo ii info inst hi hic hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hic
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  mem_inv hp [] at hmatch heval
  mem_rootTI hctx hi hic
  mem_vregsT hctx
  obtain rfl := store_op_of (k := 36) (cop := .istore16) rfl (by assumption)
  have hA := ‹ApplyInternal _ _ _ _ 89 574 _ _ _ _›
  have hH := ‹ApplyInternal _ _ _ _ 46 542 _ _ _ _›
  have hS := ‹ApplyInternal _ _ _ _ 25 243 _ _ _ _›
  exact store_root_finishTI hp hR hMR hM hctx hMRo hco (by omega) (by omega) hvb ‹_› ‹_›
    (hA64 _ rfl) ‹_› (t := .int 16) (aop := .store16) rfl (.inr (.inl rfl)) (by decide) (fun _ _ _ _ => rfl)
    (fun rd amv am h => by rw [ofV_store16', h]; rfl) hA (store16_helper_ok hp ctx hco (by omega) hH) hS

set_option maxHeartbeats 2000000 in
include hp in
theorem istore32_okTI (hR : Refines F isem) (hMR : MRStable F MR) (hM : MemRefinesR Rd F sb syms isem) :
    MemRuleOkRTX Rd F sb syms isem MR env cp p rule_lower_2730 := by
  intro f ctx hctxT hMRo ii info inst hi hic hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hic
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  mem_inv hp [] at hmatch heval
  mem_rootTI hctx hi hic
  mem_vregsT hctx
  obtain rfl := store_op_of (k := 39) (cop := .istore32) rfl (by assumption)
  have hA := ‹ApplyInternal _ _ _ _ 89 574 _ _ _ _›
  have hH := ‹ApplyInternal _ _ _ _ 46 543 _ _ _ _›
  have hS := ‹ApplyInternal _ _ _ _ 25 243 _ _ _ _›
  exact store_root_finishTI hp hR hMR hM hctx hMRo hco (by omega) (by omega) hvb ‹_› ‹_›
    (hA64 _ rfl) ‹_› (t := .int 32) (aop := .store32) rfl (.inr (.inr (.inl rfl))) (by decide) (fun _ _ _ _ => rfl)
    (fun rd amv am h => by rw [ofV_store32', h]; rfl) hA (store32_helper_ok hp ctx hco (by omega) hH) hS

set_option maxHeartbeats 2000000 in
include hp in
/-- **`stack_addr`** (`lower.isle:2849`, rule id 1093). -/
theorem stack_addr_okTI (hMR : MRStable F MR) (hM : MemRefinesR Rd F sb syms isem) :
    MemRuleOkRTX Rd F sb syms isem MR env cp p rule_lower_2849 := by
  intro f ctx hctxT hMRo ii info inst hi hic hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hic
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  mem_inv hp [] at hmatch heval
  mem_rootTI hctx hi hic
  have hC := ‹ApplyInternal _ _ _ _ 27 643 _ _ _ _›
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  obtain ⟨base, hbase, rfl, hs3⟩ := compute_stack_addr_ok hp ctx hco (by omega) hC
  obtain ⟨rfl, hs'⟩ := output_reg_inv hp ctx hco (by omega) hO
  simp only at hs'
  rw [hs3] at hs'
  subst hs'
  refine ⟨_, ?_, _, rfl, (stackAddr_lower_okTI hMR hM hctx hMRo hbase
    (width_stackAddr hRE (by assumption) (by assumption))).toR⟩
  rw [fresh_fst]
  exact (frag_one _ (.loadAddr (.vreg _ .int) (.slotOffset _)) rfl).emitted

set_option maxHeartbeats 2000000 in
include hp in
/-- **`symbol_value`** (`lower.isle:2491`, rule id 1027). -/
theorem symbol_value_okTI (hR : Refines F isem) (hMR : MRStable F MR)
    (hM : MemRefinesR Rd F sb syms isem) : MemRuleOkRTX Rd F sb syms isem MR env cp p rule_lower_2491 := by
  intro f ctx hctxT hMRo ii info inst hi hic hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hic
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  mem_inv hp [] at hmatch heval
  mem_rootTI hctx hi hic
  have hL := ‹ApplyInternal _ _ _ _ 27 570 _ _ _ _›
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  obtain ⟨ms, d, rfl, hsym⟩ := load_ext_name_ok hp ctx hco hR hM (by omega) hL
  obtain ⟨rfl, hs'⟩ := output_reg_inv hp ctx hco (by omega) hO
  simp only at hs'
  subst hs'
  exact ⟨ms, hsym.frag.emitted, _, rfl, (symbol_lower_ok hMR hMRo hsym ‹_›).toR⟩

include hp in
/-- **`uextend_load`** (rule id 815): never matches (`is_sinkable_inst` fails). -/
theorem uextend_load_okTI : MemRuleOkRTX Rd F sb syms isem MR env cp p rule_lower_1300 := by
  intro f ctx hctxT hMRo ii info inst hi hic hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hic
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  mem_inv hp [ctor_is_sinkable_inst] at hmatch

include hp in
/-- **`sextend_load`** (rule id 824): never matches (`is_sinkable_inst` fails). -/
theorem sextend_load_okTI : MemRuleOkRTX Rd F sb syms isem MR env cp p rule_lower_1359 := by
  intro f ctx hctxT hMRo ii info inst hi hic hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hic
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  mem_inv hp [ctor_is_sinkable_inst] at hmatch

end Backend.Proof
