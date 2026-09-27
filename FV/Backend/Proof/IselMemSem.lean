import FV.Backend.Proof.IselMemHelpers

/-!
# Memory family (M4Mem2): `LowerInstOk` of the memory instructions

The CLIF side (`evalInst` of `load`/`store`/`stack_addr`/`symbol_value` inverted), the run-time
context `RtOk` from the per-instruction premises and `MemRelOk`, and the four builders the root
rules end in: a load through an `AmOk` mode (`load_lower_ok`), a store (`store_lower_ok`), a
stack-slot address (`stackAddr_lower_ok`) and a symbol address (`symbol_lower_ok`).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-! ## CLIF side -/

theorem res_bind_eq_ok {α β : Type} {x : Clif.Res α} {f : α → Clif.Res β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | ok a => exact ⟨a, rfl, h⟩
  | trap c => cases h
  | stuck m => cases h

theorem res_check_ok {c : Bool} {msg : String} {u : Unit} (h : Clif.Res.check c msg = .ok u) :
    c = true := by
  cases c
  · cases h
  · rfl

theorem res_ofOption_ok {α : Type} {msg : String} {o : Option α} {a : α}
    (h : Clif.Res.ofOption msg o = .ok a) : o = some a := by
  cases o with
  | none => cases h
  | some b => cases h; rfl

theorem get_regs {fr : Clif.Frame} {x : Nat} {v : Clif.Val} (h : fr.get x = .ok v) :
    fr.regs x = some v := get_ok h

theorem checkAccess_ok {m : Clif.Mem} {fl : Clif.MemFlags} {a n : Nat} {u : Unit}
    (h : m.checkAccess fl a n = .ok u) : m.valid a n = true := by
  unfold Clif.Mem.checkAccess at h
  split at h
  · assumption
  · split at h <;> cases h

theorem big_false {fl : Clif.MemFlags} (h : fl.endianness ≠ some .big) :
    (fl.endianness == some .big) = false := by
  simpa using h

theorem evalInst_load_inv {fr : Clif.Frame} {cm cm' : Clif.Mem} {op : Clif.LoadOp} {ty : Clif.Ty}
    {fl : Clif.MemFlags} {p : Nat} {off : Int} {vals : List Clif.Val}
    (hfl : fl.endianness ≠ some .big)
    (h : Clif.evalInst fr cm (.load op ty fl p off) = .ok (vals, cm')) :
    ∃ pv raw, fr.regs p = some pv ∧ op.size ty ≤ ty.bytes ∧
      cm.valid (Clif.effAddr pv off) (op.size ty) = true ∧
      cm.readBits false (Clif.effAddr pv off) (op.size ty) (8 * op.size ty) = some raw ∧
      vals = [⟨ty, if op.signed then raw.signExtend ty.width else raw.zeroExtend ty.width⟩] ∧
      cm' = cm := by
  simp only [Clif.evalInst] at h
  obtain ⟨pv, hpv, h⟩ := res_bind_eq_ok h
  obtain ⟨_, hck, h⟩ := res_bind_eq_ok h
  obtain ⟨raw, hl, h⟩ := res_bind_eq_ok h
  simp only [Clif.Res.pure_eq, Clif.Res.ok.injEq, Prod.mk.injEq] at h
  unfold Clif.Mem.load at hl
  obtain ⟨_, hca, hl⟩ := res_bind_eq_ok hl
  rw [big_false hfl] at hl
  exact ⟨pv, raw, get_regs hpv, by simpa using res_check_ok hck, checkAccess_ok hca,
    res_ofOption_ok hl, h.1.symm, h.2.symm⟩

theorem evalInst_store_inv {fr : Clif.Frame} {cm cm' : Clif.Mem} {op : Clif.StoreOp}
    {ty : Clif.Ty} {fl : Clif.MemFlags} {x p : Nat} {off : Int} {vals : List Clif.Val}
    (hfl : fl.endianness ≠ some .big)
    (h : Clif.evalInst fr cm (.store op ty fl x p off) = .ok (vals, cm')) :
    ∃ a pv, fr.getAs x ty = .ok a ∧ fr.regs p = some pv ∧ op.size ty ≤ ty.bytes ∧
      cm.valid (Clif.effAddr pv off) (op.size ty) = true ∧ vals = [] ∧
      cm' = cm.writeBits false (Clif.effAddr pv off) (op.size ty) a := by
  simp only [Clif.evalInst] at h
  obtain ⟨a, ha, h⟩ := res_bind_eq_ok h
  obtain ⟨pv, hpv, h⟩ := res_bind_eq_ok h
  obtain ⟨_, hck, h⟩ := res_bind_eq_ok h
  obtain ⟨m', hs, h⟩ := res_bind_eq_ok h
  simp only [Clif.Res.pure_eq, Clif.Res.ok.injEq, Prod.mk.injEq] at h
  unfold Clif.Mem.store at hs
  obtain ⟨_, hca, hs⟩ := res_bind_eq_ok hs
  obtain ⟨_, -, hs⟩ := res_bind_eq_ok hs
  rw [big_false hfl] at hs
  simp only [Clif.Res.pure_eq, Clif.Res.ok.injEq] at hs
  exact ⟨a, pv, ha, get_regs hpv, by simpa using res_check_ok hck, checkAccess_ok hca, h.1.symm,
    h.2.symm.trans hs.symm⟩

theorem valid_sub {m : Clif.Mem} {a n i : Nat} (h : m.valid a n = true) (hi : i < n) :
    m.valid (a + i) 1 = true := by
  unfold Clif.Mem.valid at h ⊢
  rw [List.any_eq_true] at h ⊢
  obtain ⟨al, hal, hc⟩ := h
  refine ⟨al, hal, ?_⟩
  simp only [Clif.Alloc.contains, Bool.and_eq_true, decide_eq_true_eq] at hc ⊢
  omega

theorem effAddr_ofInt (pv : Clif.Val) (off : Int) :
    BitVec.ofInt 64 (pv.toNat + off) = BitVec.ofNat 64 (Clif.effAddr pv off) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt, BitVec.toNat_ofNat, Clif.effAddr]
  omega

theorem pv_i64 {ctx : Ctx} {fr : Clif.Frame} (hdfg : DFGCons ctx fr) {p : Nat} {pv : Clif.Val}
    (hp64 : ctx.valueType? p = some (.int 64)) (hpv : fr.regs p = some pv) : pv.ty = .i64 := by
  have := hdfg.2 p _ pv hp64 hpv
  rw [ofClif_int_width] at this
  injection this with h
  exact ty_i64_of_width h

/-! ## Arm side -/

theorem getLsbD_ofX (x : BitVec 64) (i : Nat) : (ofX x).getLsbD i = (decide (i < 64) && x.getLsbD i) := by
  simp only [ofX, BitVec.getLsbD_setWidth]
  by_cases hi : i < 64
  · simp [hi, show i < 128 by omega]
  · simp [hi, BitVec.getLsbD_of_ge x i (by omega)]

/-- The register a load leaves holds the CLIF load's value. -/
theorem load_holds {n m : Nat} (hnm : m = n) {raw : BitVec (8 * n)} {R : BitVec (m * 8)}
    (hbits : ∀ j, raw.getLsbD j = R.getLsbD j) {ty : Clif.Ty} (hw : ty.width ≤ 64)
    (hn : 8 * n ≤ ty.width) (hn0 : 0 < n) (sg : Bool) :
    VHolds ⟨ty, if sg then raw.signExtend ty.width else raw.zeroExtend ty.width⟩
      (ofX (if sg then R.signExtend 64 else R.setWidth 64)) := by
  simp only [VHolds]
  have hmsb : raw.msb = R.msb := by
    rw [BitVec.msb_eq_getLsbD_last, BitVec.msb_eq_getLsbD_last, hbits]
    congr 1; omega
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  cases sg
  · simp only [Bool.false_eq_true, ite_false, BitVec.getLsbD_setWidth, getLsbD_ofX,
      BitVec.zeroExtend_eq_setWidth, hbits]
    have : i < 64 := by omega
    simp [hi, this]
  · simp only [ite_true, BitVec.getLsbD_setWidth, getLsbD_ofX, BitVec.getLsbD_signExtend, hbits,
      hmsb]
    have : i < 64 := by omega
    simp only [hi, this, decide_true, Bool.true_and]
    by_cases h8 : i < 8 * n
    · simp [h8, show i < m * 8 by omega]
    · simp [h8, show ¬ i < m * 8 by omega]

/-! ## The run-time context -/

theorem rtOk_of {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {F : BitVec 64 → Prop}
    {sb : Nat} {syms : String → Option Nat} {MR : MemRelT} (hMRo : MemRelOk F sb syms f MR)
    {fr : Clif.Frame} {cm : Clif.Mem} {ρ : Nat → CV} {w : Arm.ArmState} (hf : fr.func = ctx.func)
    (hv : ValsHeld fr ρ) (hdfg : DFGCons ctx fr) (hmr : MR fr.slots cm w) :
    RtOk ctx sb fr ρ w := by
  refine ⟨hf, hv, hdfg, fun id b hb => ?_⟩
  obtain ⟨off, ho, hb'⟩ := hMRo.slots _ _ _ id b hmr hb
  exact ⟨off, by rw [hctx.slotOff]; exact ho, hb'⟩

theorem frag_emit0 (st : LState) (m : MInst) (hd : vdefs m = []) : Frag st (st.emit m) [m] := by
  refine ⟨by simp [LState.emit], by simp [LState.emit], ?_⟩
  intro m' hm d hd'
  simp only [List.mem_singleton] at hm; subst hm
  rw [hd] at hd'; simp at hd'

/-! ## The builders -/

section Builders
variable {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat} {isem : Sem}
  {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} {f : Clif.Function} {ctx : Ctx}

theorem instOutcome_load (fr : Clif.Frame) (cm : Clif.Mem) (op : Clif.LoadOp) (ty : Clif.Ty)
    (fl : Clif.MemFlags) (p : Nat) (off : Int) :
    instOutcome env cp fr cm (.load op ty fl p off) = Clif.evalInst fr cm (.load op ty fl p off) :=
  rfl

theorem instOutcome_store (fr : Clif.Frame) (cm : Clif.Mem) (op : Clif.StoreOp) (ty : Clif.Ty)
    (fl : Clif.MemFlags) (x p : Nat) (off : Int) :
    instOutcome env cp fr cm (.store op ty fl x p off) =
      Clif.evalInst fr cm (.store op ty fl x p off) := rfl

theorem instOutcome_stackAddr (fr : Clif.Frame) (cm : Clif.Mem) (ty : Clif.Ty) (sl : Nat)
    (o : Int) : instOutcome env cp fr cm (.stackAddr ty sl o) = Clif.evalInst fr cm (.stackAddr ty sl o) :=
  rfl

theorem instOutcome_symbolValue (fr : Clif.Frame) (cm : Clif.Mem) (ty : Clif.Ty) (gv : Nat) :
    instOutcome env cp fr cm (.symbolValue ty gv) = Clif.evalInst fr cm (.symbolValue ty gv) := rfl

/-- **A load through an addressing mode** (`AmOk`): the mode's code, then `ldr` into a fresh
register. -/
theorem load_lower_ok (hMR : MRStable F MR) (hM : MemRefines F sb syms isem)
    (hctx : CtxInv f ctx) (hMRo : MemRelOk F sb syms f MR) {st st2 : LState} {ms : List MInst}
    {am : AMode} {aop : LoadOp} {op : Clif.LoadOp} {ty : Clif.Ty} {fl : Clif.MemFlags} {p : Nat}
    {off : Int} {results : List Nat}
    (hok : AmOk F isem sb ctx st st2 ms am aop.bytes p off) (haop : aop ≠ .fpuLoad128)
    (hsz : aop.bytes = op.size ty) (hsg : loadSigned aop = op.signed) (hw : ty.width ≤ 64)
    (hfl : fl.endianness ≠ some .big) (hp64 : ctx.valueType? p = some (.int 64)) :
    LowerInstOk isem MR env cp ctx (.load op ty fl p off) results st [[(st2.fresh .int).1]]
      ((st2.fresh .int).2.emit (.load aop (st2.fresh .int).1 am fl))
      (ms ++ [.load aop (st2.fresh .int).1 am fl]) := by
  rw [fresh_fst]
  have hops := load_ops aop st2.nextVreg hok.vregs fl
  have hfr := hok.frag.append (frag_one st2 _ hops.defs)
  refine ⟨hfr.mono, hfr.defs, ?_⟩
  intro fr cm ρ w hf hv hdfg hmr
  rw [instOutcome_load]
  cases he : Clif.evalInst fr cm (.load op ty fl p off) with
  | trap c => intro h; simp [explicitTrapInst] at h
  | stuck _ => trivial
  | ok r =>
  obtain ⟨vals, cm'⟩ := r
  obtain ⟨pv, raw, hpv, hle, hvalid, hread, rfl, rfl⟩ := evalInst_load_inv hfl he
  dsimp only
  have hrt := rtOk_of hctx hMRo hf hv hdfg hmr
  obtain ⟨hU, hAv, ρ1, w1, hr1, hw1, haddr⟩ := hok.run fr ρ w pv hrt hpv (pv_i64 hdfg hp64 hpv)
  have hmr1 := hMR _ _ _ _ hw1 hmr
  rw [effAddr_ofInt] at haddr
  generalize Clif.effAddr pv off = A at haddr hvalid hread
  obtain ⟨hA64, hF⟩ := hMRo.valid _ _ _ _ _ hmr1 hvalid
  have havoid : Avoids F aop.bytes (BitVec.ofNat 64 A) := by
    intro k hk
    rw [← BitVec.ofNat_add]
    exact hF k (by omega)
  obtain ⟨w2, hs, hsw⟩ := hM.1 aop st2.nextVreg am fl _ w1 _ haop haddr havoid
  obtain ⟨ops, hopsE, hvu, hlen, hupd⟩ := hops.ops
  rw [← hvu] at hs
  have hr2 := seqRun_isem_one hopsE hs (by rw [hlen]; rfl)
  refine ⟨?_, _, w2, seqRun_append_fall' isem hr1 hr2, .inr ⟨rfl, ?_⟩,
    hMR _ _ _ _ hsw.toNF hmr1⟩
  · refine UsesLo.append hU fun m hm u hu => ?_
    simp only [List.mem_singleton] at hm; subst hm
    rw [hops.uses] at hu
    exact hAv u hu
  · intro j rs v hrs hv'
    cases j with
    | succ j => simp at hrs
    | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hrs hv'
    subst hrs hv'
    refine ⟨st2.nextVreg, .int, rfl, .inl hok.frag.mono, ?_⟩
    rw [hupd, upd_same]
    have hbits := readBits_getLsbD_eq (s := w1) hread (by omega)
      (fun i hi b hb => hMRo.bytes _ _ _ _ b hmr1 (valid_sub hvalid hi) hb)
    have hn0 : 0 < op.size ty := by
      rw [← hsz]; cases aop <;> simp [LoadOp.bytes] at haop ⊢
    have hle' : 8 * op.size ty ≤ ty.width := by
      have : ty.bytes * 8 = ty.width := by cases ty <;> rfl
      omega
    have hbits' : ∀ j, raw.getLsbD j =
        (Arm.read_mem_bytes aop.bytes (BitVec.ofNat 64 A) w1).getLsbD j := by
      rw [hsz]; exact hbits
    simp only [loadVal]
    rw [hsg]
    exact load_holds hsz hbits' hw hle' hn0 op.signed

theorem store_setWidth {ty : Clif.Ty} {a : BitVec ty.width} {c : CV} (hh : VHolds ⟨ty, a⟩ c) {n : Nat}
    (hn : n * 8 ≤ ty.width) (hw : ty.width ≤ 64) :
    a.setWidth (n * 8) = (lo64 c).setWidth (n * 8) := by
  simp only [VHolds] at hh
  rw [← hh, BitVec.setWidth_setWidth_of_le _ hn, lo64, BitVec.setWidth_setWidth_of_le _ (by omega)]

/-- **A store through an addressing mode** (`AmOk`): the mode's code, then `str` of the value's
register. -/
theorem store_lower_ok (hMR : MRStable F MR) (hM : MemRefines F sb syms isem)
    (hctx : CtxInv f ctx) (hMRo : MemRelOk F sb syms f MR) {st st2 : LState} {ms : List MInst}
    {am : AMode} {aop : StoreOp} {op : Clif.StoreOp} {ty : Clif.Ty} {fl : Clif.MemFlags}
    {x p : Nat} {off : Int} {results : List Nat}
    (hok : AmOk F isem sb ctx st st2 ms am aop.bytes p off) (haop : aop ≠ .fpuStore128)
    (hsz : ∀ (fr : Clif.Frame) (a : BitVec ty.width), DFGCons ctx fr → fr.getAs x ty = .ok a →
      aop.bytes = op.size ty) (hw : ty.width ≤ 64)
    (hfl : fl.endianness ≠ some .big) (hp64 : ctx.valueType? p = some (.int 64))
    (hx : x < st.nextVreg) :
    LowerInstOk isem MR env cp ctx (.store op ty fl x p off) results st []
      (st2.emit (.store aop (.vreg x .int) am fl)) (ms ++ [.store aop (.vreg x .int) am fl]) := by
  have hops := store_ops aop x hok.vregs fl
  have hfr := hok.frag.append (frag_emit0 st2 _ hops.defs)
  refine ⟨hfr.mono, hfr.defs, ?_⟩
  intro fr cm ρ w hf hv hdfg hmr
  rw [instOutcome_store]
  cases he : Clif.evalInst fr cm (.store op ty fl x p off) with
  | trap c => intro h; simp [explicitTrapInst] at h
  | stuck _ => trivial
  | ok r =>
  obtain ⟨vals, cm'⟩ := r
  obtain ⟨a, pv, hax, hpv, hle, hvalid, rfl, rfl⟩ := evalInst_store_inv hfl he
  dsimp only
  have hsz := hsz fr a hdfg hax
  have hrt := rtOk_of hctx hMRo hf hv hdfg hmr
  obtain ⟨hU, hAv, ρ1, w1, hr1, hw1, haddr⟩ := hok.run fr ρ w pv hrt hpv (pv_i64 hdfg hp64 hpv)
  have hmr1 := hMR _ _ _ _ hw1 hmr
  rw [effAddr_ofInt] at haddr
  generalize Clif.effAddr pv off = A at haddr hvalid
  rw [← hsz] at hvalid hle ⊢
  obtain ⟨hA64, hF⟩ := hMRo.valid _ _ _ _ _ hmr1 hvalid
  have havoid : Avoids F aop.bytes (BitVec.ofNat 64 A) := by
    intro k hk
    rw [← BitVec.ofNat_add]
    exact hF k (by omega)
  obtain ⟨w2, hs, hsw⟩ := hM.2.1 aop x am fl (ρ1 x) _ w1 _ haop haddr havoid
  obtain ⟨ops, hopsE, hvu, hlen, hupd⟩ := hops.ops
  rw [← hvu] at hs
  have hr2 := seqRun_isem_one hopsE hs (by rw [hlen]; rfl)
  have hxv := getAs_ok hax
  have hx1 : ρ1 x = ρ x := hok.frag.frame hr1 hx
  have hle8 : aop.bytes * 8 ≤ ty.width := by
    have : ty.bytes * 8 = ty.width := by cases ty <;> rfl
    omega
  refine ⟨?_, _, w2, seqRun_append_fall' isem hr1 hr2, .inr ⟨rfl, fun j rs v h => by simp at h⟩, ?_⟩
  · refine UsesLo.append hU fun m hm u hu => ?_
    simp only [List.mem_singleton] at hm; subst hm
    rw [hops.uses] at hu
    rcases List.mem_cons.1 hu with rfl | hu
    · exact .inr (by rw [hxv]; rfl)
    · exact hAv u hu
  · refine hMR _ _ _ _ hsw.toNF ?_
    rw [writeBits_setWidth A aop.bytes a hle8, store_setWidth (hv x _ hxv) hle8 hw, hx1]
    exact hMRo.store _ _ _ _ _ _ hmr1 hvalid

theorem evalInst_stackAddr_inv' {fr : Clif.Frame} {cm cm' : Clif.Mem} {ty : Clif.Ty} {sl : Nat}
    {o : Int} {vals : List Clif.Val} (h : Clif.evalInst fr cm (.stackAddr ty sl o) = .ok (vals, cm')) :
    ∃ b, fr.slots.lookup sl = some b ∧ vals = [Clif.Val.ofInt ty (b + o)] ∧ cm' = cm := by
  simp only [Clif.evalInst] at h
  cases hb : fr.slots.lookup sl with
  | none => rw [hb] at h; cases h
  | some b =>
    rw [hb] at h
    cases h
    exact ⟨b, rfl, rfl, rfl⟩

theorem operands_loadAddr_slot (d : Nat) (k : Int) :
    (MInst.loadAddr (.vreg d .int) (.slotOffset k)).operands = .ok #[⟨d, .int, .def, .late, .reg⟩] :=
  rfl

theorem setWidth_ofInt64 {ty : Clif.Ty} (hw : ty.width ≤ 64) (z : Int) :
    (ofX (BitVec.ofInt 64 z)).setWidth ty.width = BitVec.ofInt ty.width z := by
  apply BitVec.eq_of_toNat_eq
  cases ty <;> simp only [Clif.Ty.width] at hw ⊢ <;>
    simp only [ofX, BitVec.toNat_setWidth, BitVec.toNat_ofInt] <;> omega

/-- **`stack_addr`**: `LoadAddr` of the slot's `SlotOffset` into a fresh register. -/
theorem stackAddr_lower_ok (hMR : MRStable F MR) (hM : MemRefines F sb syms isem)
    (hctx : CtxInv f ctx) (hMRo : MemRelOk F sb syms f MR) {st : LState} {ty : Clif.Ty}
    {sl base : Nat} {o : Int} {results : List Nat} (hbase : ctx.slotOff.lookup sl = some base)
    (hw : ty.width ≤ 64) :
    LowerInstOk isem MR env cp ctx (.stackAddr ty sl o) results st [[(st.fresh .int).1]]
      ((st.fresh .int).2.emit (.loadAddr (st.fresh .int).1 (.slotOffset (base + o))))
      [.loadAddr (st.fresh .int).1 (.slotOffset (base + o))] := by
  rw [fresh_fst]
  have hfr := frag_one st (.loadAddr (.vreg st.nextVreg .int) (.slotOffset (base + o))) rfl
  refine ⟨hfr.mono, hfr.defs, ?_⟩
  intro fr cm ρ w hf hv hdfg hmr
  rw [instOutcome_stackAddr]
  cases he : Clif.evalInst fr cm (.stackAddr ty sl o) with
  | trap c => intro h; simp [explicitTrapInst] at h
  | stuck _ => trivial
  | ok r =>
  obtain ⟨vals, cm'⟩ := r
  obtain ⟨b, hb, rfl, rfl⟩ := evalInst_stackAddr_inv' he
  dsimp only
  have hrt := rtOk_of hctx hMRo hf hv hdfg hmr
  obtain ⟨base', hbase', rfl⟩ := hrt.slots sl b hb
  rw [hbase] at hbase'
  cases hbase'
  obtain ⟨w', hs, hsw⟩ := hM.2.2.1 st.nextVreg (base + o) w
  have hr := seqRun_isem_one (ρ := ρ) (operands_loadAddr_slot st.nextVreg (base + o)) hs rfl
  refine ⟨?_, _, w', hr, .inr ⟨rfl, ?_⟩, hMR _ _ _ _ hsw.toNF hmr⟩
  · intro m hm u hu
    simp only [List.mem_singleton] at hm; subst hm
    simp [vuseNums, operands_loadAddr_slot, Operand.isUse] at hu
  · intro j rs v hrs hv'
    cases j with
    | succ j => simp at hrs
    | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hrs hv'
    subst hrs hv'
    refine ⟨st.nextVreg, .int, rfl, .inl (Nat.le_refl _), ?_⟩
    have hu : ∀ x, vdefUpd #[⟨st.nextVreg, .int, .def, .late, .reg⟩] [x] ρ = upd ρ st.nextVreg x :=
      fun _ => rfl
    show ((vdefUpd _ _ ρ) st.nextVreg).setWidth ty.width = _
    rw [hu, upd_same]
    have hX : spOf w + BitVec.ofInt 64 (↑(base + o) + ↑sb) =
        BitVec.ofInt 64 (↑((spOf w).toNat + sb + base) + o) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofInt]
      have := (spOf w).isLt
      omega
    rw [hX, setWidth_ofInt64 hw]
    rfl

theorem evalInst_symbolValue_inv {fr : Clif.Frame} {cm cm' : Clif.Mem} {ty : Clif.Ty} {gv : Nat}
    {vals : List Clif.Val} (h : Clif.evalInst fr cm (.symbolValue ty gv) = .ok (vals, cm')) :
    ∃ name o col base, fr.func.globals.lookup gv = some (.symbol name o col) ∧
      cm.symbols name = some base ∧ vals = [Clif.Val.ofInt ty (base + o)] ∧ cm' = cm := by
  simp only [Clif.evalInst] at h
  obtain ⟨g, hg, h⟩ := res_bind_eq_ok h
  cases g with
  | symbol name o col =>
    obtain ⟨base, hb, h⟩ := res_bind_eq_ok h
    simp only [Clif.Res.pure_eq, Clif.Res.ok.injEq, Prod.mk.injEq] at h
    exact ⟨name, o, col, base, res_ofOption_ok hg, res_ofOption_ok hb, h.1.symm, h.2.symm⟩
  | _ => cases h

/-- **`symbol_value`** through `load_ext_name` (`SymOk`). -/
theorem symbol_lower_ok (hMR : MRStable F MR) (hMRo : MemRelOk F sb syms f MR)
    {st st' : LState} {ms : List MInst} {d gv : Nat} {name : String} {o : Int} {col : Bool}
    {results : List Nat} (hsym : SymOk F isem syms st st' ms d name o)
    (hg : ctx.func.globals.lookup gv = some (.symbol name o col)) :
    LowerInstOk isem MR env cp ctx (.symbolValue .i64 gv) results st [[.vreg d .int]] st' ms := by
  refine ⟨hsym.frag.mono, hsym.frag.defs, ?_⟩
  intro fr cm ρ w hf hv hdfg hmr
  rw [instOutcome_symbolValue]
  cases he : Clif.evalInst fr cm (.symbolValue .i64 gv) with
  | trap c => intro h; simp [explicitTrapInst] at h
  | stuck _ => trivial
  | ok r =>
  obtain ⟨vals, cm'⟩ := r
  obtain ⟨name', o', col', base, hg', hb, rfl, rfl⟩ := evalInst_symbolValue_inv he
  dsimp only
  rw [hf, hg] at hg'
  cases hg'
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
  rw [hd]
  exact (addr_nat_off _ _).symm

end Builders

end Backend.Proof
