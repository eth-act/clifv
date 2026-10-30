import FV.Backend.Proof.IselMemSem
import FV.Backend.Proof.IselFloatMem

/-!
# `IselMemSem` over typed contexts (S11e5 Stage C, slice 7)

The `CtxInv` proofs of `IselMemSem`, restated over float-capable contexts (`CtxT`, `LowerRuleOkTI`):
the values whose registers they use are in integer positions (`CtxInvT.valueRegI`, `int_posA`).
-/

namespace Backend.Proof
open Backend Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
section Builders
variable {Rd : BitVec 64 → Prop} {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
  {isem : Sem}
  {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} {f : Clif.Function} {ctx : Ctx}
/-- **A load through an addressing mode** (`AmOk`): the mode's code, then `ldr` into a fresh
register. -/
theorem load_lower_okTI (hMR : MRStable F MR) (hM : MemRefinesR Rd F sb syms isem)
    (hctx : CtxInvT f ctx) (hMRo : MemRelOk F sb syms f MR) {st st2 : LState} {ms : List MInst}
    {am : AMode} {aop : LoadOp} {op : Clif.LoadOp} {ty : Clif.Ty} {fl : Clif.MemFlags} {p : Nat}
    {off : Int} {results : List Nat}
    (hok : AmOk F isem sb ctx st st2 ms am aop.bytes p off) (haop : aop ≠ .fpuLoad128)
    (hsz : aop.bytes = op.size ty) (hsg : loadSigned aop = op.signed) (hw : ty.width ≤ 64)
    (hfl : fl.endianness ≠ some .big) (hp64 : ctx.valueType? p = some (.int 64)) :
    LowerInstOkR Rd isem MR env cp ctx (.load op ty fl p off) results st [[(st2.fresh .int).1]]
      ((st2.fresh .int).2.emit (.load aop (st2.fresh .int).1 am fl))
      (ms ++ [.load aop (st2.fresh .int).1 am fl]) := by
  rw [fresh_fst]
  have hops := load_ops aop st2.nextVreg hok.vregs fl
  have hfr := hok.frag.append (frag_one st2 _ hops.defs)
  refine ⟨hfr.mono, hfr.defs, ?_⟩
  intro fr cm ρ w hf hv hdfg hmr hRd
  rw [instOutcome_load]
  cases he : Clif.evalInst fr cm (.load op ty fl p off) with
  | trap c => intro h; simp [explicitTrapInst] at h
  | stuck _ => trivial
  | ok r =>
  obtain ⟨vals, cm'⟩ := r
  obtain ⟨pv, raw, hpv, hle, hvalid, hread, rfl, rfl⟩ := evalInst_load_inv hfl he
  dsimp only
  have hrt := rtOk_ofT hctx hMRo hf hv hdfg hmr
  obtain ⟨hU, hAv, ρ1, w1, hr1, hw1, haddr⟩ := hok.run fr ρ w pv hrt hpv (pv_i64 hdfg hp64 hpv)
  have hmr1 := hMR _ _ _ _ hw1 hmr
  rw [effAddr_ofInt] at haddr
  generalize Clif.effAddr pv off = A at haddr hvalid hread
  obtain ⟨hA64, hF⟩ := hMRo.valid _ _ _ _ _ hmr1 hvalid
  have havoid : Avoids F aop.bytes (BitVec.ofNat 64 A) := by
    intro k hk
    rw [← BitVec.ofNat_add]
    exact hF k (by omega)
  have hrd : ∀ k < aop.bytes, Rd (BitVec.ofNat 64 A + BitVec.ofNat 64 k) := by
    intro k hk
    rw [← BitVec.ofNat_add]
    have hk' : k < op.size ty := by rw [← hsz]; exact hk
    exact hRd _ (valid_sub hvalid hk') ((readBits_spec hread).1 k hk')
  obtain ⟨w2, hs, hsw⟩ := hM.1 aop st2.nextVreg am fl _ w1 _ haop haddr havoid hrd
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

/-- **A store through an addressing mode** (`AmOk`): the mode's code, then `str` of the value's
register. -/
theorem store_lower_okTI (hMR : MRStable F MR) (hM : MemRefinesR Rd F sb syms isem)
    (hctx : CtxInvT f ctx) (hMRo : MemRelOk F sb syms f MR) {st st2 : LState} {ms : List MInst}
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
  have hrt := rtOk_ofT hctx hMRo hf hv hdfg hmr
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

/-- **`stack_addr`**: `LoadAddr` of the slot's `SlotOffset` into a fresh register. -/
theorem stackAddr_lower_okTI (hMR : MRStable F MR) (hM : MemRefinesR Rd F sb syms isem)
    (hctx : CtxInvT f ctx) (hMRo : MemRelOk F sb syms f MR) {st : LState} {ty : Clif.Ty}
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
  have hrt := rtOk_ofT hctx hMRo hf hv hdfg hmr
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

end Builders
end Backend.Proof
