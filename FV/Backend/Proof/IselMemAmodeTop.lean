import FV.Backend.Proof.IselMemNoIconst

/-!
# Memory family (M4Mem2): `amode`

The contract of `amode ty x off` (`inst.isle:4036`, 4 rules): `stack_addr` look-through to a
`SlotOffset` mode (the slot at `sp + sb + off(slot)`, `RtOk.slots`), an `iconst` operand of an
`iadd` folded into the offset, and `amode_no_more_iconst` (`amode_nmi_ok`).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

theorem ctor_i32_to_offset32' (ctx : Ctx) (st : LState) (i : Int) (v : V) (st' : LState) :
    externCtor ctx T.i32_to_offset32 [.int i] st = .ok (v, st') ↔ v = .int i ∧ st' = st := by
  have : externCtor ctx T.i32_to_offset32 [.int i] st = .ok (.int i, st) := rfl
  rw [this]; simp [eq_comm]

section Values

theorem iconst_regs {ctx : Ctx} {fr : Clif.Frame} (hdfg : DFGCons ctx fr) {b : Nat} {ty : Clif.Ty}
    {c : BitVec ty.width} (hdc : ctx.defClif? b = some (.iconst ty c)) {bv : Clif.Val}
    (hb : fr.regs b = some bv) : bv = ⟨ty, c⟩ := by
  obtain ⟨j, info, hj, hij, hcl⟩ := defClif_inv hdc
  exact dfg_single hdfg hj hij hcl rfl hb (fun vals cm cm' h => by rw [evalInst_iconst] at h; cases h; rfl)

theorem evalInst_stackAddr_inv {fr : Clif.Frame} {cm cm' : Clif.Mem} {ty : Clif.Ty} {sl : Nat}
    {o : Int} {vals : List Clif.Val} (h : Clif.evalInst fr cm (.stackAddr ty sl o) = .ok (vals, cm')) :
    ∃ b, fr.slots.lookup sl = some b ∧ vals = [Clif.Val.ofInt ty (b + o)] := by
  simp only [Clif.evalInst] at h
  cases hb : fr.slots.lookup sl with
  | none => rw [hb] at h; cases h
  | some b =>
    rw [hb] at h
    cases h
    exact ⟨b, rfl, rfl⟩

theorem ofInt_sextFrom64 (i : Int) : BitVec.ofInt 64 (sextFrom 64 i) = BitVec.ofInt 64 i := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt, sextFrom]
  split <;> omega

/-- The `i32_from_iconst` operand of an `i64` `iadd`, as the 64-bit value it folds in. -/
theorem iconst_fold {ctx : Ctx} {fr : Clif.Frame} (hdfg : DFGCons ctx fr) {b : Nat} {ty : Clif.Ty}
    {c : BitVec ty.width} (hdc : ctx.defClif? b = some (.iconst ty c)) {bv : Clif.Val}
    (hb : fr.regs b = some bv) (ht : bv.ty = .i64) :
    BitVec.ofInt 64 (sextFrom ty.width (imm64OfIconst ty c)) = BitVec.ofNat 64 bv.toNat := by
  have := iconst_regs hdfg hdc hb
  subst this
  simp only at ht
  subst ht
  show BitVec.ofInt 64 (sextFrom 64 c.toInt) = BitVec.ofNat 64 c.toNat
  rw [ofInt_sextFrom64]
  have e : ∀ c : BitVec 64, BitVec.ofInt 64 c.toInt = BitVec.ofNat 64 c.toNat := by
    intro c; rw [ofNat_toNat64]; exact BitVec.ofInt_toInt
  exact e c

end Values

section Build
variable {F : BitVec 64 → Prop} {isem : Sem} {sb : Nat} {ctx : Ctx}

/-- An addressing mode for `a + off'` is one for `x + off` when these are equal. -/
theorem amOk_rebase {st st' : LState} {ms : List MInst} {am : AMode} {bytes x a : Nat}
    {off off' : Int} (h : AmOk F isem sb ctx st st' ms am bytes a off')
    (hv : ∀ fr ρ w pv, RtOk ctx sb fr ρ w → fr.regs x = some pv → pv.ty = .i64 →
      ∃ av, fr.regs a = some av ∧ av.ty = .i64 ∧
        BitVec.ofInt 64 (av.toNat + off') = BitVec.ofInt 64 (pv.toNat + off)) :
    AmOk F isem sb ctx st st' ms am bytes x off := by
  refine ⟨h.frag, h.vregs, fun fr ρ w pv hrt hx ht => ?_⟩
  obtain ⟨av, ha, hat, he⟩ := hv fr ρ w pv hrt hx ht
  obtain ⟨h1, h2, h3⟩ := h.run fr ρ w av hrt ha hat
  exact ⟨h1, h2, h3.imp fun ρ' w' _ e => e.trans (congrArg some he)⟩

/-- `iadd a (iconst c)` / `iadd (iconst c) a`: the constant folded into the offset. -/
theorem fold_val {x a b : Nat} {ty ty3 : Clif.Ty} {c : BitVec ty3.width} {off : Int} (left : Bool)
    (hdc : ctx.defClif? x = some (.binary .iadd ty (if left then b else a) (if left then a else b)))
    (hdb : ctx.defClif? b = some (.iconst ty3 c)) :
    ∀ fr ρ w pv, RtOk ctx sb fr ρ w → fr.regs x = some pv → pv.ty = .i64 →
      ∃ av, fr.regs a = some av ∧ av.ty = .i64 ∧
        BitVec.ofInt 64 (av.toNat + (sextFrom ty3.width (imm64OfIconst ty3 c) + off)) =
          BitVec.ofInt 64 (pv.toNat + off) := by
  intro fr ρ w pv hrt hx ht
  obtain ⟨u, v, hu, hv, hut, hvt, hpv⟩ := iadd_val hrt.dfg hdc hx ht
  cases left
  · simp only [Bool.false_eq_true, ite_false] at hu hv
    refine ⟨u, hu, hut, ?_⟩
    rw [hpv, addr_arith, ofInt_add64, ofInt_add64, ofInt_nat64, iconst_fold hrt.dfg hdb hv hvt]
    ac_rfl
  · simp only [ite_true] at hu hv
    refine ⟨v, hv, hvt, ?_⟩
    rw [hpv, addr_arith, ofInt_add64, ofInt_add64, ofInt_nat64, iconst_fold hrt.dfg hdb hu hut]
    ac_rfl

/-- `stack_addr slot o1` looked through: the slot-offset mode. -/
theorem amOk_slot {st : LState} {x sl base bytes : Nat} {ty : Clif.Ty} {o1 off : Int}
    (hdc : ctx.defClif? x = some (.stackAddr ty sl o1)) (hbase : ctx.slotOff.lookup sl = some base) :
    AmOk F isem sb ctx st st [] (.slotOffset (base + o1 + off)) bytes x off := by
  refine ⟨Frag.nil st, fun r hr => by simp [AMode.regs] at hr, fun fr ρ w pv hrt hx ht => ?_⟩
  refine ⟨UsesLo.nil _ _, fun u hu => by simp [amVregs, AMode.regs] at hu, Runs.nil ?_⟩
  obtain ⟨j, info, hj, hij, hcl⟩ := defClif_inv hdc
  obtain ⟨vals, hev, hl⟩ := hrt.dfg.1 x j info _ pv hj hij hcl rfl hx
  obtain ⟨b, hb, rfl⟩ := evalInst_stackAddr_inv (hev default)
  have hpv := lookup_zip_single hl
  subst hpv
  simp only [Clif.Val.ofInt] at ht
  subst ht
  obtain ⟨base', hbase', hbv⟩ := hrt.slots sl b hb
  rw [hbase] at hbase'
  cases hbase'
  subst hbv
  simp only [amUses, amVregs, AMode.regs, List.filterMap, List.map, amodeAddr, Clif.Val.ofInt,
    Clif.Val.toNat, Option.some.injEq]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofInt]
  have := (spOf w).isLt
  show _ = ((((BitVec.ofInt 64 _ : BitVec 64).toNat : Int) + off) % 2 ^ 64).toNat
  rw [BitVec.toNat_ofInt]
  omega

end Build

variable {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config} (hc : cfg.checkOverlap = false)
variable {F : BitVec 64 → Prop} {isem : Sem} {sb : Nat}

set_option maxHeartbeats 2000000 in
include hp hc in
/-- **`amode ty x off`** (all four rules), for `ty` of 1, 2, 4 or 8 bytes. -/
theorem amode_ok (hR : Refines F isem) {f : Clif.Function} (hctx : CtxInv f ctx) {n : Nat}
    (hn : 300 ≤ n) {x : Nat} {t : CTy} {off : Int} {st : LState} {tr : Array RuleId}
    {s' : LState × Array RuleId} {v : V} (hvb : ValsBelow ctx st)
    (hb : t.bytes = 1 ∨ t.bytes = 2 ∨ t.bytes = 4 ∨ t.bytes = 8)
    (h : ApplyInternal p (sem ctx) cfg n 89 574 [.ty t, .value x, .int off] (st, tr) v s') :
    ∃ ms am, v.amode? = some am ∧ AmOk F isem sb ctx st s'.1 ms am t.bytes x off := by
  revert hb
  mem_split hp hc h 574
  · -- 4047: `stack_addr`
    intro hb
    mem_invd hp hctx at hm he
    repeat (simp only [ctor_i32_to_offset32', ctor_abi_stackslot_offset_iff, ctor_i32_into_i64']
      at * <;> isel_destruct <;> subst_vars)
    exact ⟨[], _, rfl, amOk_slot ‹_› ‹_›⟩
  · -- 4043: `iadd (iconst c) y`
    intro hb
    mem_invd hp hctx at hm he
    have h575 := ‹ApplyInternal _ _ _ _ 89 575 _ _ _ _›
    obtain ⟨ms, am, ham, hok⟩ := amode_nmi_ok hp ctx hc hR hctx (by omega) hvb hb h575
    exact ⟨ms, am, ham, amOk_rebase hok (fold_val true ‹_› ‹_›)⟩
  · -- 4040: `iadd x (iconst c)`
    intro hb
    mem_invd hp hctx at hm he
    have h575 := ‹ApplyInternal _ _ _ _ 89 575 _ _ _ _›
    obtain ⟨ms, am, ham, hok⟩ := amode_nmi_ok hp ctx hc hR hctx (by omega) hvb hb h575
    exact ⟨ms, am, ham, amOk_rebase hok (fold_val false ‹_› ‹_›)⟩
  · -- 4038: `amode_no_more_iconst`
    intro hb
    mem_invd hp hctx at hm he
    have h575 := ‹ApplyInternal _ _ _ _ 89 575 _ _ _ _›
    exact amode_nmi_ok hp ctx hc hR hctx (by omega) hvb hb h575

end Backend.Proof
