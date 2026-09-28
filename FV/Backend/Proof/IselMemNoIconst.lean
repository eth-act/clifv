import FV.Backend.Proof.IselMemAddr

/-!
# Memory family (M4Mem2): `amode_no_more_iconst`

The addressing-mode contract `AmOk` (code `ms` defining fresh vregs; an addressing mode over int
vregs whose effective address, after the code ran, is `x + off` for the 64-bit address value
`x`) and its proof for all eleven rules of `amode_no_more_iconst` (`inst.isle:4053`): immediate
offsets (`Unscaled`, `UnsignedOffset`), a materialised offset (`RegReg x (imm off)`), and the
`iadd` look-throughs (`RegReg`, `RegExtended`, `amode_reg_scaled` of `ishl` by a constant).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

open Lean Elab Tactic Meta in
/-- `mem_vregs hctx`: substitute `r := .vreg y .int` for every hypothesis
`ctx.valueReg? y = some r` with `r` a local (`CtxInv.valueReg`). -/
elab "mem_vregs " hctx:ident : tactic => do
  let mut progress := true
  while progress do
    progress := false
    let g ← getMainGoal
    let found ← g.withContext do
      for d in (← getLCtx) do
        if d.isImplementationDetail then continue
        let ty ← instantiateMVars d.type
        let some (_, l, r) := ty.eq? | continue
        unless l.isAppOf ``Backend.Ctx.valueReg? && r.isAppOfArity ``Option.some 2 &&
          r.appArg!.isFVar do continue
        let e ← mkAppM ``Backend.Proof.CtxInv.valueReg
          #[(← getLocalDeclFromUserName hctx.getId).toExpr, l.appArg!, r.appArg!, d.toExpr]
        return some e
      return none
    if let some e := found then
      let g ← g.withContext do
        let g ← g.assert `hvr (← inferType e) e
        let (fv, g) ← g.intro1P
        Lean.Meta.subst g fv
      replaceMainGoal [g]
      progress := true

/-- What `amode ty x off` produced (`bytes = ty.bytes`): code `ms` from `st` to `st'` and an
addressing mode over int vregs; from a run-time context where `x` holds a 64-bit value `pv`, the
code reads fresh or defined vregs, the mode's vregs are fresh or defined, and after the code the
mode's effective address is `pv + off`. -/
structure AmOk (F : BitVec 64 → Prop) (isem : Sem) (sb : Nat) (ctx : Ctx) (st st' : LState)
    (ms : List MInst) (am : AMode) (bytes x : Nat) (off : Int) : Prop where
  frag : Frag st st' ms
  vregs : AmVregs am
  run : ∀ fr ρ w pv, RtOk ctx sb fr ρ w → fr.regs x = some pv → pv.ty = .i64 →
    UsesLo st.nextVreg fr ms ∧ (∀ u ∈ amVregs am, st.nextVreg ≤ u ∨ (fr.regs u).isSome) ∧
    Runs F isem ms ρ w (fun ρ' w' =>
      amodeAddr sb am bytes (amUses am ρ') w' = some (BitVec.ofInt 64 (pv.toNat + off)))

section Arith

theorem ofInt_add64 (a b : Int) : BitVec.ofInt 64 (a + b) = BitVec.ofInt 64 a + BitVec.ofInt 64 b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt, BitVec.toNat_add]
  omega

theorem ofInt_nat64 (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  omega

theorem addr_arith (X Y : Nat) (off : Int) :
    BitVec.ofInt 64 ((((X + Y) % 2 ^ 64 : Nat) : Int) + off) =
      BitVec.ofNat 64 X + BitVec.ofInt 64 off + BitVec.ofNat 64 Y := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem addr_nat_off (X : Nat) (off : Int) :
    BitVec.ofInt 64 ((X : Int) + off) = BitVec.ofNat 64 X + BitVec.ofInt 64 off := by
  rw [ofInt_add64, ofInt_nat64]

theorem log2_scale {B N : Nat} (hN : N < 2 ^ 64) (hb : B = 1 ∨ B = 2 ∨ B = 4 ∨ B = 8)
    (h : true = ((B : Int) == ((u64 (1 * 2 ^ ((((u64 (N : Int) % 256).land 63 : Nat) : Int).toNat % 64)) :
      Nat) : Int))) : log2 B = N % 64 := by
  have hu : u64 (N : Int) = N := fb_u64_nat hN
  rw [hu] at h
  have hl : (N % 256).land 63 = N % 64 := by
    show (N % 256) &&& (2 ^ 6 - 1) = N % 64
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega
  rw [hl] at h
  simp only [Int.toNat_natCast, Nat.mod_mod, Int.one_mul] at h
  have hk : N % 64 < 64 := Nat.mod_lt _ (by decide)
  have hp : 2 ^ (N % 64) < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hk
  have hu2 : u64 ((2 : Int) ^ (N % 64)) = 2 ^ (N % 64) := by
    have := fb_u64_nat hp; push_cast at this; exact this
  rw [hu2] at h
  have hB : B = 2 ^ (N % 64) := by
    have := (beq_iff_eq.mp h.symm)
    exact_mod_cast this
  generalize N % 64 = k at hB ⊢
  have hk4 : k < 4 := by
    refine Nat.lt_of_not_le fun hc => ?_
    have : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hc
    rcases hb with rfl | rfl | rfl | rfl <;> omega
  have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl <;> subst hB <;> rfl

end Arith

section Values

/-- The value of a looked-through `iadd` at `i64`. -/
theorem iadd_val {ctx : Ctx} {fr : Clif.Frame} (hdfg : DFGCons ctx fr) {x a b : Nat} {ty : Clif.Ty}
    (hdc : ctx.defClif? x = some (.binary .iadd ty a b)) {pv : Clif.Val} (hx : fr.regs x = some pv)
    (ht : pv.ty = .i64) :
    ∃ av bv, fr.regs a = some av ∧ fr.regs b = some bv ∧ av.ty = .i64 ∧ bv.ty = .i64 ∧
      pv.toNat = (av.toNat + bv.toNat) % 2 ^ 64 := by
  obtain ⟨tyy, bits⟩ := pv
  simp only at ht; subst ht
  obtain ⟨j, info, hj, hij, hcl⟩ := defClif_inv hdc
  obtain ⟨u, w, hu, hw, hb⟩ := binary_value hdfg hj hij hcl rfl (getAs_of_regs hx)
  refine ⟨⟨.i64, u⟩, ⟨.i64, w⟩, getAs_ok hu, getAs_ok hw, rfl, rfl, ?_⟩
  subst hb
  simp only [Clif.Val.toNat, Clif.Sem.binary, Clif.Sem.iadd, BitVec.toNat_add]
  rfl

/-- The value of a looked-through `ishl` by an `iconst` at `i64`. -/
theorem ishl_val {ctx : Ctx} {fr : Clif.Frame} (hdfg : DFGCons ctx fr) {y z b : Nat}
    {ty1 ty3 : Clif.Ty} {c3 : BitVec ty3.width}
    (hdc : ctx.defClif? y = some (.binary .ishl ty1 z b)) (hdb : ctx.defClif? b = some (.iconst ty3 c3))
    {yv : Clif.Val} (hy : fr.regs y = some yv) (ht : yv.ty = .i64) :
    ty1 = .i64 ∧ ∃ zv, fr.regs z = some zv ∧ zv.ty = .i64 ∧
      BitVec.ofNat 64 yv.toNat = BitVec.ofNat 64 zv.toNat <<< (c3.toNat % 64) := by
  obtain ⟨j1, info1, hj1, hij1, hcl1⟩ := defClif_inv hdc
  obtain ⟨j2, info2, hj2, hij2, hcl2⟩ := defClif_inv hdb
  obtain ⟨vals, hev, hl⟩ := hdfg.1 y j1 info1 _ yv hj1 hij1 hcl1 rfl hy
  obtain ⟨u, bv, r, hz, hb, hr, rfl⟩ := evalInst_shift_inv rfl (hev default)
  have hyv := lookup_zip_single hl
  subst hyv
  simp only at ht; subst ht
  have hbv := dfg_single hdfg hj2 hij2 hcl2 rfl (get_ok hb) (a := ⟨ty3, c3⟩)
    (fun vals cm cm' h => by rw [evalInst_iconst] at h; cases h; rfl)
  subst hbv
  simp only [Clif.Sem.shift, Option.some.injEq] at hr
  subst hr
  refine ⟨rfl, ⟨.i64, u⟩, getAs_ok hz, rfl, ?_⟩
  simp only [Clif.Val.toNat, Clif.Sem.ishl, Clif.Sem.shiftAmt]
  have e : ∀ (u : BitVec 64) (k : Nat), BitVec.ofNat 64 (u <<< k).toNat = BitVec.ofNat 64 u.toNat <<< k := by
    intro u k; rw [ofNat_toNat64, ofNat_toNat64]
  exact e u _

/-- The value of a looked-through extend of a 32-bit value at `i64`, as the extended operand. -/
theorem ext_val {ctx : Ctx} {fr : Clif.Frame} (hdfg : DFGCons ctx fr) {ρ : Nat → CV}
    (hv : ValsHeld fr ρ) {y x : Nat} {op : Clif.ExtendOp} {ty : Clif.Ty} {e : ExtendOp}
    (he : extOpOf op 32 = some e) (hdc : ctx.defClif? y = some (.extend op ty x))
    (hvt : ctx.valueType? x = some (.int 32)) {yv : Clif.Val} (hy : fr.regs y = some yv)
    (ht : yv.ty = .i64) :
    (fr.regs x).isSome ∧ BitVec.ofNat 64 yv.toNat = extendVal e 64 (ρ x) := by
  obtain ⟨tyy, bits⟩ := yv
  simp only at ht; subst ht
  obtain ⟨a, ha, haw, hbits⟩ := extend_value hdfg hdc hvt (getAs_of_regs hy)
  refine ⟨by rw [ha]; rfl, ?_⟩
  have hx := extendVal_holds he haw (hv x a ha) (Nat.le_refl 64)
  rw [BitVec.setWidth_eq] at hx
  rw [hx]
  subst hbits
  show BitVec.ofNat 64 (extVal op 64 a.bits).toNat = _
  rw [ofNat_toNat64]

end Values

section Build
variable {F : BitVec 64 → Prop} {isem : Sem} {sb : Nat} {ctx : Ctx}

theorem amVregs_pair (a b : Nat) : amVregs (.regReg (.vreg a .int) (.vreg b .int)) = [a, b] := rfl

theorem amVregs_ext (a b : Nat) (e : ExtendOp) :
    amVregs (.regExtended (.vreg a .int) (.vreg b .int) e) = [a, b] := rfl

theorem amVregs_one_uoff (a : Nat) (i : Nat) : amVregs (.unsignedOffset (.vreg a .int) i) = [a] := rfl

theorem amVregs_one_unscaled (a : Nat) (i : Int) : amVregs (.unscaled (.vreg a .int) i) = [a] := rfl

theorem amVregs_int {am : AMode} (h : ∀ r ∈ am.regs, ∃ n, r = .vreg n .int) : AmVregs am := h

/-- No code: an immediate-offset mode over `x`. -/
theorem amOk_nil {st : LState} {am : AMode} {bytes x : Nat} {off : Int} (hvr : AmVregs am)
    (hav : amVregs am = [x])
    (hsem : ∀ (A : CV) (pv : Clif.Val) (w : Arm.ArmState), pv.ty = .i64 →
      lo64 A = BitVec.ofNat 64 pv.toNat →
      amodeAddr sb am bytes [A] w = some (BitVec.ofInt 64 (pv.toNat + off))) :
    AmOk F isem sb ctx st st [] am bytes x off := by
  refine ⟨Frag.nil st, hvr, fun fr ρ w pv hrt hx ht => ⟨UsesLo.nil _ _, ?_, Runs.nil ?_⟩⟩
  · intro u hu
    rw [hav] at hu
    simp only [List.mem_singleton] at hu
    subst hu
    exact .inr (by rw [hx]; rfl)
  · simp only [amUses, hav, List.map]
    exact hsem _ pv w ht (lo64_of_holds (hrt.held x pv hx) ht)

/-- Code from `amode_add a off` (register `d`) and a mode `[d, y']` with `y'` a value's vreg. -/
theorem amOk_add {st st2 : LState} {ms : List MInst} {a d y' x : Nat} {off : Int} {am : AMode}
    {bytes : Nat} (hadd : AddOk F isem st st2 ms a off d) (hvr : AmVregs am)
    (hav : amVregs am = [d, y']) (hy' : y' < st.nextVreg)
    (hsem : ∀ fr ρ w pv, RtOk ctx sb fr ρ w → fr.regs x = some pv → pv.ty = .i64 →
      (fr.regs a).isSome ∧ (fr.regs y').isSome ∧ ∀ (A : CV) (w' : Arm.ArmState),
        lo64 A = lo64 (ρ a) + BitVec.ofInt 64 off →
        amodeAddr sb am bytes [A, ρ y'] w' = some (BitVec.ofInt 64 (pv.toNat + off))) :
    AmOk F isem sb ctx st st2 ms am bytes x off := by
  refine ⟨hadd.frag, hvr, fun fr ρ w pv hrt hx ht => ?_⟩
  obtain ⟨ha, hy, hA⟩ := hsem fr ρ w pv hrt hx ht
  refine ⟨fun m hm u hu => ?_, fun u hu => ?_, ?_⟩
  · rcases hadd.uses m hm u hu with h | rfl
    · exact .inl h
    · exact .inr ha
  · rw [hav] at hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    · rcases hadd.res with rfl | h
      · exact .inr ha
      · exact .inl h
    · exact .inr hy
  · refine (hadd.run ρ w).imp fun ρ' w' hr hd => ?_
    have hfy : ρ' y' = ρ y' := hadd.frag.frame hr hy'
    simp only [amUses, hav, List.map, hfy]
    exact hA _ _ hd

/-- `RegReg x (imm off)`: the materialised offset. -/
theorem amOk_imm {st st' : LState} {ms : List MInst} {x d : Nat} {off : Int}
    {bytes : Nat} (hx : x < st.nextVreg) (hsh : CodeShape st st' ms d st.nextVreg)
    (hrun : ∀ ρ, ∃ ρ' X, PRun F isem ms ρ ρ' ∧ lo64 (ρ' d) = BitVec.ofNat 64 X ∧
      X % 2 ^ 64 = u64 (u64 off : Int) % 2 ^ 64) :
    AmOk F isem sb ctx st st' ms (.regReg (.vreg x .int) (.vreg d .int)) bytes x off := by
  have hfr : Frag st st' ms := ⟨hsh.emitted, hsh.mono, hsh.defs⟩
  refine ⟨hfr, amVregs_int (by simp [AMode.regs]), fun fr ρ w pv hrt hxv ht => ?_⟩
  have hxs : (fr.regs x).isSome := by rw [hxv]; rfl
  refine ⟨fun m hm u hu => ?_, fun u hu => ?_, ?_⟩
  · rcases hsh.uses m hm u hu with h | h
    · exact .inl h
    · exact .inl (by omega)
  · simp only [amVregs_pair, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    · exact .inr hxs
    · exact .inl hsh.res
  · obtain ⟨ρ1, X, hp1, hX, hXc⟩ := hrun ρ
    refine Runs.of_prun hp1 w fun w' _ => ?_
    have hfx : ρ1 x = ρ x := hfr.frame (hp1 w).choose_spec.1 hx
    simp only [amUses, amVregs_pair, List.map, amodeAddr, hfx, hX]
    rw [lo64_of_holds (hrt.held x pv hxv) ht, ofNat_mod64 hXc, u64_u64, u64_ofNat_ofInt,
      addr_nat_off]

/-- The address of `a + b` (`x = iadd a b`) with `amode_add a off` as base and an index register
`y'` holding `b`'s value. -/
theorem sem_left {x a b y' : Nat} {ty : Clif.Ty} {am : AMode} {bytes : Nat} {off : Int}
    (hdc : ctx.defClif? x = some (.binary .iadd ty a b))
    (hidx : ∀ fr (ρ : Nat → CV), DFGCons ctx fr → ValsHeld fr ρ → ∀ bv, fr.regs b = some bv →
      bv.ty = .i64 → (fr.regs y').isSome ∧ ∀ (A : CV) (w' : Arm.ArmState),
        amodeAddr sb am bytes [A, ρ y'] w' = some (lo64 A + BitVec.ofNat 64 bv.toNat)) :
    ∀ fr ρ w pv, RtOk ctx sb fr ρ w → fr.regs x = some pv → pv.ty = .i64 →
      (fr.regs a).isSome ∧ (fr.regs y').isSome ∧ ∀ (A : CV) (w' : Arm.ArmState),
        lo64 A = lo64 (ρ a) + BitVec.ofInt 64 off →
        amodeAddr sb am bytes [A, ρ y'] w' = some (BitVec.ofInt 64 (pv.toNat + off)) := by
  intro fr ρ w pv hrt hx ht
  obtain ⟨av, bv, ha, hb, hat, hbt, hpv⟩ := iadd_val hrt.dfg hdc hx ht
  obtain ⟨hy', hA⟩ := hidx fr ρ hrt.dfg hrt.held bv hb hbt
  refine ⟨by rw [ha]; rfl, hy', fun A w' hAe => ?_⟩
  rw [hA, hAe, lo64_of_holds (hrt.held a av ha) hat, hpv, addr_arith]

/-- As `sem_left`, with `amode_add b off` as base and the index holding `a`'s value. -/
theorem sem_right {x a b y' : Nat} {ty : Clif.Ty} {am : AMode} {bytes : Nat} {off : Int}
    (hdc : ctx.defClif? x = some (.binary .iadd ty a b))
    (hidx : ∀ fr (ρ : Nat → CV), DFGCons ctx fr → ValsHeld fr ρ → ∀ av, fr.regs a = some av →
      av.ty = .i64 → (fr.regs y').isSome ∧ ∀ (A : CV) (w' : Arm.ArmState),
        amodeAddr sb am bytes [A, ρ y'] w' = some (lo64 A + BitVec.ofNat 64 av.toNat)) :
    ∀ fr ρ w pv, RtOk ctx sb fr ρ w → fr.regs x = some pv → pv.ty = .i64 →
      (fr.regs b).isSome ∧ (fr.regs y').isSome ∧ ∀ (A : CV) (w' : Arm.ArmState),
        lo64 A = lo64 (ρ b) + BitVec.ofInt 64 off →
        amodeAddr sb am bytes [A, ρ y'] w' = some (BitVec.ofInt 64 (pv.toNat + off)) := by
  intro fr ρ w pv hrt hx ht
  obtain ⟨av, bv, ha, hb, hat, hbt, hpv⟩ := iadd_val hrt.dfg hdc hx ht
  obtain ⟨hy', hA⟩ := hidx fr ρ hrt.dfg hrt.held av ha hat
  refine ⟨by rw [hb]; rfl, hy', fun A w' hAe => ?_⟩
  rw [hA, hAe, lo64_of_holds (hrt.held b bv hb) hbt, hpv, addr_arith]
  congr 1
  ac_rfl

/-- Index: the register of the value itself. -/
theorem idx_reg {b d : Nat} {bytes : Nat} :
    ∀ fr (ρ : Nat → CV), DFGCons ctx fr → ValsHeld fr ρ → ∀ bv, fr.regs b = some bv →
      bv.ty = .i64 → (fr.regs b).isSome ∧ ∀ (A : CV) (w' : Arm.ArmState),
        amodeAddr sb (.regReg (.vreg d .int) (.vreg b .int)) bytes [A, ρ b] w' =
          some (lo64 A + BitVec.ofNat 64 bv.toNat) := by
  intro fr ρ _ hv bv hb hbt
  refine ⟨by rw [hb]; rfl, fun A w' => ?_⟩
  simp only [amodeAddr]
  rw [lo64_of_holds (hv b bv hb) hbt]

/-- Index: the 32-bit operand `y'` of the extend defining `b`, extended. -/
theorem idx_ext {b d y' : Nat} {bytes : Nat} {op : Clif.ExtendOp} {ty : Clif.Ty} {e : ExtendOp}
    (he : extOpOf op 32 = some e) (hue : e = .uxtw ∨ e = .sxtw)
    (hdc : ctx.defClif? b = some (.extend op ty y')) (hvt : ctx.valueType? y' = some (.int 32)) :
    ∀ fr (ρ : Nat → CV), DFGCons ctx fr → ValsHeld fr ρ → ∀ bv, fr.regs b = some bv →
      bv.ty = .i64 → (fr.regs y').isSome ∧ ∀ (A : CV) (w' : Arm.ArmState),
        amodeAddr sb (.regExtended (.vreg d .int) (.vreg y' .int) e) bytes [A, ρ y'] w' =
          some (lo64 A + BitVec.ofNat 64 bv.toNat) := by
  intro fr ρ hdfg hv bv hb hbt
  obtain ⟨hs, hval⟩ := ext_val hdfg hv he hdc hvt hb hbt
  refine ⟨hs, fun A w' => ?_⟩
  simp only [amodeAddr, hue, ite_true]
  rw [hval]

/-- Index: `amode_reg_scaled` of the operand `z` of `ishl z (iconst c)` defining `b`, when the
access size is `2 ^ (c % 64)`. -/
theorem idx_scaled {b d z j : Nat} {bytes : Nat} {ty1 ty3 : Clif.Ty}
    {c3 : BitVec ty3.width} {am : AMode} (hsc : ScaledOk ctx d z am) {y' : Nat}
    (hav : amVregs am = [d, y'])
    (hdc : ctx.defClif? b = some (.binary .ishl ty1 z j)) (hdj : ctx.defClif? j = some (.iconst ty3 c3))
    (hlog : ty1 = .i64 → log2 bytes = c3.toNat % 64) :
    ∀ fr (ρ : Nat → CV), DFGCons ctx fr → ValsHeld fr ρ → ∀ bv, fr.regs b = some bv →
      bv.ty = .i64 → (fr.regs y').isSome ∧ ∀ (A : CV) (w' : Arm.ArmState),
        amodeAddr sb am bytes [A, ρ y'] w' = some (lo64 A + BitVec.ofNat 64 bv.toNat) := by
  intro fr ρ hdfg hv bv hb hbt
  obtain ⟨ht1, zv, hz, hzt, hbv⟩ := ishl_val hdfg hdc hdj hb hbt
  obtain ⟨y'', hav', -, hsem⟩ := hsc.idx
  rw [hav] at hav'
  obtain rfl : y' = y'' := by simpa using hav'
  obtain ⟨hs, hA⟩ := hsem sb fr ρ hdfg hv zv hz hzt
  refine ⟨hs, fun A w' => ?_⟩
  rw [hA, hbv, hlog ht1]

theorem uoff_sem {x : Nat} {off : Int} {bytes : Nat} (h0 : 0 ≤ off) (h1 : off ≤ 4095 * (bytes : Int))
    (h2 : off.toNat % bytes = 0) :
    ∀ (A : CV) (pv : Clif.Val) (w : Arm.ArmState), pv.ty = .i64 →
      lo64 A = BitVec.ofNat 64 pv.toNat →
      amodeAddr sb (.unsignedOffset (.vreg x .int) off.toNat) bytes [A] w =
        some (BitVec.ofInt 64 (pv.toNat + off)) := by
  intro A pv w _ hA
  have h3 : off.toNat ≤ 4095 * bytes := by omega
  simp only [amodeAddr, h2, h3, and_self, ite_true, hA]
  rw [addr_nat_off]
  congr 2
  rw [← ofInt_nat64, Int.toNat_of_nonneg h0]

theorem simm9_sem {x : Nat} {off : Int} {bytes : Nat} (h0 : -256 ≤ off) (h1 : off ≤ 255) :
    ∀ (A : CV) (pv : Clif.Val) (w : Arm.ArmState), pv.ty = .i64 →
      lo64 A = BitVec.ofNat 64 pv.toNat →
      amodeAddr sb (.unscaled (.vreg x .int) off) bytes [A] w =
        some (BitVec.ofInt 64 (pv.toNat + off)) := by
  intro A pv w _ hA
  simp only [amodeAddr, h0, h1, and_self, ite_true, hA]
  rw [addr_nat_off]

end Build

/-- The scale check of `amode_no_more_iconst`'s `ishl` rules: the access size is
`2 ^ (c % 64)` (the `ishl` is at `i64`). -/
theorem scale_log {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {jj : Nat} {info : IInfo}
    {ty1 : Clif.Ty} {z j : Nat} {ty3 : Clif.Ty} {c3 : BitVec ty3.width} {B : Nat}
    (h : true = ((B : Int) == ((u64 (1 * 2 ^ ((((u64 ((u64 (imm64OfIconst ty3 c3) : Nat) : Int) % 256).land
      ((info.resTys.head?.getD CTy.invalid).laneBits - 1) : Nat) : Int).toNat % 64)) : Nat) : Int)))
    (hcl : info.clif = some (.binary .ishl ty1 z j)) (hij : ctx.insts[jj]? = some info)
    (he3 : eTy ty3 = true) (hb : B = 1 ∨ B = 2 ∨ B = 4 ∨ B = 8) :
    ty1 = .i64 → log2 B = c3.toNat % 64 := by
  rintro rfl
  obtain ⟨tys, htys, hres, -⟩ := hctx.resTys jj info _ hij hcl
  simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
  subst htys
  rw [hres] at h
  have hw := eTy_width he3
  rw [fb_u64_imm64 hw] at h
  exact log2_scale (Nat.lt_of_lt_of_le c3.isLt (Nat.pow_le_pow_right (by decide) hw)) hb h

variable {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config} (hc : cfg.checkOverlap = false)
variable {F : BitVec 64 → Prop} {isem : Sem} {sb : Nat}

set_option maxHeartbeats 4000000 in
include hp hc in
/-- **`amode_no_more_iconst ty x off`** (all eleven rules), for `ty` of 1, 2, 4 or 8 bytes. -/
theorem amode_nmi_ok (hR : Refines F isem) {f : Clif.Function} (hctx : CtxInv f ctx) {n : Nat}
    (hn : 200 ≤ n) {x : Nat} {t : CTy} {off : Int} {st : LState} {tr : Array RuleId}
    {s' : LState × Array RuleId} {v : V} (hvb : ValsBelow ctx st)
    (hb : t.bytes = 1 ∨ t.bytes = 2 ∨ t.bytes = 4 ∨ t.bytes = 8)
    (h : ApplyInternal p (sem ctx) cfg n 89 575 [.ty t, .value x, .int off] (st, tr) v s') :
    ∃ ms am, v.amode? = some am ∧ AmOk F isem sb ctx st s'.1 ms am t.bytes x off := by
  revert hb
  mem_split hp hc h 575
  · -- 4103: non-zero scaled `uimm12`
    intro hb
    mem_invd hp hctx at hm he
    mem_vregs hctx
    exact ⟨[], _, rfl, amOk_nil (amVregs_int (by simp [AMode.regs])) (amVregs_one_uoff _ _)
      (uoff_sem ‹_› ‹_› ‹_›)⟩
  · -- 4096: `(ishl y c) + x`
    intro hb
    mem_invd hp hctx at hm he
    mem_vregs hctx
    have h577 := ‹ApplyInternal _ _ _ _ 27 577 _ _ _ _›
    have h576 := ‹ApplyInternal _ _ _ _ 89 576 _ _ _ _›
    have hlog := scale_log hctx ‹true = _› ‹IInfo.clif _ = some (.binary .ishl _ _ _)› ‹_› ‹_› hb
    obtain ⟨d, ms, rfl, hadd⟩ := amode_add_ok hp ctx hc hR (by omega) (hvb _ _ (by assumption)) h577
    obtain ⟨hs, am, ham, hsc⟩ := amode_reg_scaled_ok hp ctx hc hctx (by omega) h576
    obtain ⟨y', hav, hvr', -⟩ := hsc.idx
    simp only at hs
    subst hs
    exact ⟨ms, am, ham, amOk_add hadd hsc.vregs hav (hvb _ _ hvr')
      (sem_right ‹ctx.defClif? x = some _› (idx_scaled hsc hav ‹_› ‹_› hlog))⟩
  · -- 4093: `x + (ishl y c)`
    intro hb
    mem_invd hp hctx at hm he
    mem_vregs hctx
    have h577 := ‹ApplyInternal _ _ _ _ 27 577 _ _ _ _›
    have h576 := ‹ApplyInternal _ _ _ _ 89 576 _ _ _ _›
    have hlog := scale_log hctx ‹true = _› ‹IInfo.clif _ = some (.binary .ishl _ _ _)› ‹_› ‹_› hb
    obtain ⟨d, ms, rfl, hadd⟩ := amode_add_ok hp ctx hc hR (by omega) (hvb _ _ (by assumption)) h577
    obtain ⟨hs, am, ham, hsc⟩ := amode_reg_scaled_ok hp ctx hc hctx (by omega) h576
    obtain ⟨y', hav, hvr', -⟩ := hsc.idx
    simp only at hs
    subst hs
    exact ⟨ms, am, ham, amOk_add hadd hsc.vregs hav (hvb _ _ hvr')
      (sem_left ‹ctx.defClif? x = some _› (idx_scaled hsc hav ‹_› ‹_› hlog))⟩
  · -- 4081: `uextend x + y`
    intro hb
    mem_invd hp hctx at hm he
    mem_vregs hctx
    have h577 := ‹ApplyInternal _ _ _ _ 27 577 _ _ _ _›
    obtain ⟨d, ms, rfl, hadd⟩ := amode_add_ok hp ctx hc hR (by omega) (hvb _ _ (by assumption)) h577
    exact ⟨ms, _, rfl, amOk_add hadd (amVregs_int (by simp [AMode.regs])) (amVregs_ext _ _ _)
      (hvb _ _ (by assumption)) (sem_right ‹ctx.defClif? x = some _› (idx_ext (op := .uextend) rfl (.inl rfl) ‹_› ‹_›))⟩
  · -- 4083: `sextend x + y`
    intro hb
    mem_invd hp hctx at hm he
    mem_vregs hctx
    have h577 := ‹ApplyInternal _ _ _ _ 27 577 _ _ _ _›
    obtain ⟨d, ms, rfl, hadd⟩ := amode_add_ok hp ctx hc hR (by omega) (hvb _ _ (by assumption)) h577
    exact ⟨ms, _, rfl, amOk_add hadd (amVregs_int (by simp [AMode.regs])) (amVregs_ext _ _ _)
      (hvb _ _ (by assumption)) (sem_right ‹ctx.defClif? x = some _› (idx_ext (op := .sextend) rfl (.inr rfl) ‹_› ‹_›))⟩
  · -- 4077: `x + uextend y`
    intro hb
    mem_invd hp hctx at hm he
    mem_vregs hctx
    have h577 := ‹ApplyInternal _ _ _ _ 27 577 _ _ _ _›
    obtain ⟨d, ms, rfl, hadd⟩ := amode_add_ok hp ctx hc hR (by omega) (hvb _ _ (by assumption)) h577
    exact ⟨ms, _, rfl, amOk_add hadd (amVregs_int (by simp [AMode.regs])) (amVregs_ext _ _ _)
      (hvb _ _ (by assumption)) (sem_left ‹ctx.defClif? x = some _› (idx_ext (op := .uextend) rfl (.inl rfl) ‹_› ‹_›))⟩
  · -- 4079: `x + sextend y`
    intro hb
    mem_invd hp hctx at hm he
    mem_vregs hctx
    have h577 := ‹ApplyInternal _ _ _ _ 27 577 _ _ _ _›
    obtain ⟨d, ms, rfl, hadd⟩ := amode_add_ok hp ctx hc hR (by omega) (hvb _ _ (by assumption)) h577
    exact ⟨ms, _, rfl, amOk_add hadd (amVregs_int (by simp [AMode.regs])) (amVregs_ext _ _ _)
      (hvb _ _ (by assumption)) (sem_left ‹ctx.defClif? x = some _› (idx_ext (op := .sextend) rfl (.inr rfl) ‹_› ‹_›))⟩
  · -- 4075: `x + y`
    intro hb
    mem_invd hp hctx at hm he
    mem_vregs hctx
    have h577 := ‹ApplyInternal _ _ _ _ 27 577 _ _ _ _›
    obtain ⟨d, ms, rfl, hadd⟩ := amode_add_ok hp ctx hc hR (by omega) (hvb _ _ (by assumption)) h577
    exact ⟨ms, _, rfl, amOk_add hadd (amVregs_int (by simp [AMode.regs])) (amVregs_pair _ _)
      (hvb _ _ (by assumption)) (sem_left ‹_› idx_reg)⟩
  · -- 4064: scaled `uimm12`
    intro hb
    mem_invd hp hctx at hm he
    mem_vregs hctx
    exact ⟨[], _, rfl, amOk_nil (amVregs_int (by simp [AMode.regs])) (amVregs_one_uoff _ _)
      (uoff_sem ‹_› ‹_› ‹_›)⟩
  · -- 4061: `simm9`
    intro hb
    mem_invd hp hctx at hm he
    mem_vregs hctx
    exact ⟨[], _, rfl, amOk_nil (amVregs_int (by simp [AMode.regs])) (amVregs_one_unscaled _ _)
      (simm9_sem ‹_› ‹_›)⟩
  · -- 4056: `RegReg x (imm off)`
    intro hb
    mem_invd hp hctx at hm he
    mem_vregs hctx
    have h553 := ‹ApplyInternal _ _ _ _ 27 553 _ _ _ _›
    obtain ⟨ms, d, rfl, hsh, hrun⟩ := imm64_inv hp ctx hc hR (by omega) h553
    exact ⟨ms, _, rfl, amOk_imm (hvb x _ ‹_›) hsh fun ρ => by
      obtain ⟨ρ', X, h1, h2, h3, -⟩ := hrun ρ; exact ⟨ρ', X, h1, h2, h3⟩⟩

end Backend.Proof
