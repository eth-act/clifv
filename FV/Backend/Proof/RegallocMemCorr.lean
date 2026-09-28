import FV.Backend.Proof.RegallocMem

/-!
# `Corr` for every load and store form (M6 proof)

`load_core`/`store_core` (the operand-independent parts) applied to the addressing modes the
lowering emits (`amodeAddr`'s forms): stack-slot offsets (no register operand), one base
register (`unscaled`, `unsignedOffset`), base and index registers (`regReg`, `regScaled`,
`regScaledExtended`, `regExtended`). The generic lemmas take the addressing mode as a function
of its registers whose address is a function of the registers' values.
-/

namespace Backend.Proof

open Backend

/-! ## Stores -/

theorem mem_write_mem_bytes_ne : ∀ (n : Nat) (a : BitVec 64) (v : BitVec (n * 8)) (s : Arm.ArmState)
    (x : BitVec 64), (∀ k < n, x ≠ a + BitVec.ofNat 64 k) → (Arm.write_mem_bytes n a v s).mem x = s.mem x
  | 0, _, _, _, _, _ => rfl
  | n + 1, a, v, s, x, h => by
    simp only [Arm.write_mem_bytes]
    rw [mem_write_mem_bytes_ne n (a + 1#64) _ _ x (fun k hk e => h (k + 1) (by omega) (by
      rw [e, BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega))]
    have h0 : x ≠ a := by simpa using h 0 (by omega)
    simp [Arm.write_mem, Arm.write_store, h0]

/-- The post-state of a store. -/
def stPost (s : Arm.ArmState) (P : BitVec 64) (n : Nat) (a : BitVec 64) (v : BitVec (n * 8))
    (o : Option (BitVec 64)) : Arm.ArmState :=
  Arm.w .PC P (Arm.write_mem_bytes n a v (x16w o s))

/-- The allocated/canonical correspondence of one store. -/
theorem store_core {F : BitVec 64 → Prop} (ctx : FnCtx) (env : Env) (op : StoreOp)
    (hop : op ≠ .fpuStore128) (fl : Clif.MemFlags) {n0 : Nat}
    (hn0 : n0 < 29 ∧ n0 ≠ 16 ∧ n0 ≠ 17 ∧ n0 ≠ 18) {m mC : AMode}
    (hm : MemMode op.bytes m) (hmC : MemMode op.bytes mC) {s t t' : Arm.ArmState}
    (hal : Arm.CheckSPAlignment s) (hwt : SameWorld F s t)
    (hsp_t : Arm.r (.GPR 31#5) t = Arm.r (.GPR 31#5) s)
    (hv_t : Arm.r (.GPR (BitVec.ofNat 5 0)) t = Arm.r (.GPR (BitVec.ofNat 5 n0)) s)
    (hacc : AccessOk F ctx (.store op (.x 0) mC fl) t)
    (hex : execMInst ctx env0 (.store op (.x 0) mC fl) t = some t')
    (haddr : mC.addr ctx op.bytes t = m.addr ctx op.bytes s) :
    ∃ S, execMInst ctx env (.store op (.x n0) m fl) s = some S ∧ SameWorld F S t' ∧
      FrameKeep F s S ∧ ∀ r, r.allocatable = true → regVal S r = regVal s r := by
  obtain ⟨ls, o, hl, hS⟩ := execMInst_store ctx env op hop (d := n0) (by omega) hn0.2.1 m fl hm s hal
  obtain ⟨lsC, oC, hlC, hT⟩ := execMInst_store ctx env0 op hop (d := 0) (by omega) (by omega) mC fl
    hmC t (align_of_spEq hsp_t hal)
  simp only [execMInst, hlC, hT.exec, Option.some.injEq] at hex
  subst hex
  have hav : Avoids F op.bytes (m.addr ctx op.bytes s) := by
    have := hacc (mC.addr ctx op.bytes t, op.bytes) (by simp [MInst.accesses])
    rw [← haddr]; exact this
  refine ⟨_, by simp only [execMInst, hl]; exact hS.exec, ?_, ⟨?_, fun a ha => ?_⟩, fun r hr => ?_⟩
  · refine SameWorld.w_right (by simp [Masked]) (SameWorld.w_left (by simp [Masked]) ?_)
    refine SameWorld.write_mem_bytes' haddr.symm (by rw [hv_t]) (sameWorld_x16w o oC hwt)
  · simp only [spOf]
    rw [Arm.r_of_w_different (by simp), Arm.r_of_write_mem_bytes]
    exact (x16w_facts o s).2.2.2.2
  · rw [Arm.ArmState.mem_w_eq_mem, mem_write_mem_bytes_ne _ _ _ _ _ (fun k hk e => hav k hk (e ▸ ha)),
      (x16w_facts o s).2.2.2.1]
  · rcases allocatable_cases hr with ⟨k, rfl, hk⟩ | ⟨k, rfl, hk⟩
    · have e2 : rnum k ≠ 16#5 := rnum_ne (a := k) (b := 16) (by omega) (by omega) (by omega)
      cases o <;> simp [regVal, x16w, Arm.r_of_w_different, Arm.r_of_write_mem_bytes, e2]
    · cases o <;> simp [regVal, x16w, Arm.r_of_w_different, Arm.r_of_write_mem_bytes]

/-! ## Generic `Corr` lemmas -/


/-- Close the `Corr` of a load from `load_core`'s result. -/
syntax "load_fin" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| load_fin) => `(tactic| (
    obtain ⟨S, h1, h2, h3, h4, h5⟩ := hcore
    exact ⟨S, h1, h2, h3, by simp [defVals, Operand.isDef, h4], fun r hr hnd => h5 r hr
      (fun e => hnd ⟨⟨d, .int, .def, .late, .reg⟩, .x n0⟩ (by simp) rfl e.symm)⟩))

theorem corr_load0 (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (op : LoadOp)
    (hop : op ≠ .fpuLoad128) (d : Nat) (off : Int) (fl : Clif.MemFlags) :
    Corr F ctx env #[⟨d, .int, .def, .late, .reg⟩]
      (fun r => .load op (r.getD 0 .xzr) (.slotOffset off) fl) := by
  intro regs s w t' ha hw hal hacc hex herr
  have hsz := ha.size
  simp only [List.size_toArray, List.length_cons, List.length_nil] at hsz
  have hf := ha.fits
  obtain ⟨r0, rfl⟩ := regs1 hsz
  simp [RegFits] at hf
  rcases hf with ⟨n0, rfl, hn0⟩
  have hcanon : canonRegs #[⟨d, .int, .def, .late, .reg⟩] = #[.x 0] := by
    simp [canonRegs, canonReg, canonBase, List.range_succ]
  have ht : placeUses #[⟨d, .int, .def, .late, .reg⟩] (canonRegs #[⟨d, .int, .def, .late, .reg⟩])
      (useVals #[⟨d, .int, .def, .late, .reg⟩] #[.x n0] s) w = w := by
    simp [placeUses, useVals, hcanon, Operand.isUse]
  rw [ht, hcanon] at hex hacc
  rw [hcanon]
  have hsp : Arm.r (.GPR 31#5) w = Arm.r (.GPR 31#5) s := sw_r_eq hw (by simp [Masked])
  have hcore := load_core ctx env op hop fl hn0 (m := .slotOffset off) (mC := .slotOffset off)
    trivial trivial hal hw hsp (fun x hx => (hw.2.1 x hx).symm) hacc hex
    (by simp [AMode.addr, spOf, hsp])
  load_fin

theorem corr_load1 (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (op : LoadOp)
    (hop : op ≠ .fpuLoad128) (d n : Nat) (fl : Clif.MemFlags) (A : Reg → AMode)
    (g : BitVec 64 → BitVec 64)
    (hA : ∀ a : Nat, a < 29 → MemMode op.bytes (A (.x a)))
    (hg : ∀ (a : Nat) s, (A (.x a)).addr ctx op.bytes s = g (Arm.r (.GPR (rnum a)) s)) :
    Corr F ctx env #[⟨d, .int, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩]
      (fun r => .load op (r.getD 0 .xzr) (A (r.getD 1 .xzr)) fl) := by
  intro regs s w t' ha hw hal hacc hex herr
  have hsz := ha.size
  simp only [List.size_toArray, List.length_cons, List.length_nil] at hsz
  have hf := ha.fits
  obtain ⟨r0, r1, rfl⟩ := regs2 hsz
  simp [RegFits] at hf
  rcases hf with ⟨⟨n0, rfl, hn0⟩, ⟨n1, rfl, hn1⟩⟩
  have hcanon : canonRegs #[⟨d, .int, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩] =
      #[.x 0, .x 1] := by
    simp [canonRegs, canonReg, canonBase, List.range_succ]
  have ht : placeUses #[⟨d, .int, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩]
      (canonRegs #[⟨d, .int, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩])
      (useVals #[⟨d, .int, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩] #[.x n0, .x n1] s) w =
      Arm.w (.GPR 1#5) (Arm.r (.GPR (rnum n1)) s) w := by
    simp [placeUses, useVals, hcanon, Operand.isUse, lo64, regVal, rnum]
  rw [ht, hcanon] at hex hacc
  rw [hcanon]
  have hcore := load_core ctx env op hop fl hn0 (m := A (.x n1)) (mC := A (.x 1))
    (hA _ hn1.1) (hA 1 (by decide)) hal
    (SameWorld.w_right (by simp [Masked]) hw)
    (by rw [Arm.r_of_w_different (by simp)]; exact sw_r_eq hw (by simp [Masked]))
    (fun x hx => by rw [Arm.ArmState.mem_w_eq_mem]; exact (hw.2.1 x hx).symm) hacc hex
    (by rw [hg, hg]; simp [rnum])
  load_fin

theorem corr_load2 (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (op : LoadOp)
    (hop : op ≠ .fpuLoad128) (d n m : Nat) (fl : Clif.MemFlags) (A : Reg → Reg → AMode)
    (g : BitVec 64 → BitVec 64 → BitVec 64)
    (hA : ∀ a b : Nat, a < 29 → b < 29 → MemMode op.bytes (A (.x a) (.x b)))
    (hg : ∀ (a b : Nat) s, (A (.x a) (.x b)).addr ctx op.bytes s =
      g (Arm.r (.GPR (rnum a)) s) (Arm.r (.GPR (rnum b)) s)) :
    Corr F ctx env #[⟨d, .int, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩,
      ⟨m, .int, .use, .early, .reg⟩]
      (fun r => .load op (r.getD 0 .xzr) (A (r.getD 1 .xzr) (r.getD 2 .xzr)) fl) := by
  intro regs s w t' ha hw hal hacc hex herr
  have hsz := ha.size
  simp only [List.size_toArray, List.length_cons, List.length_nil] at hsz
  have hf := ha.fits
  obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz
  simp [RegFits] at hf
  rcases hf with ⟨⟨n0, rfl, hn0⟩, ⟨n1, rfl, hn1⟩, ⟨n2, rfl, hn2⟩⟩
  have hcanon : canonRegs #[⟨d, .int, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩,
      ⟨m, .int, .use, .early, .reg⟩] = #[.x 0, .x 1, .x 2] := by
    simp [canonRegs, canonReg, canonBase, List.range_succ]
  have ht : placeUses #[⟨d, .int, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩,
      ⟨m, .int, .use, .early, .reg⟩]
      (canonRegs #[⟨d, .int, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩,
        ⟨m, .int, .use, .early, .reg⟩])
      (useVals #[⟨d, .int, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩,
        ⟨m, .int, .use, .early, .reg⟩] #[.x n0, .x n1, .x n2] s) w =
      Arm.w (.GPR 2#5) (Arm.r (.GPR (rnum n2)) s) (Arm.w (.GPR 1#5) (Arm.r (.GPR (rnum n1)) s) w) := by
    simp [placeUses, useVals, hcanon, Operand.isUse, lo64, regVal, rnum]
  rw [ht, hcanon] at hex hacc
  rw [hcanon]
  have hcore := load_core ctx env op hop fl hn0 (m := A (.x n1) (.x n2)) (mC := A (.x 1) (.x 2))
    (hA _ _ hn1.1 hn2.1) (hA 1 2 (by decide) (by decide)) hal
    (SameWorld.w_right (by simp [Masked]) (SameWorld.w_right (by simp [Masked]) hw))
    (by rw [Arm.r_of_w_different (by simp), Arm.r_of_w_different (by simp)]
        exact sw_r_eq hw (by simp [Masked]))
    (fun x hx => by rw [Arm.ArmState.mem_w_eq_mem, Arm.ArmState.mem_w_eq_mem]; exact (hw.2.1 x hx).symm)
    hacc hex (by rw [hg, hg]; simp [rnum])
  load_fin

/-- Close the `Corr` of a store from `store_core`'s result. -/
syntax "store_fin" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| store_fin) => `(tactic| (
    obtain ⟨S, h1, h2, h3, h5⟩ := hcore
    exact ⟨S, h1, h2, h3, by simp [defVals, Operand.isDef], fun r hr _ => h5 r hr⟩))

theorem corr_store0 (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (op : StoreOp)
    (hop : op ≠ .fpuStore128) (d : Nat) (off : Int) (fl : Clif.MemFlags) :
    Corr F ctx env #[⟨d, .int, .use, .early, .reg⟩]
      (fun r => .store op (r.getD 0 .xzr) (.slotOffset off) fl) := by
  intro regs s w t' ha hw hal hacc hex herr
  have hsz := ha.size
  simp only [List.size_toArray, List.length_cons, List.length_nil] at hsz
  have hf := ha.fits
  obtain ⟨r0, rfl⟩ := regs1 hsz
  simp [RegFits] at hf
  rcases hf with ⟨n0, rfl, hn0⟩
  have hcanon : canonRegs #[⟨d, .int, .use, .early, .reg⟩] = #[.x 0] := by
    simp [canonRegs, canonReg, canonBase, List.range_succ]
  have ht : placeUses #[⟨d, .int, .use, .early, .reg⟩] (canonRegs #[⟨d, .int, .use, .early, .reg⟩])
      (useVals #[⟨d, .int, .use, .early, .reg⟩] #[.x n0] s) w =
      Arm.w (.GPR 0#5) (Arm.r (.GPR (rnum n0)) s) w := by
    simp [placeUses, useVals, hcanon, Operand.isUse, lo64, regVal, rnum]
  rw [ht, hcanon] at hex hacc
  rw [hcanon]
  have hsp : Arm.r (.GPR 31#5) (Arm.w (.GPR 0#5) (Arm.r (.GPR (rnum n0)) s) w) = Arm.r (.GPR 31#5) s := by
    rw [Arm.r_of_w_different (by simp)]; exact sw_r_eq hw (by simp [Masked])
  have hcore := store_core ctx env op hop fl hn0 (m := .slotOffset off) (mC := .slotOffset off)
    trivial trivial hal (SameWorld.w_right (by simp [Masked]) hw) hsp
    (by simp [rnum]) hacc hex (by simp only [AMode.addr, spOf]; rw [hsp])
  store_fin

theorem corr_store1 (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (op : StoreOp)
    (hop : op ≠ .fpuStore128) (d n : Nat) (fl : Clif.MemFlags) (A : Reg → AMode)
    (g : BitVec 64 → BitVec 64)
    (hA : ∀ a : Nat, a < 29 → MemMode op.bytes (A (.x a)))
    (hg : ∀ (a : Nat) s, (A (.x a)).addr ctx op.bytes s = g (Arm.r (.GPR (rnum a)) s)) :
    Corr F ctx env #[⟨d, .int, .use, .early, .reg⟩, ⟨n, .int, .use, .early, .reg⟩]
      (fun r => .store op (r.getD 0 .xzr) (A (r.getD 1 .xzr)) fl) := by
  intro regs s w t' ha hw hal hacc hex herr
  have hsz := ha.size
  simp only [List.size_toArray, List.length_cons, List.length_nil] at hsz
  have hf := ha.fits
  obtain ⟨r0, r1, rfl⟩ := regs2 hsz
  simp [RegFits] at hf
  rcases hf with ⟨⟨n0, rfl, hn0⟩, ⟨n1, rfl, hn1⟩⟩
  have hcanon : canonRegs #[⟨d, .int, .use, .early, .reg⟩, ⟨n, .int, .use, .early, .reg⟩] =
      #[.x 0, .x 1] := by
    simp [canonRegs, canonReg, canonBase, List.range_succ]
  have ht : placeUses #[⟨d, .int, .use, .early, .reg⟩, ⟨n, .int, .use, .early, .reg⟩]
      (canonRegs #[⟨d, .int, .use, .early, .reg⟩, ⟨n, .int, .use, .early, .reg⟩])
      (useVals #[⟨d, .int, .use, .early, .reg⟩, ⟨n, .int, .use, .early, .reg⟩] #[.x n0, .x n1] s) w =
      Arm.w (.GPR 1#5) (Arm.r (.GPR (rnum n1)) s) (Arm.w (.GPR 0#5) (Arm.r (.GPR (rnum n0)) s) w) := by
    simp [placeUses, useVals, hcanon, Operand.isUse, lo64, regVal, rnum]
  rw [ht, hcanon] at hex hacc
  rw [hcanon]
  have hcore := store_core ctx env op hop fl hn0 (m := A (.x n1)) (mC := A (.x 1))
    (hA _ hn1.1) (hA 1 (by decide)) hal
    (SameWorld.w_right (by simp [Masked]) (SameWorld.w_right (by simp [Masked]) hw))
    (by rw [Arm.r_of_w_different (by simp), Arm.r_of_w_different (by simp)]
        exact sw_r_eq hw (by simp [Masked]))
    (by simp [rnum]) hacc hex (by rw [hg, hg]; simp [rnum])
  store_fin

theorem corr_store2 (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (op : StoreOp)
    (hop : op ≠ .fpuStore128) (d n m : Nat) (fl : Clif.MemFlags) (A : Reg → Reg → AMode)
    (g : BitVec 64 → BitVec 64 → BitVec 64)
    (hA : ∀ a b : Nat, a < 29 → b < 29 → MemMode op.bytes (A (.x a) (.x b)))
    (hg : ∀ (a b : Nat) s, (A (.x a) (.x b)).addr ctx op.bytes s =
      g (Arm.r (.GPR (rnum a)) s) (Arm.r (.GPR (rnum b)) s)) :
    Corr F ctx env #[⟨d, .int, .use, .early, .reg⟩, ⟨n, .int, .use, .early, .reg⟩,
      ⟨m, .int, .use, .early, .reg⟩]
      (fun r => .store op (r.getD 0 .xzr) (A (r.getD 1 .xzr) (r.getD 2 .xzr)) fl) := by
  intro regs s w t' ha hw hal hacc hex herr
  have hsz := ha.size
  simp only [List.size_toArray, List.length_cons, List.length_nil] at hsz
  have hf := ha.fits
  obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz
  simp [RegFits] at hf
  rcases hf with ⟨⟨n0, rfl, hn0⟩, ⟨n1, rfl, hn1⟩, ⟨n2, rfl, hn2⟩⟩
  have hcanon : canonRegs #[⟨d, .int, .use, .early, .reg⟩, ⟨n, .int, .use, .early, .reg⟩,
      ⟨m, .int, .use, .early, .reg⟩] = #[.x 0, .x 1, .x 2] := by
    simp [canonRegs, canonReg, canonBase, List.range_succ]
  have ht : placeUses #[⟨d, .int, .use, .early, .reg⟩, ⟨n, .int, .use, .early, .reg⟩,
      ⟨m, .int, .use, .early, .reg⟩]
      (canonRegs #[⟨d, .int, .use, .early, .reg⟩, ⟨n, .int, .use, .early, .reg⟩,
        ⟨m, .int, .use, .early, .reg⟩])
      (useVals #[⟨d, .int, .use, .early, .reg⟩, ⟨n, .int, .use, .early, .reg⟩,
        ⟨m, .int, .use, .early, .reg⟩] #[.x n0, .x n1, .x n2] s) w =
      Arm.w (.GPR 2#5) (Arm.r (.GPR (rnum n2)) s) (Arm.w (.GPR 1#5) (Arm.r (.GPR (rnum n1)) s)
        (Arm.w (.GPR 0#5) (Arm.r (.GPR (rnum n0)) s) w)) := by
    simp [placeUses, useVals, hcanon, Operand.isUse, lo64, regVal, rnum]
  rw [ht, hcanon] at hex hacc
  rw [hcanon]
  have hcore := store_core ctx env op hop fl hn0 (m := A (.x n1) (.x n2)) (mC := A (.x 1) (.x 2))
    (hA _ _ hn1.1 hn2.1) (hA 1 2 (by decide) (by decide)) hal
    (SameWorld.w_right (by simp [Masked]) (SameWorld.w_right (by simp [Masked])
      (SameWorld.w_right (by simp [Masked]) hw)))
    (by rw [Arm.r_of_w_different (by simp), Arm.r_of_w_different (by simp),
          Arm.r_of_w_different (by simp)]
        exact sw_r_eq hw (by simp [Masked]))
    (by simp [rnum]) hacc hex (by rw [hg, hg]; simp [rnum])
  store_fin

end Backend.Proof
