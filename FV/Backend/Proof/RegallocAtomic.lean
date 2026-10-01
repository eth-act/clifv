import FV.Backend.Proof.RegallocMemOS

/-!
# `OperandsSound` for `csetm`, `dmb ish`, `ldar` and `stlr` (M6 proof)

The `Corr` facts of the forms `bmask`, `fence`, `atomic_load` and `atomic_store` lower to, by
`corr_tac` (`csetm`), a direct run (`dmb ish`: no operands) and `atom_pre`/`atom_tail` (`ldar`,
`stlr`: one access at the address register, which avoids the frame addresses `F`). In the
single-threaded Arm model `ldar`/`stlr` are a plain load/store and `dmb` only advances the pc
(`docs/decisions/arm-model.md`).
-/

namespace Backend.Proof

open Backend

theorem setWidth_cast' {n m k : Nat} (h : n = m) (x : BitVec n) :
    (x.cast h).setWidth k = x.setWidth k := by
  subst h; rfl

theorem wmb_cast {n m : Nat} (h : m = n * 8) (a : BitVec 64) (x : BitVec m) (s : Arm.ArmState) :
    Arm.write_mem_bytes n a (x.cast h) s = Arm.write_mem_bytes n a (x.setWidth (n * 8)) s := by
  subst h; simp

theorem sw_wmb_cast {F : BitVec 64 → Prop} {s t : Arm.ArmState} {n m : Nat} (h : m = n * 8)
    (a : BitVec 64) (x : BitVec m) (y : BitVec (n * 8)) (hxy : x.toNat = y.toNat)
    (hst : SameWorld F s t) :
    SameWorld F (Arm.write_mem_bytes n a (x.cast h) s) (Arm.write_mem_bytes n a y t) := by
  subst h
  have : x = y := BitVec.eq_of_toNat_eq hxy
  subst this
  exact SameWorld.write_mem_bytes hst n a _

attribute [local csimp_rules] wmb_cast Arm.BR.exec_barrier Arm.LDST.exec_reg_exclusive
  Insn.armFields.exclFields CTy.bits Arm.r_of_write_mem_bytes Arm.ldst_read Arm.read_mem_bytes_of_w

/-- `sw_tac`, also matching equal stored values up to a width cast (`rfl`). -/
syntax "sw_tac_c" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| sw_tac_c) => `(tactic| repeat (first
    | assumption
    | contradiction
    | (refine SameWorld.ite_both (fun _ => ?_) (fun _ => ?_))
    | (refine SameWorld.w_left ?_ ?_; · (simp [Masked]; try omega))
    | (refine SameWorld.w_right ?_ ?_; · (simp [Masked]; try omega))
    | (refine SameWorld.w_both' ?_ ?_; · veq_tac)
    | (refine sw_wmb_cast ?hc _ _ _ (by simp [BitVec.toNat_cast]) ?_; case hc => rfl)
    | (refine SameWorld.write_mem_bytes' ?_ ?_ ?_
       · first | (apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_cast]; done) | veq_tac
       · first | (apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_cast]; done) | veq_tac)
    | simp only [*]))

/-- The prelude of an `ldar`/`stlr` `Corr` proof: the allocation (`x n0` the address, `x n1`
the other operand), the canonical placement, and the access avoiding `F` (`hacc`). -/
syntax "atom_pre" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| atom_pre) => `(tactic| (
    intro regs s w t' ha hw _hal hacc hex herr
    have hsz := ha.size
    simp only [List.size_toArray, List.length_cons, List.length_nil] at hsz
    have hf := ha.fits
    obtain ⟨r0, r1, rfl⟩ := regs2 hsz
    simp [RegFits] at hf
    rcases hf with ⟨⟨n0, rfl, hn0⟩, ⟨n1, rfl, hn1⟩⟩
    have hfl : ∀ f, Arm.r (.FLAG f) w = Arm.r (.FLAG f) s :=
      fun f => (hw.1 (.FLAG f) (by simp [Masked])).symm
    have hsp : Arm.r (.GPR 31#5) w = Arm.r (.GPR 31#5) s :=
      (hw.1 (.GPR 31#5) (by simp [Masked])).symm
    have e0 := ne31_of hn0.1
    have e1 := ne31_of hn1.1
    have e0' := ne31_of' hn0.1
    have e1' := ne31_of' hn1.1
    have l0 := le30_of hn0.1
    have l1 := le30_of hn1.1
    simp only [canonRegs, canonReg, canonBase, List.size_toArray, List.length_cons,
      List.length_nil, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
      List.map_cons, List.map_nil, List.getElem?_toArray, List.getElem?_cons_zero,
      List.getElem?_cons_succ] at hex hacc ⊢
    simp [AccessOk, MInst.accesses, placeUses, useVals, Operand.isUse, regX, regVal, setReg,
      lo64, csimp_rules] at hacc))

/-- The rest of an `ldar`/`stlr` `Corr` proof at a concrete access type: both runs computed
and matched (`hrm`: the bytes read agree on both worlds). -/
syntax "atom_tail" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| atom_tail) => `(tactic| (
    simp only [CTy.bytes, CTy.bits, Nat.reduceDiv] at hacc
    have hrm := read_mem_bytes_congr (s := s) (t := w) _ _ (fun k hk => hw.2.1 _ (hacc k hk))
    generalize hA : execMInst ctx env _ s = oa
    simp (config := {decide := true}) [csimp_rules, hsp, *] at hex hA
    all_goals (repeat' (first
      | subst hex
      | (split at hex <;> try simp (config := {decide := true}) [csimp_rules, *] at hex hA)))
    all_goals subst hA
    all_goals (try simp (config := {decide := true}) [csimp_rules] at herr)
    all_goals (repeat' (split at herr <;>
      try simp (config := {decide := true}) [csimp_rules, *] at herr))
    all_goals (
      refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
      · sw_tac_c
      · refine ⟨?_, fun a ha => ?_⟩
        · simp (config := {decide := true}) [csimp_rules, *]
        · first
            | (simp [csimp_rules, Arm.ArmState.mem_w_eq_mem, *]; done)
            | (simp only [Arm.ArmState.mem_w_eq_mem]
               exact mem_write_mem_bytes_ne _ _ _ _ _ (fun k hk e => hacc k hk (e ▸ ha)))
      · first
          | (simp (config := {decide := true}) [csimp_rules, *]; done)
          | (simp (config := {decide := true}) [csimp_rules, *]
             first | rfl | (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_cast]))
      · intro r hr hnd
        rcases allocatable_cases hr with ⟨k, rfl, hk⟩|⟨k, rfl, hk⟩
        · try simp [Operand.isDef] at hnd
          try have hnd' := Ne.symm hnd
          simp (config := {decide := true}) (disch := omega) [csimp_rules, ofNat5_eq_iff, *]
        · try simp [Operand.isDef] at hnd
          try have hnd' := Ne.symm hnd
          simp (config := {decide := true}) (disch := omega) [csimp_rules, ofNat5_eq_iff, *])))

set_option maxHeartbeats 4000000 in
theorem corr_loadAcquire (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (ty : CTy)
    (hty : AtomTy ty) (fl : Clif.MemFlags) (d a : Nat) :
    Corr F ctx env #[⟨a, .int, .use, .early, .reg⟩, ⟨d, .int, .def, .late, .reg⟩]
      (fun r => .loadAcquire ty (r.getD 1 .xzr) (r.getD 0 .xzr) fl) := by
  atom_pre
  rcases hty with rfl | rfl | rfl | rfl <;> atom_tail

set_option maxHeartbeats 40000000 in
theorem corr_storeRelease (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (ty : CTy)
    (hty : AtomTy ty) (fl : Clif.MemFlags) (x a : Nat) :
    Corr F ctx env #[⟨a, .int, .use, .early, .reg⟩, ⟨x, .int, .use, .early, .reg⟩]
      (fun r => .storeRelease ty (r.getD 1 .xzr) (r.getD 0 .xzr) fl) := by
  atom_pre
  rcases hty with rfl | rfl | rfl | rfl <;> atom_tail

set_option maxHeartbeats 4000000 in
theorem corr_csetm (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (c : Cond) (d : Nat) :
    Corr F ctx env #[⟨d, .int, .def, .late, .reg⟩] (fun r => .csetm (r.getD 0 .xzr) c) := by
  cases c <;> corr_tac

set_option maxHeartbeats 4000000 in
theorem corr_fence (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) :
    Corr F ctx env #[] (fun _ => .fence) := by
  intro regs s w t' ha hw _hal hacc hex herr
  have hsz := ha.size
  obtain rfl : regs = #[] := by
    rcases regs with ⟨_ | _⟩ <;> simp at hsz ⊢
  simp only [canonRegs, List.size_toArray, List.length_nil, List.range_zero] at hex hacc ⊢
  generalize hA : execMInst ctx env _ s = oa
  simp (config := {decide := true}) [csimp_rules, *] at hex hA
  all_goals (repeat' (first
    | subst hex
    | (split at hex <;> try simp (config := {decide := true}) [csimp_rules, *] at hex hA)))
  all_goals subst hA
  all_goals (try simp (config := {decide := true}) [csimp_rules] at herr)
  refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
  · sw_tac
  · refine ⟨?_, fun a _ => ?_⟩
    · simp (config := {decide := true}) [csimp_rules, *]
    · simp [csimp_rules, Arm.ArmState.mem_w_eq_mem, *]
  · simp [defVals]
  · intro r hr _
    rcases allocatable_cases hr with ⟨k, rfl, hk⟩|⟨k, rfl, hk⟩ <;>
      simp (config := {decide := true}) [csimp_rules, *]

variable (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (X : ExtSem)

theorem os_csetm (c : Cond) (d : Nat) :
    OperandsSound F (execMInst ctx env) (csem F ctx X) (.csetm (.vreg d .int) c) :=
  os_of_corr rfl _ (by assign_tac) rfl rfl rfl (corr_csetm F ctx env c d)

theorem os_fence : OperandsSound F (execMInst ctx env) (csem F ctx X) .fence :=
  os_of_corr rfl (fun _ => .fence)
    (fun regs h => by rcases regs with ⟨_ | _⟩ <;> simp at h; rfl) rfl rfl rfl (corr_fence F ctx env)

theorem os_loadAcquire (ty : CTy) (hty : AtomTy ty) (fl : Clif.MemFlags) (d a : Nat) :
    OperandsSound F (execMInst ctx env) (csem F ctx X)
      (.loadAcquire ty (.vreg d .int) (.vreg a .int) fl) :=
  os_of_corr rfl _ (by assign_tac) (by simp [FormOk, hty]) rfl rfl
    (corr_loadAcquire F ctx env ty hty fl d a)

theorem os_storeRelease (ty : CTy) (hty : AtomTy ty) (fl : Clif.MemFlags) (x a : Nat) :
    OperandsSound F (execMInst ctx env) (csem F ctx X)
      (.storeRelease ty (.vreg x .int) (.vreg a .int) fl) :=
  os_of_corr rfl _ (by assign_tac) (by simp [FormOk, hty]) rfl rfl
    (corr_storeRelease F ctx env ty hty fl x a)

end Backend.Proof
