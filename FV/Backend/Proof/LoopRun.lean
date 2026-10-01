import FV.Backend.Proof.RegallocAtomic

/-!
# Runs of the LL/SC loop bodies (M6 proof)

The bodies of the `atomic_rmw` and `atomic_cas` loops (`rmwLoopBody`, `casLoopHead`, the CAS
`stlxr`) run on any error-free state, computed with `simp` per access type and operation:

* `rmwBody_spec`: `ldaxr x27, [x25]; …; stlxr w24, …, [x25]` loads the old value into x27,
  writes `atomic_rmw`'s new value (`Clif.Sem.atomicRmw`) of the old value and x26's low bits
  at x25, writes status 0 to w24 (the single-threaded Arm model: the exclusive store
  succeeds), and changes no other field but the pc, x28 and the flags;
* `casHead_spec`: `ldaxr x27, [x25]; cmp …` loads the old value and sets the flags so that `ne`
  holds iff the old value differs from x26's low bits (`casLoopCmp`);
* `stlxr_spec`: the store of x28's low bits at x25, status 0 in w24;
* `*_congr`: the same lines run on two states with the same world (`SameWorld F`), the same
  use registers and an access avoiding `F` give states with the same world.

These are the meaning `csem` gives the loops (`loopSem`) and the machine's run of them
(`RegLevelAtomic`).
-/

namespace Backend.Proof

open Backend

attribute [local csimp_rules] wmb_cast Arm.LDST.exec_reg_exclusive Insn.armFields.exclFields
  CTy.bits Arm.r_of_write_mem_bytes Arm.ldst_read Arm.read_mem_bytes_of_w

/-- The `decode_bit_masks` of `sxtb`/`sxth` (`sbfm w27, w27, #0, #7`/`#15`). -/
theorem dbm_sxtb : Arm.decode_bit_masks 0#1 7#6 0#6 false 32 = some (255#32, 255#32) := by
  native_decide
theorem dbm_sxth : Arm.decode_bit_masks 0#1 15#6 0#6 false 32 = some (65535#32, 65535#32) := by
  native_decide

attribute [local csimp_rules] dbm_sxtb dbm_sxth

/-- The fields an LL/SC body leaves alone: all but the pc, the given registers and the flags. -/
def LoopFrame (rs : List (BitVec 5)) (t t' : Arm.ArmState) : Prop :=
  ∀ f, f ≠ .PC → (∀ r ∈ rs, f ≠ .GPR r) → (∀ g, f ≠ .FLAG g) → Arm.r f t' = Arm.r f t

/-- The states between the lines of a run are error-free and keep the program (`InterOk` of
the machine-level proofs). -/
def LinesInterOk (e : Env) (ls : List Line) (t : Arm.ArmState) : Prop :=
  ∀ k, 0 < k → k < ls.length → ∀ s1, execLines e (ls.take k) t = some s1 →
    Arm.r .ERR s1 = .None ∧ s1.program = t.program

/-- The new value `atomic_rmw` stores. -/
def rmwNew (ty : CTy) (op : AtomicRmwLoopOp) (t : Arm.ArmState) : BitVec (ty.bytes * 8) :=
  Clif.Sem.atomicRmw op.clif (Arm.read_mem_bytes ty.bytes (Arm.r (.GPR 25#5) t) t)
    ((Arm.r (.GPR 26#5) t).setWidth (ty.bytes * 8))

/-! ## The operand extensions of the comparisons -/

theorem ext_sxtb32 (x : BitVec 32) :
    Arm.extend_reg x (Arm.decode_reg_extend ExtendOp.sxtb.bits) 0 = (x.setWidth 8).signExtend 32 := by
  show (BitVec.signExtend 32 (BitVec.extractLsb' 0 8 x)) <<< 0 = _
  bv_decide
theorem ext_sxth32 (x : BitVec 32) :
    Arm.extend_reg x (Arm.decode_reg_extend ExtendOp.sxth.bits) 0 = (x.setWidth 16).signExtend 32 := by
  show (BitVec.signExtend 32 (BitVec.extractLsb' 0 16 x)) <<< 0 = _
  bv_decide
theorem ext_uxtb32 (x : BitVec 32) :
    Arm.extend_reg x (Arm.decode_reg_extend ExtendOp.uxtb.bits) 0 = (x.setWidth 8).setWidth 32 := by
  show (BitVec.setWidth 32 (BitVec.extractLsb' 0 8 x)) <<< 0 = _
  bv_decide
theorem ext_uxth32 (x : BitVec 32) :
    Arm.extend_reg x (Arm.decode_reg_extend ExtendOp.uxth.bits) 0 = (x.setWidth 16).setWidth 32 := by
  show (BitVec.setWidth 32 (BitVec.extractLsb' 0 16 x)) <<< 0 = _
  bv_decide
theorem ext_uxtb64 (x : BitVec 64) :
    Arm.extend_reg x (Arm.decode_reg_extend ExtendOp.uxtb.bits) 0 = (x.setWidth 8).setWidth 64 := by
  show (BitVec.setWidth 64 (BitVec.extractLsb' 0 8 x)) <<< 0 = _
  bv_decide
theorem ext_uxth64 (x : BitVec 64) :
    Arm.extend_reg x (Arm.decode_reg_extend ExtendOp.uxth.bits) 0 = (x.setWidth 16).setWidth 64 := by
  show (BitVec.setWidth 64 (BitVec.extractLsb' 0 16 x)) <<< 0 = _
  bv_decide
theorem ext_uxtw64 (x : BitVec 64) :
    Arm.extend_reg x (Arm.decode_reg_extend ExtendOp.uxtw.bits) 0 = (x.setWidth 32).setWidth 64 := by
  show (BitVec.setWidth 64 (BitVec.extractLsb' 0 32 x)) <<< 0 = _
  bv_decide

/-- Abstract the old value and the operand of a run on `t` as plain bit vectors (`bv_decide`
needs literal widths and non-dependent types). -/
syntax "loop_atoms" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| loop_atoms) => `(tactic| (
    try (first
      | (obtain ⟨m, hm⟩ : ∃ m : BitVec 8, Arm.read_mem_bytes 1 (Arm.r (.GPR 25#5) t) t = m :=
          ⟨_, rfl⟩
         rw [hm]; clear hm)
      | (obtain ⟨m, hm⟩ : ∃ m : BitVec 16, Arm.read_mem_bytes 2 (Arm.r (.GPR 25#5) t) t = m :=
          ⟨_, rfl⟩
         rw [hm]; clear hm)
      | (obtain ⟨m, hm⟩ : ∃ m : BitVec 32, Arm.read_mem_bytes 4 (Arm.r (.GPR 25#5) t) t = m :=
          ⟨_, rfl⟩
         rw [hm]; clear hm)
      | (obtain ⟨m, hm⟩ : ∃ m : BitVec 64, Arm.read_mem_bytes 8 (Arm.r (.GPR 25#5) t) t = m :=
          ⟨_, rfl⟩
         rw [hm]; clear hm))
    try (obtain ⟨xv, hxv⟩ : ∃ xv : BitVec 64, Arm.r (.GPR 26#5) t = xv := ⟨_, rfl⟩
         rw [hxv]; clear hxv)))

/-- The value proof of a body run: after `simp`, the stored value is `rmwNew`. -/
syntax "rmw_val" : tactic
macro_rules
  | `(tactic| rmw_val) => `(tactic| (
    simp only [AtomicRmwLoopOp.clif, Clif.Sem.atomicRmw, Clif.Sem.smin, Clif.Sem.smax,
      Clif.Sem.umin, Clif.Sem.umax, Arm.AddWithCarry, Arm.make_pstate, BitVec.zero_eq,
      ext_sxtb32, ext_sxth32, ext_uxtb32, ext_uxth32, ext_uxtb64, ext_uxth64, ext_uxtw64]
    loop_atoms
    bv_decide))

set_option maxHeartbeats 4000000 in
/-- **The `atomic_rmw` loop body** on an error-free state. -/
theorem rmwBody_spec {ty : CTy} (hty : AtomTy ty) (op : AtomicRmwLoopOp) (fl : Clif.MemFlags)
    (e : Env) (t : Arm.ArmState) (herr : Arm.r .ERR t = .None) :
    ∃ t', execLines e (rmwLoopBody ty.bits op fl) t = some t' ∧
      LinesInterOk e (rmwLoopBody ty.bits op fl) t ∧
      (Arm.r (.GPR 27#5) t').setWidth (ty.bytes * 8) =
        Arm.read_mem_bytes ty.bytes (Arm.r (.GPR 25#5) t) t ∧
      Arm.r (.GPR 24#5) t' = 0#64 ∧ LoopFrame [24#5, 27#5, 28#5] t t' ∧
      t'.mem = (Arm.write_mem_bytes ty.bytes (Arm.r (.GPR 25#5) t) (rmwNew ty op t) t).mem ∧
      t'.program = t.program := by
  rcases hty with rfl | rfl | rfl | rfl <;> cases op
  all_goals
    simp only [CTy.bits, rmwLoopBody, rmwLoopMid, rmwLoopStored, rmwLoopSext, rmwLoopCmp,
      List.map, List.cons_append, List.nil_append, List.singleton_append]
    generalize hT : execLines e _ t = ot
    simp (config := {decide := true}) [csimp_rules] at hT
    subst hT
    refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro k hk0 hk s1 hs1
      simp only [List.length_cons, List.length_nil] at hk
      rcases (by omega : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with rfl | rfl | rfl | rfl <;>
        (try omega) <;> simp (config := {decide := true}) [csimp_rules, List.take] at hs1 <;>
        subst hs1 <;> simp [herr, Arm.w_program, Arm.write_mem_bytes_program]
    · dsimp only [CTy.bytes, CTy.bits, Nat.reduceDiv, Nat.reduceMul]
      simp (config := {decide := true}) [csimp_rules]
      try (loop_atoms; bv_decide)
    · simp (config := {decide := true}) [csimp_rules]
    · intro f h1 h2 h3
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h2
      obtain ⟨h24, h27, h28⟩ := h2
      have := h3 .N; have := h3 .Z; have := h3 .C; have := h3 .V
      simp [Arm.r_of_w_different, Arm.r_of_write_mem_bytes, *]
    · simp only [Arm.ArmState.mem_w_eq_mem]
      refine (Arm.mem_write_mem_bytes_of_mem_eq (s₂ := t) ?_ _ _ _).trans ?_
      · simp [Arm.ArmState.mem_w_eq_mem]
      dsimp only [rmwNew, CTy.bytes, CTy.bits, Nat.reduceDiv, Nat.reduceMul]
      congr 2 <;> rmw_val
    · simp [Arm.w_program, Arm.write_mem_bytes_program]

/-- The bytes an access avoiding `F` reads agree on two states with the same world. -/
theorem read_avoid {F : BitVec 64 → Prop} {s w : Arm.ArmState} (hsw : SameWorld F s w) {n : Nat}
    {a : BitVec 64} (hav : Avoids F n a) : Arm.read_mem_bytes n a s = Arm.read_mem_bytes n a w :=
  read_mem_bytes_congr _ _ (fun k hk => hsw.2.1 _ (hav k hk))

/-- Two runs of the same lines, their use registers and loaded bytes rewritten to agree: strip
the masked writes (registers, pc) from either side and match the equal writes (flags, memory).
Unification is reducible-only, so a mismatch fails fast. -/
syntax "lsw_tac" : tactic
macro_rules
  | `(tactic| lsw_tac) => `(tactic| repeat (first
    | assumption
    | (with_reducible refine SameWorld.write_mem_bytes' rfl rfl ?_)
    | (with_reducible refine SameWorld.w_left ?_ ?_; · simp [Masked])
    | (with_reducible refine SameWorld.w_right ?_ ?_; · simp [Masked])
    | (with_reducible refine SameWorld.w_both ?_)))

set_option maxHeartbeats 8000000 in
/-- **The `atomic_rmw` loop body on two states with the same world**, the same address and
operand registers, and an access avoiding `F`: the same world after, the same old value. -/
theorem rmwBody_congr {F : BitVec 64 → Prop} {ty : CTy} (hty : AtomTy ty) (op : AtomicRmwLoopOp)
    (fl : Clif.MemFlags) (e1 e2 : Env) {s w s' w' : Arm.ArmState} (hsw : SameWorld F s w)
    (h25 : Arm.r (.GPR 25#5) s = Arm.r (.GPR 25#5) w)
    (h26 : Arm.r (.GPR 26#5) s = Arm.r (.GPR 26#5) w)
    (hav : Avoids F ty.bytes (Arm.r (.GPR 25#5) w))
    (hs : execLines e1 (rmwLoopBody ty.bits op fl) s = some s')
    (hw : execLines e2 (rmwLoopBody ty.bits op fl) w = some w') :
    SameWorld F s' w' ∧ Arm.r (.GPR 27#5) s' = Arm.r (.GPR 27#5) w' := by
  have hrm := read_avoid hsw hav
  have hfl : ∀ f, Arm.r (.FLAG f) s = Arm.r (.FLAG f) w := fun f => hsw.1 (.FLAG f) (by simp [Masked])
  rcases hty with rfl | rfl | rfl | rfl <;> cases op
  all_goals
    dsimp only [CTy.bytes, CTy.bits, Nat.reduceDiv] at hrm hav
    simp only [CTy.bits, rmwLoopBody, rmwLoopMid, rmwLoopStored, rmwLoopSext, rmwLoopCmp,
      List.map, List.cons_append, List.nil_append, List.singleton_append] at hs hw
    simp (config := {decide := true}) [csimp_rules] at hs hw
    subst hs hw
    refine ⟨?_, by simp (config := {decide := true}) [Arm.r_of_w_different, Arm.r_of_write_mem_bytes,
      h25, h26, hrm]⟩
    simp only [h25, h26, hrm]
    lsw_tac

/-! ## The `atomic_cas` loop -/

theorem condHolds_ne_iff (t : Arm.ArmState) :
    Arm.ConditionHolds Cond.ne.bits t = true ↔ Arm.r (.FLAG .Z) t ≠ 1#1 := by
  rcases bv1_cases (Arm.r (.FLAG .Z) t) with h | h <;>
    simp (config := {decide := true}) [Arm.ConditionHolds, Arm.read_flag, Cond.bits, h]

set_option maxHeartbeats 4000000 in
/-- **The head of the `atomic_cas` loop** (`ldaxr x27, [x25]; cmp …`) on an error-free state:
`ne` holds iff the old value differs from x26's low bits. -/
theorem casHead_spec {ty : CTy} (hty : AtomTy ty) (fl : Clif.MemFlags) (e : Env)
    (t : Arm.ArmState) (herr : Arm.r .ERR t = .None) :
    ∃ t', execLines e (casLoopHead ty.bits fl) t = some t' ∧
      LinesInterOk e (casLoopHead ty.bits fl) t ∧
      Arm.r (.GPR 27#5) t' = (Arm.read_mem_bytes ty.bytes (Arm.r (.GPR 25#5) t) t).setWidth 64 ∧
      LoopFrame [27#5] t t' ∧ t'.mem = t.mem ∧ t'.program = t.program ∧
      (Arm.ConditionHolds Cond.ne.bits t' = true ↔
        Arm.read_mem_bytes ty.bytes (Arm.r (.GPR 25#5) t) t ≠
          (Arm.r (.GPR 26#5) t).setWidth (ty.bytes * 8)) := by
  rcases hty with rfl | rfl | rfl | rfl
  all_goals
    simp only [CTy.bits, casLoopHead, casLoopCmp]
    generalize hT : execLines e _ t = ot
    simp (config := {decide := true}) [csimp_rules] at hT
    subst hT
    refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro k hk0 hk s1 hs1
      simp only [List.length_cons, List.length_nil] at hk
      obtain rfl : k = 1 := by omega
      simp (config := {decide := true}) [csimp_rules, List.take] at hs1
      subst hs1; simp [herr, Arm.w_program]
    · simp (config := {decide := true}) [csimp_rules, CTy.bytes]
    · intro f h1 h2 h3
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h2
      have := h3 .N; have := h3 .Z; have := h3 .C; have := h3 .V
      simp [Arm.r_of_w_different, *]
    · simp [Arm.ArmState.mem_w_eq_mem]
    · simp [Arm.w_program]
    · rw [condHolds_ne_iff]
      dsimp only [CTy.bytes, CTy.bits, Nat.reduceDiv, Nat.reduceMul]
      simp (config := {decide := true}) [Arm.r_of_w_different, Arm.AddWithCarry, Arm.make_pstate,
        BitVec.zero_eq, ext_uxtb64, ext_uxth64, ext_uxtw64]
      loop_atoms
      bv_decide

set_option maxHeartbeats 4000000 in
/-- **The `atomic_cas` loop's `stlxr`** on an error-free state: x28's low bits stored at x25,
status 0 in w24. -/
theorem stlxr_spec {ty : CTy} (hty : AtomTy ty) (fl : Clif.MemFlags) (e : Env)
    (t : Arm.ArmState) (herr : Arm.r .ERR t = .None) :
    ∃ t', execLines e [.ins (.stlxr ty.bits (.x 24) (.x 28) (.x 25)) fl.trapCode] t = some t' ∧
      Arm.r (.GPR 24#5) t' = 0#64 ∧
      (∀ f, f ≠ .PC → f ≠ .GPR 24#5 → Arm.r f t' = Arm.r f t) ∧
      t'.mem = (Arm.write_mem_bytes ty.bytes (Arm.r (.GPR 25#5) t)
        ((Arm.r (.GPR 28#5) t).setWidth (ty.bytes * 8)) t).mem ∧
      t'.program = t.program := by
  rcases hty with rfl | rfl | rfl | rfl
  all_goals
    simp only [CTy.bits]
    generalize hT : execLines e _ t = ot
    simp (config := {decide := true}) [csimp_rules] at hT
    subst hT
    refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
    · simp (config := {decide := true}) [csimp_rules]
    · intro f h1 h2
      simp [Arm.r_of_w_different, Arm.r_of_write_mem_bytes, *]
    · simp only [Arm.ArmState.mem_w_eq_mem]
      dsimp only [CTy.bytes, CTy.bits, Nat.reduceDiv, Nat.reduceMul]
      try simp only [BitVec.setWidth_eq]
    · simp [Arm.w_program, Arm.write_mem_bytes_program]

set_option maxHeartbeats 4000000 in
/-- **The head of the `atomic_cas` loop on two states with the same world.** -/
theorem casHead_congr {F : BitVec 64 → Prop} {ty : CTy} (hty : AtomTy ty) (fl : Clif.MemFlags)
    (e1 e2 : Env) {s w s' w' : Arm.ArmState} (hsw : SameWorld F s w)
    (h25 : Arm.r (.GPR 25#5) s = Arm.r (.GPR 25#5) w)
    (h26 : Arm.r (.GPR 26#5) s = Arm.r (.GPR 26#5) w)
    (hav : Avoids F ty.bytes (Arm.r (.GPR 25#5) w))
    (hs : execLines e1 (casLoopHead ty.bits fl) s = some s')
    (hw : execLines e2 (casLoopHead ty.bits fl) w = some w') :
    SameWorld F s' w' ∧ Arm.r (.GPR 27#5) s' = Arm.r (.GPR 27#5) w' := by
  have hrm := read_avoid hsw hav
  rcases hty with rfl | rfl | rfl | rfl
  all_goals
    dsimp only [CTy.bytes, CTy.bits, Nat.reduceDiv] at hrm hav
    simp only [CTy.bits, casLoopHead, casLoopCmp] at hs hw
    simp (config := {decide := true}) [csimp_rules] at hs hw
    subst hs hw
    refine ⟨?_, by simp (config := {decide := true}) [Arm.r_of_w_different, h25, hrm]⟩
    simp only [h25, h26, hrm]
    lsw_tac

set_option maxHeartbeats 4000000 in
/-- **The `atomic_cas` loop's `stlxr` on two states with the same world.** -/
theorem stlxr_congr {F : BitVec 64 → Prop} {ty : CTy} (hty : AtomTy ty) (fl : Clif.MemFlags)
    (e1 e2 : Env) {s w s' w' : Arm.ArmState} (hsw : SameWorld F s w)
    (h25 : Arm.r (.GPR 25#5) s = Arm.r (.GPR 25#5) w)
    (h28 : Arm.r (.GPR 28#5) s = Arm.r (.GPR 28#5) w)
    (hs : execLines e1 [.ins (.stlxr ty.bits (.x 24) (.x 28) (.x 25)) fl.trapCode] s = some s')
    (hw : execLines e2 [.ins (.stlxr ty.bits (.x 24) (.x 28) (.x 25)) fl.trapCode] w = some w') :
    SameWorld F s' w' := by
  rcases hty with rfl | rfl | rfl | rfl
  all_goals
    simp only [CTy.bits] at hs hw
    simp (config := {decide := true}) [csimp_rules] at hs hw
    subst hs hw
    simp only [h25, h28]
    lsw_tac

end Backend.Proof
