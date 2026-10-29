module

public import FV.Concurrency.IselMemAux

@[expose] public section

/-!
# Per-case facts about the LL/SC loop bodies (layer 4b's retry proof, T2 #311)

The `atomic_rmw` loop body (`rmwLoopBody`) and the `atomic_cas` loop head (`casLoopHead`) are
symbolically executed per access type and per operation: what they change (flags, x27), what
they leave alone, and their events (`linesEvs`); plus the classes and frame of the `ldaxr`/`stlxr`,
for the retry proofs of the LL/SC loops.
-/

namespace Concurrency.ArmLoop

open Arm ArmFoot ArmThread ArmInstFoot Backend Backend.Proof VCodeThread VCodeEvents Code VCodeAddr
  IselMemAux

attribute [local csimp_rules] wmb_cast Arm.LDST.exec_reg_exclusive Insn.armFields.exclFields
  CTy.bits Arm.r_of_write_mem_bytes Arm.ldst_read Arm.read_mem_bytes_of_w

attribute [local csimp_rules] dbm_sxtb dbm_sxth

/-- `sxtb w, w` (local copy of `LoopRun`'s private lemma). -/
theorem loop_exec_sxtb (Rn Rd : BitVec 5) (st : Arm.ArmState) :
    Arm.DPI.exec_bitfield (Arm.Bitfield_cls.mk 0#1 0#2 0b100110#6 0#1 0#6 7#6 Rn Rd) st =
      Arm.write_pc (Arm.read_pc (Arm.write_gpr_zr 32 Rd
          (((Arm.read_gpr_zr 32 Rn st).setWidth 8).signExtend 32) st) + 4#64)
        (Arm.write_gpr_zr 32 Rd (((Arm.read_gpr_zr 32 Rn st).setWidth 8).signExtend 32) st) := by
  unfold Arm.DPI.exec_bitfield
  simp (config := {decide := true}) only [dreduceIte, false_or, false_and, ite_false, dbm_sxtb]
  generalize Arm.read_gpr_zr 32 Rn st = v
  congr 4 <;>
  · refine BitVec.eq_of_getLsbD_eq ?_
    simp only [ite_true, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
      BitVec.getLsbD_cast, BitVec.getLsbD_replicate, Arm.BitVec.ror, Arm.BitVec.lsb,
      BitVec.getLsbD_rotateRight, BitVec.getLsbD_signExtend, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_extractLsb', BitVec.msb_eq_getLsbD_last]
    simp only [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, implies_true, true_and]
    simp [-BitVec.getLsbD_eq_getElem]

/-- `sxth w, w` (local copy of `LoopRun`'s private lemma). -/
theorem loop_exec_sxth (Rn Rd : BitVec 5) (st : Arm.ArmState) :
    Arm.DPI.exec_bitfield (Arm.Bitfield_cls.mk 0#1 0#2 0b100110#6 0#1 0#6 15#6 Rn Rd) st =
      Arm.write_pc (Arm.read_pc (Arm.write_gpr_zr 32 Rd
          (((Arm.read_gpr_zr 32 Rn st).setWidth 16).signExtend 32) st) + 4#64)
        (Arm.write_gpr_zr 32 Rd (((Arm.read_gpr_zr 32 Rn st).setWidth 16).signExtend 32) st) := by
  unfold Arm.DPI.exec_bitfield
  simp (config := {decide := true}) only [dreduceIte, false_or, false_and, ite_false, dbm_sxth]
  generalize Arm.read_gpr_zr 32 Rn st = v
  congr 4 <;>
  · refine BitVec.eq_of_getLsbD_eq ?_
    simp only [ite_true, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
      BitVec.getLsbD_cast, BitVec.getLsbD_replicate, Arm.BitVec.ror, Arm.BitVec.lsb,
      BitVec.getLsbD_rotateRight, BitVec.getLsbD_signExtend, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_extractLsb', BitVec.msb_eq_getLsbD_last]
    simp only [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, implies_true, true_and]
    simp [-BitVec.getLsbD_eq_getElem]

attribute [local csimp_rules ↓ high] loop_exec_sxtb loop_exec_sxth

/-- The `atomic_rmw` operations whose loop body sets the flags (the `subs` of `smin`…`umax`). -/
def FlagOp : AtomicRmwLoopOp → Bool
  | .smin | .smax | .umin | .umax => true
  | _ => false

set_option maxHeartbeats 4000000 in
/-- Without a comparison, the `atomic_rmw` loop body keeps the flags. -/
theorem rmwBody_keepFlags {ty : CTy} (hty : AtomTy ty) {op : AtomicRmwLoopOp} (hop : FlagOp op = false)
    (fl : Clif.MemFlags) (e : Env) {t t' : ArmState}
    (h : execLines e (rmwLoopBody ty.bits op fl) t = some t') :
    ∀ g, Arm.r (.FLAG g) t' = Arm.r (.FLAG g) t := by
  rcases hty with rfl | rfl | rfl | rfl <;> cases op <;> simp [FlagOp] at hop
  all_goals
    simp only [CTy.bits, rmwLoopBody, rmwLoopMid, rmwLoopStored, rmwLoopSext, rmwLoopCmp,
      List.map, List.cons_append, List.nil_append, List.singleton_append] at h
    simp (config := {decide := true}) [csimp_rules] at h
    subst h
    intro g; cases g <;> simp [Arm.r_of_w_different, Arm.r_of_write_mem_bytes]

set_option maxHeartbeats 8000000 in
/-- Two runs of the `atomic_rmw` loop body from states with the same address, operand and
loaded bytes (and, without a comparison, flags) end with the same flags and old value. -/
theorem rmwBody_dep {ty : CTy} (hty : AtomTy ty) (op : AtomicRmwLoopOp) (fl : Clif.MemFlags)
    (e1 e2 : Env) {t1 t2 t1' t2' : ArmState}
    (h25 : Arm.r (.GPR 25#5) t1 = Arm.r (.GPR 25#5) t2)
    (h26 : Arm.r (.GPR 26#5) t1 = Arm.r (.GPR 26#5) t2)
    (hrm : Arm.read_mem_bytes ty.bytes (Arm.r (.GPR 25#5) t2) t1 =
      Arm.read_mem_bytes ty.bytes (Arm.r (.GPR 25#5) t2) t2)
    (hfl : FlagOp op = false → ∀ g, Arm.r (.FLAG g) t1 = Arm.r (.FLAG g) t2)
    (h1 : execLines e1 (rmwLoopBody ty.bits op fl) t1 = some t1')
    (h2 : execLines e2 (rmwLoopBody ty.bits op fl) t2 = some t2') :
    (∀ g, Arm.r (.FLAG g) t1' = Arm.r (.FLAG g) t2') ∧
      Arm.r (.GPR 27#5) t1' = Arm.r (.GPR 27#5) t2' := by
  rcases hty with rfl | rfl | rfl | rfl <;> cases op
  all_goals
    dsimp only [CTy.bytes, CTy.bits, Nat.reduceDiv] at hrm
    simp only [FlagOp, forall_const] at hfl
    simp only [CTy.bits, rmwLoopBody, rmwLoopMid, rmwLoopStored, rmwLoopSext, rmwLoopCmp,
      List.map, List.cons_append, List.nil_append, List.singleton_append] at h1 h2
    simp (config := {decide := true}) [csimp_rules] at h1 h2
    subst h1 h2
    refine ⟨?_, by simp (config := {decide := true}) [Arm.r_of_w_different, Arm.r_of_write_mem_bytes,
      h25, h26, hrm]⟩
    intro g; cases g <;>
      simp (config := {decide := true}) [Arm.r_of_w_different, Arm.r_of_write_mem_bytes,
        h25, h26, hrm, hfl]

set_option maxHeartbeats 8000000 in
/-- The events of the `atomic_rmw` loop body: the `ldaxr`'s read of the old value at x25, then the
`stlxr`'s write of the new value there. -/
theorem rmwBody_evsEq {ty : CTy} (hty : AtomTy ty) (op : AtomicRmwLoopOp) (fl : Clif.MemFlags)
    (e : Env) (t : ArmState) (herr : Arm.r .ERR t = .None) :
    linesEvs e (rmwLoopBody ty.bits op fl) t =
      [⟨.acqXR, Arm.r (.GPR 25#5) t, ty.bytes, readM ty.bytes (Arm.r (.GPR 25#5) t) t.mem⟩,
       ⟨.relXW, Arm.r (.GPR 25#5) t, ty.bytes, rmwNew ty op t⟩] := by
  rcases hty with rfl | rfl | rfl | rfl <;> cases op
  all_goals
    simp only [CTy.bits, rmwLoopBody, rmwLoopMid, rmwLoopStored, rmwLoopSext, rmwLoopCmp,
      List.map, List.cons_append, List.nil_append]
    dsimp only [rmwNew, CTy.bytes, CTy.bits, Nat.reduceDiv, Nat.reduceMul]
    simp (config := {decide := true}) [csimp_rules, linesEvs, instEvs, exclEvs, herr]
    try simp only [BitVec.setWidth_eq, heq_eq_eq]
    try rmw_val

set_option maxHeartbeats 4000000 in
/-- Two runs of the `atomic_cas` loop head from states with the same address, expected value and
loaded bytes end with the same flags and old value. -/
theorem casHead_dep {ty : CTy} (hty : AtomTy ty) (fl : Clif.MemFlags) (e1 e2 : Env)
    {t1 t2 t1' t2' : ArmState}
    (h25 : Arm.r (.GPR 25#5) t1 = Arm.r (.GPR 25#5) t2)
    (h26 : Arm.r (.GPR 26#5) t1 = Arm.r (.GPR 26#5) t2)
    (hrm : Arm.read_mem_bytes ty.bytes (Arm.r (.GPR 25#5) t2) t1 =
      Arm.read_mem_bytes ty.bytes (Arm.r (.GPR 25#5) t2) t2)
    (h1 : execLines e1 (casLoopHead ty.bits fl) t1 = some t1')
    (h2 : execLines e2 (casLoopHead ty.bits fl) t2 = some t2') :
    (∀ g, Arm.r (.FLAG g) t1' = Arm.r (.FLAG g) t2') ∧
      Arm.r (.GPR 27#5) t1' = Arm.r (.GPR 27#5) t2' := by
  rcases hty with rfl | rfl | rfl | rfl
  all_goals
    dsimp only [CTy.bytes, CTy.bits, Nat.reduceDiv] at hrm
    simp only [CTy.bits, casLoopHead, casLoopCmp] at h1 h2
    simp (config := {decide := true}) [csimp_rules] at h1 h2
    subst h1 h2
    refine ⟨?_, by simp (config := {decide := true}) [Arm.r_of_w_different, h25, hrm]⟩
    intro g; cases g <;>
      simp (config := {decide := true}) [Arm.r_of_w_different, h25, h26, hrm]

set_option maxHeartbeats 4000000 in
/-- The `atomic_cas` loop's `stlxr` has one event: the release-exclusive write of x28's low bits
at x25. -/
theorem casStore_evsEq {ty : CTy} (hty : AtomTy ty) (fl : Clif.MemFlags) (e : Env) (t : ArmState) :
    linesEvs e (casStore ty.bits fl) t =
      [⟨.relXW, Arm.r (.GPR 25#5) t, ty.bytes, (Arm.r (.GPR 28#5) t).setWidth (ty.bytes * 8)⟩] := by
  rcases hty with rfl | rfl | rfl | rfl <;>
  · simp (config := {decide := true}) [casStore, csimp_rules, linesEvs, instEvs, exclEvs, CTy.bytes]
    try simp only [BitVec.setWidth_eq, heq_eq_eq]

set_option maxHeartbeats 4000000 in
theorem ldaxr_cls {ty : CTy} (hty : AtomTy ty) {env : Env} {ai : ArmInst}
    (ha : (Insn.ldaxr ty.bits (.x 27) (.x 25)).toArmInst env = .ok ai) :
    ∃ sz, clsOf ai = .ldx true 25#5 sz := by
  rcases hty with rfl | rfl | rfl | rfl <;>
  · simp (config := {decide := true}) [csimp_rules] at ha
    subst ha
    simp (config := {decide := true}) [clsOf, exclCls]

set_option maxHeartbeats 4000000 in
theorem stlxr_cls {ty : CTy} (hty : AtomTy ty) {env : Env} {rs : Reg} {ai : ArmInst}
    (hrs : rs = .x 26 ∨ rs = .x 28)
    (ha : (Insn.stlxr ty.bits (.x 24) rs (.x 25)).toArmInst env = .ok ai) :
    clsOf ai = .stx true 24#5 25#5 := by
  rcases hty with rfl | rfl | rfl | rfl <;> rcases hrs with rfl | rfl <;>
  · simp (config := {decide := true}) [csimp_rules] at ha
    subst ha
    simp (config := {decide := true}) [clsOf, exclCls]

set_option maxHeartbeats 4000000 in
/-- The `stlxr` changes only the pc and the status register (and memory). -/
theorem stlxr_frame {ty : CTy} (hty : AtomTy ty) {env : Env} {rs : Reg} {ai : ArmInst}
    (hrs : rs = .x 26 ∨ rs = .x 28)
    (ha : (Insn.stlxr ty.bits (.x 24) rs (.x 25)).toArmInst env = .ok ai) (s : ArmState)
    (herr : Arm.r .ERR s = .None) :
    ∀ f, f ≠ .PC → f ≠ .GPR 24#5 → Arm.r f (Arm.exec_inst ai s) = Arm.r f s := by
  rcases hty with rfl | rfl | rfl | rfl <;> rcases hrs with rfl | rfl <;>
  · simp (config := {decide := true}) [csimp_rules] at ha
    subst ha
    intro f h1 h2
    simp (config := {decide := true}) [csimp_rules, Arm.r_of_w_different, Arm.r_of_write_mem_bytes, *]

end Concurrency.ArmLoop
