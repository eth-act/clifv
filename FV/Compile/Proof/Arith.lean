import FV.Compile.Proof.Prims

/-!
# Instruction semantics on encoded DSL scalars
-/

set_option autoImplicit false

namespace Compile.Proof

open Compile
open Clif (Val Regs ValueId Frame Mem Inst evalInst)
open DSL (Ty IntW)

theorem intV_eq (w : IntW) (x : BitVec w.bits) :
    intV w x = ⟨intTy w, BitVec.ofNat (intTy w).width x.toNat⟩ := rfl

theorem ofBool_eq (b : Bool) : Val.ofBool b = ⟨.i8, BitVec.ofNat 8 (if b then 1 else 0)⟩ := by
  cases b <;> rfl

theorem eval_binary (fr : Frame) (mem : Mem) (op : Clif.BinaryOp) (ty : Clif.Ty) {x y : ValueId}
    {A B : BitVec ty.width} (hx : fr.regs x = some ⟨ty, A⟩) (hy : fr.regs y = some ⟨ty, B⟩)
    (hs : op.isShift = false) :
    evalInst fr mem (.binary op ty x y) = .ok ([⟨ty, Clif.Sem.binary op A B⟩], mem) := by
  simp [evalInst, getAs_of hx, getAs_of hy, hs]

theorem eval_shift (fr : Frame) (mem : Mem) (op : Clif.BinaryOp) (ty : Clif.Ty) {x y : ValueId}
    {A : BitVec ty.width} {v : Val} (r : BitVec ty.width) (hx : fr.regs x = some ⟨ty, A⟩)
    (hy : fr.regs y = some v) (hs : op.isShift = true) (hr : Clif.Sem.shift op A v.bits = some r) :
    evalInst fr mem (.binary op ty x y) = .ok ([⟨ty, r⟩], mem) := by
  simp [evalInst, getAs_of hx, get_of hy, hs, hr]

theorem eval_ibin (fr : Frame) (mem : Mem) (op : DSL.IBin) (w : IntW) {x y : ValueId}
    {a b : BitVec w.bits} (hx : fr.regs x = some (intV w a)) (hy : fr.regs y = some (intV w b)) :
    evalInst fr mem (.binary (IBin.clif op) (intTy w) x y) = .ok ([intV w (op.denote a b)], mem) := by
  cases op
  case shl | lshr | ashr =>
    refine eval_shift fr mem _ _ _ hx hy rfl ?_
    cases w <;> simp only [intV, Val.ofNat, intTy, Clif.Ty.width, BitVec.ofNat_toNat,
      BitVec.setWidth_eq] <;> rfl
  all_goals
    rw [eval_binary fr mem _ _ hx hy rfl]
    cases w <;> simp only [intV, Val.ofNat, intTy, Clif.Ty.width, BitVec.ofNat_toNat,
      BitVec.setWidth_eq] <;> rfl

theorem eval_inot (fr : Frame) (mem : Mem) (w : IntW) {x : ValueId} {a : BitVec w.bits}
    (hx : fr.regs x = some (intV w a)) :
    evalInst fr mem (.unary .bnot (intTy w) x) = .ok ([intV w (~~~a)], mem) := by
  simp only [evalInst, getAs_of hx, Clif.Res.ok_bind, Clif.Res.pure_eq]
  cases w <;> simp only [intV, Val.ofNat, intTy, Clif.Ty.width, BitVec.ofNat_toNat,
    BitVec.setWidth_eq] <;> rfl

theorem eval_icmp (fr : Frame) (mem : Mem) (op : DSL.ICmp) (w : IntW) {x y : ValueId}
    {a b : BitVec w.bits} (hx : fr.regs x = some (intV w a)) (hy : fr.regs y = some (intV w b)) :
    evalInst fr mem (.icmp (ICmp.clif op) (intTy w) x y) =
      .ok ([Val.ofBool (op.denote a b)], mem) := by
  simp only [evalInst, getAs_of hx, getAs_of hy, Clif.Res.ok_bind, Clif.Res.pure_eq]
  cases w <;> cases op <;> simp only [intTy, Clif.Ty.width, BitVec.ofNat_toNat,
    BitVec.setWidth_eq, ICmp.clif, Clif.Sem.icmp, Clif.Sem.intcc, Clif.Sem.bool8, Val.ofBool,
    DSL.ICmp.denote] <;> rfl

theorem eval_bool_bin (fr : Frame) (mem : Mem) (op : Clif.BinaryOp) {x y : ValueId} {a b : Bool}
    (f : Bool → Bool → Bool) (hop : ∀ a b : Bool, Clif.Sem.binary op (if a then 1#8 else 0#8)
      (if b then 1#8 else 0#8) = if f a b then 1#8 else 0#8) (hs : op.isShift = false)
    (hx : fr.regs x = some (Val.ofBool a)) (hy : fr.regs y = some (Val.ofBool b)) :
    evalInst fr mem (.binary op .i8 x y) = .ok ([Val.ofBool (f a b)], mem) := by
  rw [eval_binary fr mem op .i8 hx hy hs]
  have := hop a b
  simp only [Val.ofBool] at this ⊢
  exact congrArg (fun z : BitVec 8 => (Clif.Res.ok ([Val.mk Clif.Ty.i8 z], mem) : Clif.Res _)) this

theorem band8 (a b : Bool) : Clif.Sem.binary .band (if a then 1#8 else 0#8)
    (if b then 1#8 else 0#8) = if (a && b) then 1#8 else 0#8 := by
  cases a <;> cases b <;> rfl

theorem bor8 (a b : Bool) : Clif.Sem.binary .bor (if a then 1#8 else 0#8)
    (if b then 1#8 else 0#8) = if (a || b) then 1#8 else 0#8 := by
  cases a <;> cases b <;> rfl

theorem bxor8 (a b : Bool) : Clif.Sem.binary .bxor (if a then 1#8 else 0#8)
    (if b then 1#8 else 0#8) = if (a ^^ b) then 1#8 else 0#8 := by
  cases a <;> cases b <;> rfl

theorem eval_ireduce (fr : Frame) (mem : Mem) {w w' : IntW} {x : ValueId} {a : BitVec w.bits}
    (hx : fr.regs x = some (intV w a)) (hlt : w'.bits < w.bits) :
    evalInst fr mem (.ireduce (intTy w') x) = .ok ([intV w' (a.setWidth w'.bits)], mem) := by
  simp only [evalInst, get_of hx, Clif.Res.ok_bind]
  cases w <;> cases w' <;> simp only [IntW.bits] at hlt <;> (try omega) <;>
    simp [intV, Val.ofNat, intTy, Clif.Ty.width, Clif.Sem.ireduce, Clif.Res.check] <;>
    congr 1 <;> apply BitVec.eq_of_toNat_eq <;> simp [IntW.bits] <;> omega

theorem eval_uextend (fr : Frame) (mem : Mem) {w w' : IntW} {x : ValueId} {a : BitVec w.bits}
    (hx : fr.regs x = some (intV w a)) (hlt : w.bits < w'.bits) :
    evalInst fr mem (.extend .uextend (intTy w') x) = .ok ([intV w' (a.setWidth w'.bits)], mem) := by
  simp only [evalInst, get_of hx, Clif.Res.ok_bind]
  cases w <;> cases w' <;> simp only [IntW.bits] at hlt <;> (try omega) <;>
    simp [intV, Val.ofNat, intTy, Clif.Ty.width, Clif.Sem.uextend, Clif.Res.check] <;>
    congr 1 <;> apply BitVec.eq_of_toNat_eq <;> simp [IntW.bits] <;> omega

theorem eval_sextend (fr : Frame) (mem : Mem) {w w' : IntW} {x : ValueId} {a : BitVec w.bits}
    (hx : fr.regs x = some (intV w a)) (hlt : w.bits < w'.bits) :
    evalInst fr mem (.extend .sextend (intTy w') x) = .ok ([intV w' (a.signExtend w'.bits)], mem) := by
  simp only [evalInst, get_of hx, Clif.Res.ok_bind]
  cases w <;> cases w' <;> simp only [IntW.bits] at hlt <;> (try omega) <;>
    simp only [intV, Val.ofNat, intTy, Clif.Ty.width, Clif.Sem.sextend, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, IntW.bits] <;> rfl

theorem intW_eq_of_bits {w w' : IntW} (h : w.bits = w'.bits) : w = w' := by
  cases w <;> cases w' <;> first | rfl | (simp only [IntW.bits] at h; omega)

end Compile.Proof
