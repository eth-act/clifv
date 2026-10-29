import FVTest.Backend.FloatDriverT
import FV.Backend.Proof.RegallocCover
import FV.Backend.SpillAlloc
import FV.E2E.EmitNear

/-!
Non-vacuity of the literal-pool load (S11e6, #565): `%litpool` of
`FVTest/Backend/float_litpool.clif` (an `f64const` with no `fmov`-immediate, zero or 32-bit
form) lowers, as `constant_f64`'s pool rule does, to an `ldr d, <entry>` of a constant-pool entry
(`MInst.isPoolLoad`); the prepared code's forms are covered by the third category of
`FormsCovered`, and the emitted lines hold the literal load (`Insn.fpuLoadLit`) and the entry's
data words (`Line.data`). `csem` gives the load the entry's value (`poolVal`). Checks by
`native_decide`/`#guard` (witness only). Its literal load reaches the pool through the size
condition (`spillSizeOkB`'s `poolReachB`: below `2 ^ 17` words; the VCode is not pool-free), so
`emitFunc_spill_near` applies. `lake build FVTest.E2E.PoolLoadWitness`.
-/

open Backend Backend.Proof Backend.Proof.Driver

namespace PoolLoadWitness

open FloatDriverT

/-- `f64const 0x1.7b8bac710cb29p0` (bits `0x3ff7b8bac710cb29`): a literal-pool constant. -/
def fLit : Clif.Function := fnOfText
  "function %litpool() -> f64 {
block0:
    v0 = f64const 0x1.7b8bac710cb29p0
    return v0
}
"

/-- `prepare`'s output on the lowering (`default` if it fails). -/
def vcpOf (f : Clif.Function) : VCode :=
  match Backend.prepare (vcOf f) with
  | .ok vcp => vcp
  | .error _ => default

def afOf (f : Clif.Function) : AFunc :=
  match lowerRFunc (vcpOf f) (spillAlloc (vcpOf f)) with
  | .ok af => af
  | .error _ => default

def faOf (f : Clif.Function) : FnAsm :=
  match emitFunc 0 (afOf f) with
  | .ok fa => fa
  | .error _ => default

/-- The pool entry's bits. -/
def bits : Nat := 0x3ff7b8bac710cb29

-- the whole pipeline succeeds, and the prepared code holds the pool load of the entry
#guard (lowerFunction fLit).toBool && (Backend.prepare (vcOf fLit)).toBool &&
  (lowerRFunc (vcpOf fLit) (spillAlloc (vcpOf fLit))).toBool && (emitFunc 0 (afOf fLit)).toBool &&
  (faOf fLit).layout.toBool
#guard (vcpOf fLit).blocks.any fun vb => vb.insts.any fun i =>
  i.isPoolLoad && i matches .fpuLoad .size64 _ (.const 0x3ff7b8bac710cb29) _
-- it is neither a control form nor a `FormOk` form: only the third category covers it
#guard (vcpOf fLit).blocks.any fun vb => vb.insts.any fun i =>
  i.isPoolLoad && !i.isCtl && !FormOk ⟨(faOf fLit).k, (afOf fLit).slotBase⟩ i
-- the emitted lines: the literal load and the entry's two data words (low word first)
#guard (faOf fLit).lines.any (· matches .ins (.fpuLoadLit .size64 _ _) _)
#guard (faOf fLit).lines.any (· matches .data 0xc710cb29) &&
  (faOf fLit).lines.any (· matches .data 0x3ff7b8ba)

/-- **Witness**: the prepared code of `%litpool` is covered (`FormsCovered`, with its pool load
in the third category). -/
theorem formsCovered_lit :
    FormsCovered ⟨(faOf fLit).k, (afOf fLit).slotBase⟩ (vcpOf fLit) :=
  (formsCoveredB_iff _ _).mp (by native_decide)

/-- **Witness**: `%litpool`'s prepared code contains a literal-pool load. -/
theorem has_poolLoad :
    ∃ b vb k i, (vcpOf fLit).blocks[b]? = some vb ∧ vb.insts[k]? = some i ∧
      i.isPoolLoad = true := by
  have h : ((vcpOf fLit).blocks.any fun vb => vb.insts.any fun i => i.isPoolLoad) = true := by
    native_decide
  obtain ⟨b, hb, hvb⟩ := Array.any_iff_exists.mp h
  obtain ⟨k, hk, hi⟩ := Array.any_iff_exists.mp hvb
  exact ⟨b, _, k, _, Array.getElem?_eq_getElem hb, Array.getElem?_eq_getElem hk, hi⟩

/-- **Witness**: `csem` of the pool load is the entry's value, the world unchanged. -/
theorem csem_lit (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) (d : Nat)
    (fl : Clif.MemFlags) (w : Arm.ArmState) :
    csem F ctx X (.fpuLoad .size64 (.vreg d .float) (.const bits) fl) [] w =
      some ([poolVal .size64 bits], w, .next) := by
  rw [csem_straight rfl]
  simp [csemWF, FormOk, memOk, mspec]

/-- The value is the `f64` constant's bits, zero-extended to the 128-bit register. -/
theorem poolVal_lit : poolVal .size64 bits = (0x3ff7b8bac710cb29#64).setWidth 128 := by
  decide

/-- The prepared code meets the size condition, by its size: it has a pool load (`noPoolB` is
false), so `poolReachB` holds by the `2 ^ 17` bound. -/
theorem spillSizeOk_lit : spillSizeOkB (vcpOf fLit) = true ∧ (vcpOf fLit).noPoolB = false := by
  native_decide

/-- **Witness of `emitFunc_spill_near` with a literal load** (`emitFunc_near_of`'s size
disjunct): the spill code of `%litpool` emits one literal line, and its lines are `NearOk`. -/
theorem near_lit : ∃ af fa, lowerRFunc (vcpOf fLit) (spillAlloc (vcpOf fLit)) = .ok af ∧
    emitFunc 0 af = .ok fa ∧ fa.lines.toList.countP Line.isLit = 1 ∧ NearOk fa.lines.toList := by
  have h : (match lowerRFunc (vcpOf fLit) (spillAlloc (vcpOf fLit)) with
    | .ok af => match emitFunc 0 af with
      | .ok fa => decide (fa.lines.toList.countP Line.isLit = 1)
      | .error _ => false
    | .error _ => false) = true := by native_decide
  have hna : (vcpOf fLit).noAlwaysB = true := by native_decide
  cases ha : lowerRFunc (vcpOf fLit) (spillAlloc (vcpOf fLit)) with
  | error e => rw [ha] at h; cases h
  | ok af =>
    rw [ha] at h
    cases he : emitFunc 0 af with
    | error e => rw [he] at h; cases h
    | ok fa =>
      rw [he] at h
      exact ⟨af, fa, rfl, rfl, of_decide_eq_true h,
        E2E.emitFunc_spill_near hna spillSizeOk_lit.1 ha he⟩

end PoolLoadWitness
