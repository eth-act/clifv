import FV.Opt.MidValCert
import FV.Opt.Proof.MidValMem
import FV.Clif.MemTrap

/-!
# `Opt.MidVal`: what the certificate's facts mean for `Clif.evalInst` (#1119)

The soundness proof of `Opt.MidVal.checkCert` reads a memory fact (`Fact.mem`: a location, a
type, an access kind, a byte order and a value) as `MemHolds`: the bytes of the access are live
and hold the value, and every load of that kind reads it back. This file proves the facts about
`Clif.evalInst` the simulation uses:

* `evalInst_load_of_holds` / `holds_of_evalInst_load`: a load of a held location reads the held
  value or is `stuck` (never traps); a load that succeeded makes its location held;
* `holds_of_evalInst_store` / `evalInst_store_idem`: a store makes its location hold the stored
  value; storing what a location already holds leaves the memory unchanged (or is `stuck`);
* `evalInst_mergeK`: an idempotent trapping instruction (`mergeK`) does not read or write memory;
* `evalInst_load_notrap`: a `notrap` load never traps.
-/

namespace Opt.MidVal

open Clif

/-- Bytes accessed by an access of kind `k` at type `ty`. -/
def Kind.size (ty : Ty) : Kind → Nat
  | .plain => ty.bytes
  | .ld op => op.size ty
  | .st op => op.size ty

/-- The value a load `op` of type `ty` makes of the raw bytes `raw` (as `Clif.evalInst`). -/
def loadExt (op : LoadOp) (ty : Ty) {w : Nat} (raw : BitVec w) : Val :=
  ⟨ty, if op.signed then raw.signExtend ty.width else raw.zeroExtend ty.width⟩

/-- The memory fact of `Opt.MidVal.Fact.mem`: in `m`, the location `a` holds the value `v` for an
access of kind `k` at type `ty` in byte order `big`. -/
def MemHolds (m : Mem) (a : Nat) (ty : Ty) (k : Kind) (big : Bool) (v : Val) : Prop :=
  k.size ty ≤ ty.bytes ∧ m.valid a (k.size ty) = true ∧ v.ty = ty ∧
    m.readBits big a (k.size ty) (8 * k.size ty) = some (v.bits.setWidth (8 * k.size ty)) ∧
    ∀ op, loadKind op = k → loadExt op ty (v.bits.setWidth (8 * k.size ty)) = v

/-! ## Sizes and kinds -/

/-- Every CLIF type is a whole number of bytes. -/
theorem ty_width_bytes : ∀ ty : Ty, ty.width = 8 * ty.bytes := by
  intro ty; cases ty <;> rfl

@[simp] theorem Kind.size_loadKind (ty : Ty) (op : LoadOp) : (loadKind op).size ty = op.size ty := by
  cases op <;> rfl

@[simp] theorem Kind.size_storeKind (ty : Ty) (op : StoreOp) :
    (storeKind op).size ty = op.size ty := by
  cases op <;> rfl

theorem loadKind_inj {op op' : LoadOp} (h : loadKind op = loadKind op') : op = op' := by
  cases op <;> cases op' <;> first | rfl | (simp [loadKind] at h)

/-- A load kind equals a store kind only for the plain (full-width) accesses. -/
theorem loadKind_eq_storeKind {op : LoadOp} {sop : StoreOp} (h : loadKind op = storeKind sop) :
    op = .load ∧ sop = .store := by
  cases op <;> cases sop <;> first | exact ⟨rfl, rfl⟩ | (simp [loadKind, storeKind] at h)

/-! ## Extension and truncation -/

/-- Truncating an extended load back to the width read gives the raw bits. -/
theorem setWidth_loadExt (op : LoadOp) (ty : Ty) {w : Nat} (raw : BitVec w) (hw : w ≤ ty.width) :
    (loadExt op ty raw).bits.setWidth w = raw := by
  unfold loadExt
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hj' : j < ty.width := by omega
  cases op.signed <;>
    simp [BitVec.getElem_signExtend, hj, hj']

theorem loadExt_setWidth_loadExt (op : LoadOp) (ty : Ty) {w : Nat} (raw : BitVec w)
    (hw : w ≤ ty.width) : loadExt op ty ((loadExt op ty raw).bits.setWidth w) = loadExt op ty raw := by
  rw [setWidth_loadExt op ty raw hw]

/-- A plain load of all the bytes of a value is the value. -/
theorem loadExt_load (ty : Ty) (b : BitVec ty.width) :
    loadExt .load ty (b.setWidth (8 * ty.bytes)) = ⟨ty, b⟩ := by
  have hw := ty_width_bytes ty
  have e : (b.setWidth (8 * ty.bytes)).zeroExtend ty.width = b := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [BitVec.zeroExtend_eq_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_setWidth]
    simp only [hj, show j < 8 * ty.bytes by omega, decide_true, Bool.true_and]
  show (⟨ty, (b.setWidth (8 * ty.bytes)).zeroExtend ty.width⟩ : Val) = ⟨ty, b⟩
  rw [e]

/-! ## `MemHolds` depends on the bytes and allocations only -/

theorem memHolds_congr {m m' : Mem} (hb : m'.bytes = m.bytes) (ha : m'.allocs = m.allocs)
    (a : Nat) (ty : Ty) (k : Kind) (big : Bool) (v : Val) :
    MemHolds m' a ty k big v ↔ MemHolds m a ty k big v := by
  simp only [MemHolds, Mem.valid, Mem.readBits, hb, ha, iff_self]

theorem memHolds_of_eq {m m' : Mem} (hb : m'.bytes = m.bytes) (ha : m'.allocs = m.allocs)
    {a : Nat} {ty : Ty} {k : Kind} {big : Bool} {v : Val} (h : MemHolds m a ty k big v) :
    MemHolds m' a ty k big v :=
  (memHolds_congr hb ha a ty k big v).2 h

/-- A location held for a load kind holds one value. -/
theorem memHolds_unique {m : Mem} {a : Nat} {ty : Ty} {op : LoadOp} {big : Bool} {v v' : Val}
    (h : MemHolds m a ty (loadKind op) big v) (h' : MemHolds m a ty (loadKind op) big v') :
    v = v' := by
  obtain ⟨-, -, -, hr, hx⟩ := h
  obtain ⟨-, -, -, hr', hx'⟩ := h'
  rw [hr] at hr'
  rw [← hx op rfl, ← hx' op rfl, Option.some.inj hr']

/-! ## Storing what is there -/

/-- Writing the bytes a location already holds leaves the memory unchanged. -/
theorem writeBits_self {m : Mem} {big : Bool} {a n w : Nat} {x : BitVec w}
    (hr : m.readBits big a n (8 * n) = some (x.setWidth (8 * n))) : m.writeBits big a n x = m := by
  rw [Mem.readBits_eq] at hr
  obtain ⟨hs1, hs2⟩ := Mem.readFold_spec n _ hr
  have hb : ∀ q, a ≤ q ∧ q < a + n →
      m.bytes q = some (x.extractLsb' (8 * Mem.byteIndex big n (q - a)) 8) := by
    intro q hq
    have hi : Mem.byteIndex big n (q - a) < n := Mem.byteIndex_lt (by omega)
    have hq' : a + Mem.byteIndex big n (Mem.byteIndex big n (q - a)) = q := by
      rw [Mem.byteIndex_byteIndex (by omega)]; omega
    generalize Mem.byteIndex big n (q - a) = i at hi hq' ⊢
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (hs1 i hi)
    have hbq : m.bytes q = some b := by rw [← hq']; exact hb
    rw [hbq]
    congr 1
    apply BitVec.eq_of_getLsbD_eq
    intro t ht
    have h8 := hs2 (8 * i + t)
    rw [BitVec.getLsbD_setWidth, show (8 * i + t) / 8 = i by omega,
      show (8 * i + t) % 8 = t by omega, hb, Option.getD_some] at h8
    simp only [show 8 * i + t < 8 * n by omega, decide_true, Bool.true_and] at h8
    rw [BitVec.getLsbD_extractLsb', h8]
    simp only [ht, decide_true, Bool.true_and]
  have hf : (fun q => if a ≤ q ∧ q < a + n then
      some (x.extractLsb' (8 * Mem.byteIndex big n (q - a)) 8) else m.bytes q) = m.bytes := by
    funext q
    split
    · exact (hb q ‹_›).symm
    · rfl
  exact congrArg (fun f : Nat → Option (BitVec 8) => ({ m with bytes := f } : Mem)) hf

/-! ## Loads -/

/-- **A load of a held location** reads the held value, or is `stuck` (an `aligned` flag on a
misaligned address); it never traps, whatever its other flags. -/
theorem evalInst_load_of_holds {fr : Frame} {m : Mem} {op : LoadOp} {ty : Ty} {fl : MemFlags}
    {p : ValueId} {off : Int} {pv v : Val} (hp : fr.get p = .ok pv)
    (hh : MemHolds m (effAddr pv off) ty (loadKind op) (fl.endianness == some .big) v) :
    evalInst fr m (.load op ty fl p off) = .ok ([v], m) ∨
      ∃ msg, evalInst fr m (.load op ty fl p off) = .stuck msg := by
  obtain ⟨hle, hv, -, hr, hx⟩ := hh
  rw [Kind.size_loadKind] at hle hv hr hx
  have hl : m.load fl (effAddr pv off) (op.size ty) (8 * op.size ty) =
        .ok (v.bits.setWidth (8 * op.size ty)) ∨
      ∃ msg, m.load fl (effAddr pv off) (op.size ty) (8 * op.size ty) = .stuck msg := by
    unfold Mem.load
    rcases Mem.checkAccess_of_valid fl hv with h | ⟨msg, h⟩
    · left; rw [h, Res.ok_bind, hr, Res.ofOption_some]
    · right; rw [h]; exact ⟨msg, rfl⟩
  simp only [evalInst, hp, Res.ok_bind, hle, decide_true, Res.check_true]
  rcases hl with hl | ⟨msg, hl⟩
  · rw [hl, Res.ok_bind, Res.pure_eq]
    exact Or.inl (congrArg (fun v => Res.ok ([v], m)) (hx op rfl))
  · rw [hl]; exact Or.inr ⟨msg, rfl⟩

/-- **A load that succeeded** keeps the memory, has one result, and its location holds it. -/
theorem holds_of_evalInst_load {fr : Frame} {m m' : Mem} {op : LoadOp} {ty : Ty} {fl : MemFlags}
    {p : ValueId} {off : Int} {vs : List Val} {pv : Val}
    (h : evalInst fr m (.load op ty fl p off) = .ok (vs, m')) (hp : fr.get p = .ok pv) :
    m' = m ∧ ∃ v, vs = [v] ∧
      MemHolds m (effAddr pv off) ty (loadKind op) (fl.endianness == some .big) v := by
  simp only [evalInst, hp, Res.ok_bind] at h
  by_cases hle : op.size ty ≤ ty.bytes
  · simp only [hle, decide_true, Res.check_true, Res.ok_bind] at h
    have hw : 8 * op.size ty ≤ ty.width := by rw [ty_width_bytes ty]; omega
    unfold Mem.load at h
    cases hc : m.checkAccess fl (effAddr pv off) (op.size ty) with
    | trap c => rw [hc] at h; simp only [Res.trap_bind, reduceCtorEq] at h
    | stuck s => rw [hc] at h; simp only [Res.stuck_bind, reduceCtorEq] at h
    | ok u =>
      rw [hc, Res.ok_bind] at h
      have hv := Mem.checkAccess_ok_valid hc
      cases hr : m.readBits (fl.endianness == some .big) (effAddr pv off) (op.size ty)
          (8 * op.size ty) with
      | none => rw [hr] at h; simp only [Res.ofOption_none, Res.stuck_bind, reduceCtorEq] at h
      | some r =>
        rw [hr, Res.ofOption_some, Res.ok_bind, Res.pure_eq] at h
        cases h
        refine ⟨rfl, loadExt op ty r, rfl, ?_⟩
        unfold MemHolds
        rw [Kind.size_loadKind]
        refine ⟨hle, hv, rfl, ?_, fun op' hk => ?_⟩
        · rw [hr, setWidth_loadExt op ty r hw]
        · rw [loadKind_inj hk]
          exact loadExt_setWidth_loadExt op ty r hw
  · simp only [hle, decide_false, Res.check_false, Res.stuck_bind, reduceCtorEq] at h

/-- **A `notrap` load never traps.** -/
theorem evalInst_load_notrap {fr : Frame} {m : Mem} {op : LoadOp} {ty : Ty} {fl : MemFlags}
    {p : ValueId} {off : Int} (hn : fl.trapCode = none) (c : TrapCode) :
    evalInst fr m (.load op ty fl p off) ≠ .trap c :=
  evalInst_notrap rfl hn c

/-! ## Stores -/

/-- **A store that succeeded** has no result, and its location holds the stored value. -/
theorem holds_of_evalInst_store {fr : Frame} {m m' : Mem} {op : StoreOp} {ty : Ty}
    {fl : MemFlags} {x p : ValueId} {off : Int} {vs : List Val} {xv pv : Val}
    (h : evalInst fr m (.store op ty fl x p off) = .ok (vs, m')) (hx : fr.get x = .ok xv)
    (hp : fr.get p = .ok pv) :
    vs = [] ∧ MemHolds m' (effAddr pv off) ty (storeKind op) (fl.endianness == some .big) xv := by
  obtain ⟨t, bits⟩ := xv
  simp only [evalInst, Frame.getAs, hx, hp, Res.ok_bind] at h
  by_cases ht : t = ty
  · subst ht
    simp only [Val.as?_mk, Res.ofOption_some, Res.ok_bind] at h
    by_cases hle : op.size t ≤ t.bytes
    · simp only [hle, decide_true, Res.check_true, Res.ok_bind] at h
      cases hs : m.store fl (effAddr pv off) (op.size t) bits with
      | trap c => rw [hs] at h; simp only [Res.trap_bind, reduceCtorEq] at h
      | stuck s => rw [hs] at h; simp only [Res.stuck_bind, reduceCtorEq] at h
      | ok m2 =>
        rw [hs, Res.ok_bind, Res.pure_eq] at h
        cases h
        unfold Mem.store at hs
        cases hc : m.checkAccess fl (effAddr pv off) (op.size t) with
        | trap c => rw [hc] at hs; simp only [Res.trap_bind, reduceCtorEq] at hs
        | stuck s => rw [hc] at hs; simp only [Res.stuck_bind, reduceCtorEq] at hs
        | ok u =>
          rw [hc, Res.ok_bind] at hs
          have hv := Mem.checkAccess_ok_valid hc
          cases hro : m.readonlyAt (effAddr pv off) (op.size t) with
          | true => rw [hro] at hs; simp only [Bool.not_true, Res.check_false, Res.stuck_bind, reduceCtorEq] at hs
          | false =>
            rw [hro] at hs
            simp only [Bool.not_false, Res.check_true, Res.ok_bind, Res.pure_eq] at hs
            cases hs
            refine ⟨rfl, ?_⟩
            unfold MemHolds
            rw [Kind.size_storeKind]
            refine ⟨hle, by rw [Mem.writeBits_valid]; exact hv, rfl,
              Mem.readBits_writeBits _ _ _ _ _, fun op' hk => ?_⟩
            obtain ⟨rfl, rfl⟩ := loadKind_eq_storeKind hk
            exact loadExt_load t bits
    · simp only [hle, decide_false, Res.check_false, Res.stuck_bind, reduceCtorEq] at h
  · simp [Val.as?, ht, Res.ofOption] at h

/-- **Storing what a location holds** leaves the memory unchanged, or is `stuck` (a misaligned
`aligned` access, or read-only data); it never traps, whatever its other flags. -/
theorem evalInst_store_idem {fr : Frame} {m : Mem} {op : StoreOp} {ty : Ty} {fl : MemFlags}
    {x p : ValueId} {off : Int} {xv pv : Val} (hx : fr.get x = .ok xv) (hp : fr.get p = .ok pv)
    (hh : MemHolds m (effAddr pv off) ty (storeKind op) (fl.endianness == some .big) xv) :
    evalInst fr m (.store op ty fl x p off) = .ok ([], m) ∨
      ∃ msg, evalInst fr m (.store op ty fl x p off) = .stuck msg := by
  obtain ⟨t, bits⟩ := xv
  obtain ⟨hle, hv, ht, hr, -⟩ := hh
  simp only at ht
  subst ht
  rw [Kind.size_storeKind] at hle hv hr
  have hw : m.writeBits (fl.endianness == some .big) (effAddr pv off) (op.size t) bits = m :=
    writeBits_self hr
  simp only [evalInst, Frame.getAs, hx, hp, Val.as?_mk, Res.ofOption_some, Res.ok_bind, hle,
    decide_true, Res.check_true]
  unfold Mem.store
  rcases Mem.checkAccess_of_valid fl hv with h | ⟨msg, h⟩
  · rw [h, Res.ok_bind]
    cases hro : m.readonlyAt (effAddr pv off) (op.size t) with
    | false =>
      left
      simp only [Bool.not_false, Res.check_true, Res.ok_bind, Res.pure_eq, hw]
    | true => exact Or.inr ⟨_, rfl⟩
  · rw [h]; exact Or.inr ⟨msg, rfl⟩

/-! ## Idempotent trapping instructions do not touch memory -/

/-- A `mergeK` instruction's result does not depend on the memory, which it keeps. -/
theorem evalInst_mergeK_eq {fr : Frame} {i : Inst} (hk : mergeK i = true) :
    ∃ r : Res (List Val), ∀ m, evalInst fr m i = r >>= fun vs => pure (vs, m) := by
  cases i <;> simp only [mergeK, Bool.false_eq_true] at hk
  case div op ty x y =>
    exact ⟨do
      let a ← fr.getAs x ty
      let b ← fr.getAs y ty
      let r ← Res.ofExcept (Sem.div op a b)
      pure [⟨ty, r⟩], fun m => by simp only [evalInst, bind_assoc, pure_bind]⟩
  case uaddOverflowTrap ty x y code =>
    exact ⟨do
      let a ← fr.getAs x ty
      let b ← fr.getAs y ty
      let r ← Res.ofExcept (Sem.uaddOverflowTrap a b code)
      pure [⟨ty, r⟩], fun m => by simp only [evalInst, bind_assoc, pure_bind]⟩
  case trapz c code =>
    refine ⟨do
      let cv ← fr.get c
      if Sem.truthy cv.bits then pure [] else .trap code, fun m => ?_⟩
    simp only [evalInst, bind_assoc]
    refine congrArg (fr.get c >>= ·) (funext fun cv => ?_)
    cases Sem.truthy cv.bits <;> rfl
  case trapnz c code =>
    refine ⟨do
      let cv ← fr.get c
      if Sem.truthy cv.bits then .trap code else pure [], fun m => ?_⟩
    simp only [evalInst, bind_assoc]
    refine congrArg (fr.get c >>= ·) (funext fun cv => ?_)
    cases Sem.truthy cv.bits <;> rfl
  case float op ty args =>
    exact ⟨do
      let vs ← fr.getMany args
      let r ← evalFloat op ty vs
      pure [r], fun m => by simp only [evalInst, bind_assoc, pure_bind]⟩

/-- **An idempotent trapping instruction (`mergeK`) does not read or write memory**: in any
memory it has the same results (keeping that memory), the same trap, or the same `stuck`. -/
theorem evalInst_mergeK {fr : Frame} {m : Mem} {i : Inst} (hk : mergeK i = true) :
    (∀ vs m1, evalInst fr m i = .ok (vs, m1) → m1 = m ∧ ∀ m', evalInst fr m' i = .ok (vs, m')) ∧
      (∀ c, evalInst fr m i = .trap c → ∀ m', evalInst fr m' i = .trap c) ∧
      (∀ msg, evalInst fr m i = .stuck msg → ∀ m', evalInst fr m' i = .stuck msg) := by
  obtain ⟨r, hr⟩ := evalInst_mergeK_eq (fr := fr) hk
  refine ⟨fun vs m1 h => ?_, fun c h m' => ?_, fun msg h m' => ?_⟩ <;> rw [hr] at h
  · cases r with
    | ok vs0 =>
      simp only [Res.ok_bind, Res.pure_eq, Res.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, fun m' => (hr m').trans rfl⟩
    | trap c => simp only [Res.trap_bind, reduceCtorEq] at h
    | stuck s => simp only [Res.stuck_bind, reduceCtorEq] at h
  · rw [hr]
    cases r with
    | ok vs0 => simp only [Res.ok_bind, Res.pure_eq, reduceCtorEq] at h
    | trap c0 => simp only [Res.trap_bind] at h ⊢; exact h
    | stuck s => simp only [Res.stuck_bind, reduceCtorEq] at h
  · rw [hr]
    cases r with
    | ok vs0 => simp only [Res.ok_bind, Res.pure_eq, reduceCtorEq] at h
    | trap c => simp only [Res.trap_bind, reduceCtorEq] at h
    | stuck s0 => simp only [Res.stuck_bind] at h ⊢; exact h

end Opt.MidVal
