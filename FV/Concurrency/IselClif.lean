module

public import FV.Concurrency.IselFoot
public import FV.Backend.Proof.IselMemArm

@[expose] public section

/-!
# The CLIF side of the variation argument (T2h, #311, layer 2d)

`IselVary.store_touched`/`load_touched` (and `IselFoot.store_in_events`/`load_in_events`) take
two facts about the CLIF statement as premises: its outcome on every memory with the same
allocations (`hout`), and, for a load-like statement, that its first result determines the
bytes it read (`hinj`). This file proves them for every CLIF memory statement in the
multi-threaded scope from one successful run of it (`load`, `store`, `atomic_load`,
`atomic_store`, `atomic_rmw`, `atomic_cas`; loads little-endian), and assembles
**`access_in_events`**: every byte of the statement's CLIF access (`access`: the effective
address and the access size, the location and size of its `ClifThread.CStep` events) lies in
some memory event of the run of the statement's lowered code.
-/

namespace Concurrency.IselClif

open Backend Backend.Proof IselVary IselFoot

/-- The `big` argument of `readBits`/`writeBits` for memory flags. -/
abbrev bigOf (fl : Clif.MemFlags) : Bool := fl.endianness == some .big

theorem bind_ok {α β : Type} {x : Clif.Res α} {f : α → Clif.Res β} {b : β} :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp

theorem check_ok {b : Bool} {msg : String} {u : Unit} : Clif.Res.check b msg = .ok u ↔ b = true := by
  cases b <;> simp

theorem checkAccess_allocs {c c' : Clif.Mem} (h : c.allocs = c'.allocs) (fl : Clif.MemFlags)
    (a n : Nat) : c.checkAccess fl a n = c'.checkAccess fl a n := by
  simp [Clif.Mem.checkAccess, Clif.Mem.valid, h]

theorem readonlyAt_allocs {c c' : Clif.Mem} (h : c.allocs = c'.allocs) (a n : Nat) :
    c.readonlyAt a n = c'.readonlyAt a n := by
  simp [Clif.Mem.readonlyAt, h]

theorem checkAccess_valid {c : Clif.Mem} {fl : Clif.MemFlags} {a n : Nat} {u : Unit}
    (h : c.checkAccess fl a n = .ok u) : c.valid a n = true := by
  unfold Clif.Mem.checkAccess at h
  split at h
  · assumption
  · split at h <;> simp at h

/-- **A successful store succeeds on every memory with the same allocations**, writing the same
bytes. -/
theorem store_ok {cm cm' : Clif.Mem} {fl : Clif.MemFlags} {a n w : Nat} {x : BitVec w}
    (h : cm.store fl a n x = .ok cm') :
    cm.valid a n = true ∧ ∀ c : Clif.Mem, c.allocs = cm.allocs →
      c.store fl a n x = .ok (c.writeBits (bigOf fl) a n x) := by
  simp only [Clif.Mem.store, bind_ok] at h
  obtain ⟨u, hc, u', hr, -⟩ := h
  refine ⟨checkAccess_valid hc, fun c hca => ?_⟩
  simp only [Clif.Mem.store, checkAccess_allocs hca, hc, readonlyAt_allocs hca, Clif.Res.ok_bind]
  rw [check_ok.mp hr]
  rfl

theorem load_check {c : Clif.Mem} {fl : Clif.MemFlags} {a n w : Nat} {r : BitVec w}
    (h : c.load fl a n w = .ok r) : c.checkAccess fl a n = .ok () := by
  simp only [Clif.Mem.load, bind_ok] at h
  obtain ⟨u, hc, -⟩ := h
  exact hc

theorem store_of {c : Clif.Mem} {fl : Clif.MemFlags} {a n w : Nat} {x : BitVec w}
    (hc : c.checkAccess fl a n = .ok ()) (hro : c.readonlyAt a n = false) :
    c.store fl a n x = .ok (c.writeBits (bigOf fl) a n x) := by
  simp only [Clif.Mem.store, hc, hro, Clif.Res.ok_bind]
  rfl

theorem store_ro {c c' : Clif.Mem} {fl : Clif.MemFlags} {a n w : Nat} {x : BitVec w}
    (h : c.store fl a n x = .ok c') : c.readonlyAt a n = false := by
  simp only [Clif.Mem.store, bind_ok] at h
  obtain ⟨u, -, u', hr, -⟩ := h
  simpa using check_ok.mp hr

theorem readBits_some {m : Clif.Mem} {a w : Nat} :
    ∀ n, (∀ k < n, (m.bytes (a + k)).isSome) → ∃ x, m.readBits false a n w = some x := by
  intro n
  induction n with
  | zero => intro _; exact ⟨0, rfl⟩
  | succ n ih =>
    intro h
    obtain ⟨acc, hacc⟩ := ih fun k hk => h k (by omega)
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (h n (by omega))
    have e : m.readBits false a (n + 1) w = (m.readBits false a n w).bind fun acc =>
        (m.bytes (a + n)).map fun b => acc ||| ((b.setWidth w : BitVec w) <<< (8 * n)) := by
      unfold Clif.Mem.readBits
      rw [List.range_succ, List.foldlM_append]
      simp only [List.foldlM_cons, List.foldlM_nil, Clif.Mem.byteIndex, Bool.false_eq_true,
        ite_false]
      show Option.bind _ _ = Option.bind _ _
      congr 1
      funext acc
      cases m.bytes (a + n) <;> rfl
    rw [e, hacc]
    exact ⟨acc ||| ((b.setWidth w : BitVec w) <<< (8 * n)), by simp [hb]⟩

/-- **A little-endian read's value determines its bytes** (when the value holds all of them). -/
theorem readBits_inj {c1 c2 : Clif.Mem} {a n w : Nat} {r : BitVec w} (hw : 8 * n ≤ w)
    (h1 : c1.readBits false a n w = some r) (h2 : c2.readBits false a n w = some r) :
    ∀ j < n, c1.bytes (a + j) = c2.bytes (a + j) := by
  intro j hj
  obtain ⟨s1, b1⟩ := readBits_spec h1
  obtain ⟨s2, b2⟩ := readBits_spec h2
  obtain ⟨y1, hy1⟩ := Option.isSome_iff_exists.mp (s1 j hj)
  obtain ⟨y2, hy2⟩ := Option.isSome_iff_exists.mp (s2 j hj)
  rw [hy1, hy2]
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have e1 := b1 (8 * j + i)
  have e2 := b2 (8 * j + i)
  rw [e1] at e2
  have q : (8 * j + i) / 8 = j := by omega
  have q' : (8 * j + i) % 8 = i := by omega
  simp only [q, q', hy1, hy2, Option.getD_some, show 8 * j + i < w by omega,
    hj, decide_true, Bool.true_and] at e2
  exact e2

theorem load_eq {c : Clif.Mem} {fl : Clif.MemFlags} {a n w : Nat} {r : BitVec w}
    (hle : bigOf fl = false) (h : c.load fl a n w = .ok r) :
    c.valid a n = true ∧ c.readBits false a n w = some r := by
  simp only [Clif.Mem.load, bind_ok] at h
  obtain ⟨u, hc, hr⟩ := h
  have hle' : (fl.endianness == some Clif.Endianness.big) = false := hle
  rw [hle'] at hr
  refine ⟨checkAccess_valid hc, ?_⟩
  cases hb : c.readBits false a n w <;> simp_all

/-- **A successful little-endian load succeeds on every memory with the same allocations whose
bytes there are initialised.** -/
theorem load_ok {cm : Clif.Mem} {fl : Clif.MemFlags} {a n w : Nat} {r : BitVec w}
    (hle : bigOf fl = false) (h : cm.load fl a n w = .ok r) :
    cm.valid a n = true ∧ (∀ j < n, (cm.bytes (a + j)).isSome) ∧
      ∀ c : Clif.Mem, c.allocs = cm.allocs → (∀ j < n, (c.bytes (a + j)).isSome) →
        ∃ r', c.load fl a n w = .ok r' := by
  obtain ⟨hv, hr⟩ := load_eq hle h
  refine ⟨hv, (readBits_spec hr).1, fun c hca hi => ?_⟩
  obtain ⟨r', hr'⟩ := readBits_some (w := w) n hi
  simp only [Clif.Mem.load, bind_ok] at h
  obtain ⟨u, hc, -⟩ := h
  refine ⟨r', ?_⟩
  have hle' : (fl.endianness == some Clif.Endianness.big) = false := hle
  simp only [Clif.Mem.load, checkAccess_allocs hca, hc, Clif.Res.ok_bind]
  rw [hle', hr']
  rfl

theorem width_bytes (ty : Clif.Ty) : 8 * ty.bytes = ty.width := by
  cases ty <;> rfl

theorem ext_inj {m w : Nat} (hm : m ≤ w) (s : Bool) {x y : BitVec m}
    (h : (if s then x.signExtend w else x.zeroExtend w) =
      (if s then y.signExtend w else y.zeroExtend w)) : x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have := congrArg (fun z => z.getLsbD i) h
  cases s
  · simp only [Bool.false_eq_true, ite_false, BitVec.getLsbD_setWidth, show i < w by omega,
      decide_true, Bool.true_and] at this
    exact this
  · simp only [ite_true, BitVec.getLsbD_signExtend, hi, ite_true, show i < w by omega,
      decide_true, Bool.true_and] at this
    exact this

/-- The CLIF access (effective address, size) of a memory statement on frame `fr`: the location
and size of its `ClifThread.CStep` events (`evShape`). Big-endian loads are left out. -/
def access (fr : Clif.Frame) : Clif.Inst → Option (Nat × Nat)
  | .load op ty fl p off =>
    if bigOf fl then none else (fr.regs p).map fun pv => (Clif.effAddr pv off, op.size ty)
  | .store op ty _ _ p off => (fr.regs p).map fun pv => (Clif.effAddr pv off, op.size ty)
  | .atomicLoad ty fl p | .atomicRmw _ ty fl p _ | .atomicCas ty fl p _ _ =>
    if bigOf fl then none else (fr.regs p).map fun pv => (Clif.effAddr pv 0, ty.bytes)
  | .atomicStore ty _ _ p => (fr.regs p).map fun pv => (Clif.effAddr pv 0, ty.bytes)
  | _ => none

/-- A statement writing exactly its access (`store`, `atomic_store`): from one successful run,
its outcome on every memory with the same allocations. -/
def StoreFacts (env : Clif.Env) (p : Clif.Program) (fr : Clif.Frame) (cm : Clif.Mem)
    (inst : Clif.Inst) (a n : Nat) : Prop :=
  cm.valid a n = true ∧ ∃ (big : Bool) (wd : Nat) (v : BitVec wd), ∀ c : Clif.Mem,
    c.allocs = cm.allocs → instOutcome env p fr c inst = .ok ([], c.writeBits big a n v)

/-- A statement whose first result is the bytes of its access (`load`, `atomic_load`,
`atomic_rmw`, `atomic_cas`): the premises of `load_touched`. -/
def LoadFacts (env : Clif.Env) (p : Clif.Program) (fr : Clif.Frame) (cm : Clif.Mem)
    (inst : Clif.Inst) (a n : Nat) : Prop :=
  cm.valid a n = true ∧ (∀ j < n, (cm.bytes (a + j)).isSome) ∧
    (∀ c : Clif.Mem, c.allocs = cm.allocs → (∀ j < n, (c.bytes (a + j)).isSome) →
      ∃ v vs c', instOutcome env p fr c inst = .ok (v :: vs, c')) ∧
    (∀ c1 c2 : Clif.Mem, ∀ v1 v2 vs1 vs2 c1' c2',
      instOutcome env p fr c1 inst = .ok (v1 :: vs1, c1') →
      instOutcome env p fr c2 inst = .ok (v2 :: vs2, c2') →
      v1.ty = v2.ty ∧ (v1 = v2 → ∀ j < n, c1.bytes (a + j) = c2.bytes (a + j)))

theorem getAs_ok {fr : Clif.Frame} {x : Nat} {ty : Clif.Ty} {a : BitVec ty.width}
    (h : fr.getAs x ty = .ok a) : ∃ v, fr.regs x = some v ∧ v.as? ty = some a := by
  simp only [Clif.Frame.getAs, Clif.Frame.get, bind_ok] at h
  obtain ⟨v, hv, ha⟩ := h
  cases hr : fr.regs x <;> simp_all
  cases hv
  cases hs : v.as? ty <;> simp_all

theorem outcome_eval (env : Clif.Env) (p : Clif.Program) (fr : Clif.Frame) (c : Clif.Mem)
    {inst : Clif.Inst} (h1 : ∀ fn args, inst ≠ .call fn args)
    (h2 : ∀ sig callee args, inst ≠ .callIndirect sig callee args) :
    instOutcome env p fr c inst = Clif.evalInst fr c inst := by
  cases inst <;> first | rfl | (exfalso; first | exact h1 _ _ rfl | exact h2 _ _ _ rfl)

theorem pure_ok {v : Clif.Val} {vs : List Clif.Val} {c c' : Clif.Mem} {l : List Clif.Val}
    (h : (pure (l, c) : Clif.Res (List Clif.Val × Clif.Mem)) = .ok (v :: vs, c')) :
    l = v :: vs ∧ c = c' := by
  simp only [Clif.Res.pure_eq, Clif.Res.ok.injEq, Prod.mk.injEq] at h
  exact h

/-- **`load`**: `LoadFacts` at its access. -/
theorem load_facts {env : Clif.Env} {p : Clif.Program} {fr : Clif.Frame} {cm : Clif.Mem}
    {op : Clif.LoadOp} {ty : Clif.Ty} {fl : Clif.MemFlags} {pp : Nat} {off : Int}
    {vs : List Clif.Val} {cm' : Clif.Mem} (hle : bigOf fl = false)
    (h : instOutcome env p fr cm (.load op ty fl pp off) = .ok (vs, cm')) {pv : Clif.Val}
    (hpv : fr.regs pp = some pv) :
    LoadFacts env p fr cm (.load op ty fl pp off) (Clif.effAddr pv off) (op.size ty) := by
  have e : ∀ c, instOutcome env p fr c (.load op ty fl pp off) =
      ((Clif.Res.check (op.size ty ≤ ty.bytes) "load: access wider than result") >>= fun _ =>
        (c.load fl (Clif.effAddr pv off) (op.size ty) (8 * op.size ty)) >>= fun raw =>
          pure ([⟨ty, if op.signed then raw.signExtend ty.width else raw.zeroExtend ty.width⟩], c)) := by
    intro c
    simp only [instOutcome, Clif.evalInst, Clif.Frame.get, hpv, Clif.Res.ofOption_some,
      Clif.Res.ok_bind]
  rw [e, bind_ok] at h
  obtain ⟨u, hck, h⟩ := h
  rw [bind_ok] at h
  obtain ⟨raw, hl, -⟩ := h
  obtain ⟨hv, hi, hc⟩ := load_ok hle hl
  refine ⟨hv, hi, fun c hca hic => ?_, fun c1 c2 v1 v2 vs1 vs2 c1' c2' h1 h2 => ?_⟩
  · obtain ⟨r', hr'⟩ := hc c hca hic
    refine ⟨⟨ty, if op.signed then r'.signExtend ty.width else r'.zeroExtend ty.width⟩, [], c, ?_⟩
    rw [e, hck, Clif.Res.ok_bind, hr', Clif.Res.ok_bind]
    rfl
  · rw [e, bind_ok] at h1 h2
    obtain ⟨_, _, h1⟩ := h1
    obtain ⟨_, _, h2⟩ := h2
    rw [bind_ok] at h1 h2
    obtain ⟨raw1, hl1, e1⟩ := h1
    obtain ⟨raw2, hl2, e2⟩ := h2
    obtain ⟨e1, -⟩ := pure_ok e1
    obtain ⟨e2, -⟩ := pure_ok e2
    simp only [List.cons.injEq] at e1 e2
    obtain ⟨rfl, -⟩ := e1
    obtain ⟨rfl, -⟩ := e2
    refine ⟨rfl, fun hvv => ?_⟩
    simp only [Clif.Val.mk.injEq, heq_eq_eq, true_and] at hvv
    have hn : op.size ty ≤ ty.bytes := by simpa [check_ok] using hck
    have hraw := ext_inj (by rw [← width_bytes]; omega) op.signed hvv
    subst hraw
    exact readBits_inj (Nat.le_refl _) (load_eq hle hl1).2 (load_eq hle hl2).2

/-- **`store`**: `StoreFacts` at its access. -/
theorem store_facts {env : Clif.Env} {p : Clif.Program} {fr : Clif.Frame} {cm : Clif.Mem}
    {op : Clif.StoreOp} {ty : Clif.Ty} {fl : Clif.MemFlags} {x pp : Nat} {off : Int}
    {vs : List Clif.Val} {cm' : Clif.Mem}
    (h : instOutcome env p fr cm (.store op ty fl x pp off) = .ok (vs, cm')) {pv : Clif.Val}
    (hpv : fr.regs pp = some pv) :
    StoreFacts env p fr cm (.store op ty fl x pp off) (Clif.effAddr pv off) (op.size ty) := by
  have e : ∀ c, instOutcome env p fr c (.store op ty fl x pp off) =
      (fr.getAs x ty >>= fun a =>
        (Clif.Res.check (op.size ty ≤ ty.bytes) "store: access wider than value") >>= fun _ =>
          (c.store fl (Clif.effAddr pv off) (op.size ty) a) >>= fun mem' => pure ([], mem')) := by
    intro c
    simp only [instOutcome, Clif.evalInst, Clif.Frame.get, hpv, Clif.Res.ofOption_some,
      Clif.Res.ok_bind]
  rw [e, bind_ok] at h
  obtain ⟨a, ha, h⟩ := h
  rw [bind_ok] at h
  obtain ⟨u, hck, h⟩ := h
  rw [bind_ok] at h
  obtain ⟨m1, hs, -⟩ := h
  obtain ⟨hv, hc⟩ := store_ok hs
  refine ⟨hv, bigOf fl, _, a, fun c hca => ?_⟩
  rw [e, ha, Clif.Res.ok_bind, hck, Clif.Res.ok_bind, hc c hca, Clif.Res.ok_bind]
  rfl

/-- **`atomic_store`**: `StoreFacts` at its access. -/
theorem atomicStore_facts {env : Clif.Env} {p : Clif.Program} {fr : Clif.Frame} {cm : Clif.Mem}
    {ty : Clif.Ty} {fl : Clif.MemFlags} {x pp : Nat} {vs : List Clif.Val} {cm' : Clif.Mem}
    (h : instOutcome env p fr cm (.atomicStore ty fl x pp) = .ok (vs, cm')) {pv : Clif.Val}
    (hpv : fr.regs pp = some pv) :
    StoreFacts env p fr cm (.atomicStore ty fl x pp) (Clif.effAddr pv 0) ty.bytes := by
  have e : ∀ c, instOutcome env p fr c (.atomicStore ty fl x pp) =
      (fr.getAs x ty >>= fun a =>
        (Clif.Res.check (Clif.effAddr pv 0 % ty.bytes == 0) "misaligned atomic access") >>= fun _ =>
          (c.store fl (Clif.effAddr pv 0) ty.bytes a) >>= fun mem' => pure ([], mem')) := by
    intro c
    simp only [instOutcome, Clif.evalInst, Clif.Frame.get, hpv, Clif.Res.ofOption_some,
      Clif.Res.ok_bind]
  rw [e, bind_ok] at h
  obtain ⟨a, ha, h⟩ := h
  rw [bind_ok] at h
  obtain ⟨u, hck, h⟩ := h
  rw [bind_ok] at h
  obtain ⟨m1, hs, -⟩ := h
  obtain ⟨hv, hc⟩ := store_ok hs
  refine ⟨hv, bigOf fl, _, a, fun c hca => ?_⟩
  rw [e, ha, Clif.Res.ok_bind, hck, Clif.Res.ok_bind, hc c hca, Clif.Res.ok_bind]
  rfl

/-- **`atomic_load`**: `LoadFacts` at its access. -/
theorem atomicLoad_facts {env : Clif.Env} {p : Clif.Program} {fr : Clif.Frame} {cm : Clif.Mem}
    {ty : Clif.Ty} {fl : Clif.MemFlags} {pp : Nat} {vs : List Clif.Val} {cm' : Clif.Mem}
    (hle : bigOf fl = false)
    (h : instOutcome env p fr cm (.atomicLoad ty fl pp) = .ok (vs, cm')) {pv : Clif.Val}
    (hpv : fr.regs pp = some pv) :
    LoadFacts env p fr cm (.atomicLoad ty fl pp) (Clif.effAddr pv 0) ty.bytes := by
  have e : ∀ c, instOutcome env p fr c (.atomicLoad ty fl pp) =
      ((Clif.Res.check (Clif.effAddr pv 0 % ty.bytes == 0) "misaligned atomic access") >>= fun _ =>
        (c.load fl (Clif.effAddr pv 0) ty.bytes ty.width) >>= fun v => pure ([⟨ty, v⟩], c)) := by
    intro c
    simp only [instOutcome, Clif.evalInst, Clif.Frame.get, hpv, Clif.Res.ofOption_some,
      Clif.Res.ok_bind]
  rw [e, bind_ok] at h
  obtain ⟨u, hck, h⟩ := h
  rw [bind_ok] at h
  obtain ⟨raw, hl, -⟩ := h
  obtain ⟨hv, hi, hc⟩ := load_ok hle hl
  refine ⟨hv, hi, fun c hca hic => ?_, fun c1 c2 v1 v2 vs1 vs2 c1' c2' h1 h2 => ?_⟩
  · obtain ⟨r', hr'⟩ := hc c hca hic
    refine ⟨⟨ty, r'⟩, [], c, ?_⟩
    rw [e, hck, Clif.Res.ok_bind, hr', Clif.Res.ok_bind]
    rfl
  · rw [e, bind_ok] at h1 h2
    obtain ⟨_, _, h1⟩ := h1
    obtain ⟨_, _, h2⟩ := h2
    rw [bind_ok] at h1 h2
    obtain ⟨raw1, hl1, e1⟩ := h1
    obtain ⟨raw2, hl2, e2⟩ := h2
    obtain ⟨e1, -⟩ := pure_ok e1
    obtain ⟨e2, -⟩ := pure_ok e2
    simp only [List.cons.injEq] at e1 e2
    obtain ⟨rfl, -⟩ := e1
    obtain ⟨rfl, -⟩ := e2
    refine ⟨rfl, fun hvv => ?_⟩
    simp only [Clif.Val.mk.injEq, heq_eq_eq, true_and] at hvv
    subst hvv
    exact readBits_inj (Nat.le_of_eq (width_bytes ty)) (load_eq hle hl1).2 (load_eq hle hl2).2

/-- **`atomic_rmw`**: `LoadFacts` at its access (its first result is the old value). -/
theorem atomicRmw_facts {env : Clif.Env} {p : Clif.Program} {fr : Clif.Frame} {cm : Clif.Mem}
    {op : Clif.AtomicRmwOp} {ty : Clif.Ty} {fl : Clif.MemFlags} {pp x : Nat}
    {vs : List Clif.Val} {cm' : Clif.Mem} (hle : bigOf fl = false)
    (h : instOutcome env p fr cm (.atomicRmw op ty fl pp x) = .ok (vs, cm')) {pv : Clif.Val}
    (hpv : fr.regs pp = some pv) :
    LoadFacts env p fr cm (.atomicRmw op ty fl pp x) (Clif.effAddr pv 0) ty.bytes := by
  have e : ∀ c, instOutcome env p fr c (.atomicRmw op ty fl pp x) =
      (fr.getAs x ty >>= fun a =>
        (Clif.Res.check (Clif.effAddr pv 0 % ty.bytes == 0) "misaligned atomic access") >>= fun _ =>
          (c.load fl (Clif.effAddr pv 0) ty.bytes ty.width) >>= fun old =>
            (c.store fl (Clif.effAddr pv 0) ty.bytes (Clif.Sem.atomicRmw op old a)) >>= fun mem' =>
              pure ([⟨ty, old⟩], mem')) := by
    intro c
    simp only [instOutcome, Clif.evalInst, Clif.Frame.get, hpv, Clif.Res.ofOption_some,
      Clif.Res.ok_bind]
  rw [e, bind_ok] at h
  obtain ⟨a, ha, h⟩ := h
  rw [bind_ok] at h
  obtain ⟨u, hck, h⟩ := h
  rw [bind_ok] at h
  obtain ⟨raw, hl, h⟩ := h
  rw [bind_ok] at h
  obtain ⟨m1, hs, -⟩ := h
  obtain ⟨hv, hi, hc⟩ := load_ok hle hl
  refine ⟨hv, hi, fun c hca hic => ?_, fun c1 c2 v1 v2 vs1 vs2 c1' c2' h1 h2 => ?_⟩
  · obtain ⟨r', hr'⟩ := hc c hca hic
    refine ⟨⟨ty, r'⟩, [], c.writeBits (bigOf fl) (Clif.effAddr pv 0) ty.bytes
      (Clif.Sem.atomicRmw op r' a), ?_⟩
    rw [e, ha, Clif.Res.ok_bind, hck, Clif.Res.ok_bind, hr', Clif.Res.ok_bind, store_of (load_check hr') (by rw [readonlyAt_allocs hca]; exact store_ro hs),
      Clif.Res.ok_bind]
    rfl
  · rw [e, bind_ok] at h1 h2
    obtain ⟨_, _, h1⟩ := h1
    obtain ⟨_, _, h2⟩ := h2
    rw [bind_ok] at h1 h2
    obtain ⟨_, _, h1⟩ := h1
    obtain ⟨_, _, h2⟩ := h2
    rw [bind_ok] at h1 h2
    obtain ⟨raw1, hl1, h1⟩ := h1
    obtain ⟨raw2, hl2, h2⟩ := h2
    rw [bind_ok] at h1 h2
    obtain ⟨_, _, e1⟩ := h1
    obtain ⟨_, _, e2⟩ := h2
    obtain ⟨e1, -⟩ := pure_ok e1
    obtain ⟨e2, -⟩ := pure_ok e2
    simp only [List.cons.injEq] at e1 e2
    obtain ⟨rfl, -⟩ := e1
    obtain ⟨rfl, -⟩ := e2
    refine ⟨rfl, fun hvv => ?_⟩
    simp only [Clif.Val.mk.injEq, heq_eq_eq, true_and] at hvv
    subst hvv
    exact readBits_inj (Nat.le_of_eq (width_bytes ty)) (load_eq hle hl1).2 (load_eq hle hl2).2

theorem cas_tail {b : Bool} {X : Clif.Res Clif.Mem} {c : Clif.Mem} {v v1 : Clif.Val}
    {vs1 : List Clif.Val} {c1' : Clif.Mem}
    (h : (if b = true then (X >>= fun m => (pure ([v], m) : Clif.Res (List Clif.Val × Clif.Mem)))
      else (pure c >>= fun m => (pure ([v], m) : Clif.Res (List Clif.Val × Clif.Mem)))) =
        .ok (v1 :: vs1, c1')) : v1 = v := by
  cases b
  · simp only [Bool.false_eq_true, ite_false, Clif.Res.pure_eq, Clif.Res.ok_bind,
      Clif.Res.ok.injEq, Prod.mk.injEq, List.cons.injEq] at h
    exact h.1.1.symm
  · simp only [ite_true, bind_ok] at h
    obtain ⟨m, -, h⟩ := h
    simp only [Clif.Res.pure_eq, Clif.Res.ok.injEq, Prod.mk.injEq, List.cons.injEq] at h
    exact h.1.1.symm

/-- **`atomic_cas`**: `LoadFacts` at its access (its first result is the old value), if it does
not target read-only data. -/
theorem atomicCas_facts {env : Clif.Env} {p : Clif.Program} {fr : Clif.Frame} {cm : Clif.Mem}
    {ty : Clif.Ty} {fl : Clif.MemFlags} {pp ex x : Nat}
    {vs : List Clif.Val} {cm' : Clif.Mem} (hle : bigOf fl = false)
    (h : instOutcome env p fr cm (.atomicCas ty fl pp ex x) = .ok (vs, cm')) {pv : Clif.Val}
    (hpv : fr.regs pp = some pv) (hro : cm.readonlyAt (Clif.effAddr pv 0) ty.bytes = false) :
    LoadFacts env p fr cm (.atomicCas ty fl pp ex x) (Clif.effAddr pv 0) ty.bytes := by
  have e : ∀ c, instOutcome env p fr c (.atomicCas ty fl pp ex x) = (do
      let ev ← fr.getAs ex ty
      let a ← fr.getAs x ty
      Clif.Res.check (Clif.effAddr pv 0 % ty.bytes == 0) "misaligned atomic access"
      let old ← c.load fl (Clif.effAddr pv 0) ty.bytes ty.width
      let mem' ← if old == ev then c.store fl (Clif.effAddr pv 0) ty.bytes a else pure c
      pure ([⟨ty, old⟩], mem')) := by
    intro c
    simp only [instOutcome, Clif.evalInst, Clif.Frame.get, hpv, Clif.Res.ofOption_some,
      Clif.Res.ok_bind]
  rw [e, bind_ok] at h
  obtain ⟨ev, hev, h⟩ := h
  rw [bind_ok] at h
  obtain ⟨a, ha, h⟩ := h
  rw [bind_ok] at h
  obtain ⟨u, hck, h⟩ := h
  rw [bind_ok] at h
  obtain ⟨raw, hl, -⟩ := h
  obtain ⟨hv, hi, hc⟩ := load_ok hle hl
  refine ⟨hv, hi, fun c hca hic => ?_, fun c1 c2 v1 v2 vs1 vs2 c1' c2' h1 h2 => ?_⟩
  · obtain ⟨r', hr'⟩ := hc c hca hic
    refine ⟨⟨ty, r'⟩, [], ?_⟩
    rw [e, hev, Clif.Res.ok_bind, ha, Clif.Res.ok_bind, hck, Clif.Res.ok_bind, hr',
      Clif.Res.ok_bind]
    by_cases hq : (r' == ev) = true
    · simp only [hq, ite_true, store_of (load_check hr')
        (by rw [readonlyAt_allocs hca]; exact hro), Clif.Res.ok_bind]
      exact ⟨_, rfl⟩
    · simp only [hq, Bool.false_eq_true, ite_false]
      exact ⟨c, rfl⟩
  · rw [e, bind_ok] at h1 h2
    obtain ⟨_, _, h1⟩ := h1
    obtain ⟨_, _, h2⟩ := h2
    rw [bind_ok] at h1 h2
    obtain ⟨_, _, h1⟩ := h1
    obtain ⟨_, _, h2⟩ := h2
    rw [bind_ok] at h1 h2
    obtain ⟨_, _, h1⟩ := h1
    obtain ⟨_, _, h2⟩ := h2
    rw [bind_ok] at h1 h2
    obtain ⟨raw1, hl1, h1⟩ := h1
    obtain ⟨raw2, hl2, h2⟩ := h2
    have e1 := cas_tail h1
    have e2 := cas_tail h2
    subst e1 e2
    refine ⟨rfl, fun hvv => ?_⟩
    simp only [Clif.Val.mk.injEq, heq_eq_eq, true_and] at hvv
    subst hvv
    exact readBits_inj (Nat.le_of_eq (width_bytes ty)) (load_eq hle hl1).2 (load_eq hle hl2).2

/-- `store`/`atomic_store`: the memory statements without results. -/
def isStore : Clif.Inst → Bool
  | .store .. | .atomicStore .. => true
  | _ => false

/-- `atomic_cas`. -/
def isCas : Clif.Inst → Bool
  | .atomicCas .. => true
  | _ => false

theorem access_some {fr : Clif.Frame} {pp : Nat} {f : Clif.Val → Nat × Nat} {a n : Nat}
    (h : (fr.regs pp).map f = some (a, n)) : ∃ pv, fr.regs pp = some pv ∧ f pv = (a, n) := by
  cases hr : fr.regs pp <;> simp_all

theorem access_some_ite {fr : Clif.Frame} {pp : Nat} {f : Clif.Val → Nat × Nat} {a n : Nat}
    {b : Bool} (h : (if b = true then none else (fr.regs pp).map f) = some (a, n)) :
    b = false ∧ ∃ pv, fr.regs pp = some pv ∧ f pv = (a, n) := by
  cases b
  · exact ⟨rfl, access_some h⟩
  · simp at h

/-- **Every byte of a memory statement's CLIF access lies in an event of its lowered code's run**
(layer 2d): for `load`, `store`, `atomic_load`, `atomic_store`, `atomic_rmw` and `atomic_cas`
that run successfully, no byte of the access (`access`) is outside every event of the run of the
statement's code (`RunOut`), given the per-statement contract `LowerInstOk` and the memory relation
`MemRelOk` of M4. Load-like statements have a result (`hres`); an `atomic_cas` does not target
read-only data (`hro`: its store would be stuck where the comparison succeeds). -/
theorem access_in_events {isem : Sem} {MR : MemRelT} {env : Clif.Env} {p : Clif.Program}
    {ctx : Ctx} {inst : Clif.Inst} {results : List Nat} {st : LState} {rss : List (List Reg)}
    {st' : LState} {ms : List MInst} {F : BitVec 64 → Prop} {sb : Nat}
    {syms : String → Option Nat} {f : Clif.Function}
    (hok : LowerInstOk isem MR env p ctx inst results st rss st' ms)
    (hMR : MemRelOk F sb syms f MR) (hres : isStore inst = false → results ≠ [])
    {fr : Clif.Frame} {cm : Clif.Mem} {ρ : Nat → CV} {w : Arm.ArmState}
    (hf : fr.func = ctx.func) (hv : ValsHeld fr ρ) (hd : DFGCons ctx fr) (hmr : MR fr.slots cm w)
    {vs : List Clif.Val} {cm' : Clif.Mem} (h : instOutcome env p fr cm inst = .ok (vs, cm'))
    {a n : Nat} (hacc : access fr inst = some (a, n))
    (hro : isCas inst = true → cm.readonlyAt a n = false)
    {k : Nat} (hk : k < n) : ¬ RunOut isem (BitVec.ofNat 64 (a + k)) ms ρ w := by
  have load_case : LoadFacts env p fr cm inst a n → results ≠ [] →
      ¬ RunOut isem (BitVec.ofNat 64 (a + k)) ms ρ w := fun ⟨hval, hinit, hout, hinj⟩ hr =>
    load_in_events hok hMR hr hf hv hd hmr hval hout hinj hinit hk
  have store_case : StoreFacts env p fr cm inst a n →
      ¬ RunOut isem (BitVec.ofNat 64 (a + k)) ms ρ w := fun ⟨hval, _, _, _, hout⟩ =>
    store_in_events hok hMR hf hv hd hmr hval hout hk
  cases inst <;> simp only [access, reduceCtorEq] at hacc
  case load op ty fl pp off =>
    obtain ⟨hle, pv, hpv, he⟩ := access_some_ite hacc
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact load_case (load_facts hle h hpv) (hres rfl)
  case store op ty fl x pp off =>
    obtain ⟨pv, hpv, he⟩ := access_some hacc
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact store_case (store_facts h hpv)
  case atomicRmw op ty fl pp x =>
    obtain ⟨hle, pv, hpv, he⟩ := access_some_ite hacc
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact load_case (atomicRmw_facts hle h hpv) (hres rfl)
  case atomicCas ty fl pp ex x =>
    obtain ⟨hle, pv, hpv, he⟩ := access_some_ite hacc
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact load_case (atomicCas_facts hle h hpv (hro rfl)) (hres rfl)
  case atomicLoad ty fl pp =>
    obtain ⟨hle, pv, hpv, he⟩ := access_some_ite hacc
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact load_case (atomicLoad_facts hle h hpv) (hres rfl)
  case atomicStore ty fl x pp =>
    obtain ⟨pv, hpv, he⟩ := access_some hacc
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact store_case (atomicStore_facts h hpv)

end Concurrency.IselClif
