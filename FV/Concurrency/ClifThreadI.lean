module

public import FV.Concurrency.ClifThread

@[expose] public section

/-!
# CLIF threads with stack slots: the own-initialisation mask (#473, (iv))

`ClifThread.CStep` cannot enter a callee with stack slots placed at their compiled frame
addresses: `Clif.enterFunc` allocates them with `Mem.allocAt`, which sets their bytes to `none`,
but an event-free `CStep` must leave every byte memory unchanged. And with stack reuse, an
uninitialised read of a slot could read a stale byte of an earlier activation. **`CStepI`** is
`CStep` for thread states carrying a ghost **mask** `U` (`TStateI`): the bytes of the thread's
stack slots that the thread has not written since their allocation. A step runs `Clif.step` on
the shared bytes with the masked bytes `none` (`mix U B`): a read of a masked byte is stuck, as in
`Clif.run` ("read of uninitialised memory"); the step's resulting bytes are the shared bytes with
the step's write events applied, masked by the new mask, which may only keep old masked bytes the
step did not write or add stack-slot bytes of the new state (`slotByte`), e.g. the slots the
step's `enterFunc` placed.

* `cstepI_empty`: with the empty mask before and after, `CStepI` is `CStep` (the old semantics is
  the special case without slot allocation);
* `cstepI_of_cstep`: every `CStep` whose reads avoid the mask is a `CStepI` (the mask loses the
  written bytes) — e.g. every memory statement, every return;
* `enterSlots_bytes`, `enterFunc_bytes`: `Clif.enterFunc` on a byte memory `B` is its outcome on
  any other memory with the placed slots' bytes (`slotZ`) set to `none` in `B`;
  **`cstepI_call`**: the call of a program function is a `CStepI` that adds the placed slot
  bytes to the mask;
* **`cstepI_own`** (the single-thread correspondence): from a state whose masked bytes are
  `none` in its own memory (`MaskOk`), a `CStepI` whose read events read that memory is the
  `Clif.step` of the state, to a state whose new masked bytes are `none` again — so the mask
  makes a read stuck exactly where `Clif.run` is stuck on an uninitialised byte, and the slots
  `enterFunc`/`placeSlots` allocate are the masked ones (`cstepI_own_stuck`).
-/

namespace Concurrency.ClifThreadI

open Prog ClifThread

/-- A CLIF thread state with its own-initialisation mask. -/
abbrev TStateI := TState × (Nat → Prop)

/-- The bytes of the stack slots of a frame. -/
def frameSlot (fr : Clif.Frame) (a : Nat) : Prop :=
  ∃ x ∈ fr.func.slots, ∃ base, (x.1, base) ∈ fr.slots ∧ base ≤ a ∧ a < base + x.2.size

/-- The bytes of the stack slots of the running and suspended frames. -/
def slotByte : TState → Nat → Prop
  | .run s, a => frameSlot s.frame a ∨ ∃ c ∈ s.callers, frameSlot c.1 a
  | .ret _, _ => False

open Classical in
/-- The bytes `B` with the masked bytes `none`. -/
noncomputable def mix (U : Nat → Prop) (B : Bytes) : Bytes := fun a => if U a then none else B a

/-- The bytes the write events of a step write. -/
def writes (evs : List (Ev SKind BVal)) (a : Nat) : Prop :=
  ∃ e ∈ evs, e.dir = .W ∧ e.loc ≤ a ∧ a < e.loc + e.n

/-- **One step of a CLIF thread with its events and its mask** (module doc). -/
def CStepI (env : Clif.Env) (p : Clif.Program) : TSem TStateI SKind BVal := fun x evs y =>
  match x.1 with
  | .ret _ => False
  | .run s => KindsOk s evs ∧ (∃ B, Agrees bytesI B evs) ∧
      (∀ a, y.2 a → (x.2 a ∧ ¬ writes evs a) ∨ slotByte y.1 a) ∧
      ∀ B, Agrees bytesI B evs → ∃ t'', res (Clif.step env p (withBytes s (mix x.2 B))) =
        some (t'', mix y.2 (applyEvs bytesI B evs)) ∧ strip t'' = strip y.1

/-- **Runs of `CStepI`.** -/
inductive CRunI (env : Clif.Env) (p : Clif.Program) :
    TStateI → List (List (Ev SKind BVal)) → TStateI → Prop
  | nil {t} : CRunI env p t [] t
  | cons {t t' t'' e tr} : CStepI env p t e t' → CRunI env p t' tr t'' → CRunI env p t (e :: tr) t''

theorem CRunI.append {env : Clif.Env} {p : Clif.Program} :
    ∀ {t t' t'' : TStateI} {a b : List (List (Ev SKind BVal))},
      CRunI env p t a t' → CRunI env p t' b t'' → CRunI env p t (a ++ b) t''
  | _, _, _, [], _, .nil, h => h
  | _, _, _, _ :: _, _, .cons h1 r, h => .cons h1 (r.append h)

/-- The masked bytes are `none` in the thread's own memory. -/
def MaskOk (U : Nat → Prop) : TState → Prop
  | .run s => ∀ a, U a → s.mem.bytes a = none
  | .ret _ => True

/-! ## The mask on byte memories -/

theorem mix_false (B : Bytes) : mix (fun _ => False) B = B := by
  funext a; simp [mix]

theorem mix_own {U : Nat → Prop} {B : Bytes} (h : ∀ a, U a → B a = none) : mix U B = B := by
  funext a; unfold mix; split
  · rename_i hu; exact (h a hu).symm
  · rfl

theorem withBytes_self (s : Clif.State) : withBytes s s.mem.bytes = s := rfl

theorem getB_mix {U : Nat → Prop} {B : Bytes} {l n : Nat} (h : ∀ k < n, ¬ U (l + k)) :
    getB (mix U B) l n = getB B l n := by
  unfold getB
  apply List.map_congr_left
  intro k hk
  simp only [List.mem_range] at hk
  simp [mix, h k hk]

theorem putB_mix (U : Nat → Prop) (B : Bytes) (l n : Nat) (v : BVal) :
    putB (mix U B) l n v = mix (fun a => U a ∧ ¬ (l ≤ a ∧ a < l + n)) (putB B l n v) := by
  funext a
  unfold putB mix
  by_cases hr : l ≤ a ∧ a < l + n
  · simp [hr]
  · by_cases hu : U a <;> simp [hu, hr]

theorem write1_mix (U : Nat → Prop) (B : Bytes) (e : Ev SKind BVal) :
    write1 bytesI (mix U B) e =
      mix (fun a => U a ∧ ¬ (e.dir = .W ∧ e.loc ≤ a ∧ a < e.loc + e.n)) (write1 bytesI B e) := by
  unfold write1
  by_cases hw : e.dir = .W
  · simp only [hw, ite_true, true_and]
    exact putB_mix U B e.loc e.n e.val
  · simp only [hw, ite_false, false_and, not_false_eq_true, and_true]

/-- The step's writes on the masked bytes: the mask loses the written bytes. -/
theorem applyEvs_mix : ∀ (U : Nat → Prop) (B : Bytes) (evs : List (Ev SKind BVal)),
    applyEvs bytesI (mix U B) evs = mix (fun a => U a ∧ ¬ writes evs a) (applyEvs bytesI B evs)
  | U, B, [] => by
    simp only [applyEvs, List.foldl_nil]
    congr; funext a; simp [writes]
  | U, B, e :: es => by
    show List.foldl (write1 bytesI) (write1 bytesI (mix U B) e) es =
      mix _ (List.foldl (write1 bytesI) (write1 bytesI B e) es)
    rw [write1_mix]
    have ih := applyEvs_mix (fun a => U a ∧ ¬ (e.dir = .W ∧ e.loc ≤ a ∧ a < e.loc + e.n))
      (write1 bytesI B e) es
    simp only [applyEvs] at ih
    rw [ih]
    congr 1; funext a
    apply propext
    constructor
    · rintro ⟨⟨hu, h1⟩, h2⟩
      refine ⟨hu, fun ⟨e', he', hw⟩ => ?_⟩
      rcases List.mem_cons.mp he' with rfl | he'
      · exact h1 hw
      · exact h2 ⟨e', he', hw⟩
    · rintro ⟨hu, h⟩
      exact ⟨⟨hu, fun hw => h ⟨e, List.mem_cons_self .., hw⟩⟩,
        fun ⟨e', he', hw⟩ => h ⟨e', List.mem_cons_of_mem _ he', hw⟩⟩

/-- Read events avoiding the mask read the same bytes from the masked memory. -/
theorem agrees_mix : ∀ (U : Nat → Prop) (B : Bytes) (evs : List (Ev SKind BVal)),
    Agrees bytesI B evs → (∀ e ∈ evs, e.dir = .R → ∀ k < e.n, ¬ U (e.loc + k)) →
    Agrees bytesI (mix U B) evs
  | _, _, [], _, _ => trivial
  | U, B, e :: es, ⟨h1, h2⟩, hr => by
    refine ⟨fun hd => ?_, ?_⟩
    · rw [h1 hd]
      exact (getB_mix (hr e (List.mem_cons_self ..) hd)).symm
    · rw [write1_mix]
      exact agrees_mix _ _ es h2 fun e' he' hd k hk hu =>
        hr e' (List.mem_cons_of_mem _ he') hd k hk hu.1

/-! ## The old semantics as the special case -/

/-- **With the empty mask before and after, `CStepI` is `CStep`.** -/
theorem cstepI_empty {env : Clif.Env} {p : Clif.Program} {t t' : TState}
    {evs : List (Ev SKind BVal)} :
    CStepI env p (t, fun _ => False) evs (t', fun _ => False) ↔ CStep env p t evs t' := by
  cases t with
  | ret v => exact ⟨fun h => h.elim, fun h => h.elim⟩
  | run s =>
    simp only [CStepI, CStep, mix_false]
    constructor
    · rintro ⟨hk, hB, -, hf⟩; exact ⟨hk, hB, hf⟩
    · rintro ⟨hk, hB, hf⟩; exact ⟨hk, hB, fun _ h => h.elim, hf⟩

/-- **Every `CStep` whose reads avoid the mask is a `CStepI`**, the mask losing the written
bytes. -/
theorem cstepI_of_cstep {env : Clif.Env} {p : Clif.Program} {s : Clif.State} {t' : TState}
    {evs : List (Ev SKind BVal)} (h : CStep env p (.run s) evs t') {U : Nat → Prop}
    (hr : ∀ e ∈ evs, e.dir = .R → ∀ k < e.n, ¬ U (e.loc + k)) :
    CStepI env p (.run s, U) evs (t', fun a => U a ∧ ¬ writes evs a) := by
  obtain ⟨hk, hB, hf⟩ := h
  refine ⟨hk, hB, fun a ha => .inl ha, fun B hB' => ?_⟩
  obtain ⟨t'', hres, hst⟩ := hf (mix U B) (agrees_mix U B evs hB' hr)
  exact ⟨t'', by rw [hres, applyEvs_mix], hst⟩

/-! ## The call of a program function -/

/-- The bytes of the slots `enterSlots` places with `Mem.allocAt` (none from the bump
allocator). -/
def slotZ (f : Clif.Function) (m : Clif.Mem) : Nat → Prop :=
  match m.place with
  | none => fun _ => False
  | some pl =>
    match pl.frame f.name with
    | some (d, off) => fun a => ∃ x ∈ f.slots,
        (pl.sps.headD 0 - BitVec.ofNat 64 d).toNat + off x.1 ≤ a ∧
          a < (pl.sps.headD 0 - BitVec.ofNat 64 d).toNat + off x.1 + x.2.size
    | none => fun _ => False


/-- The memory `m` with the bytes `B`. -/
def setB (m : Clif.Mem) (B : Bytes) : Clif.Mem := { m with bytes := B }

@[simp] theorem setB_place (m : Clif.Mem) (B : Bytes) : (setB m B).place = m.place := rfl
@[simp] theorem setB_allocs (m : Clif.Mem) (B : Bytes) : (setB m B).allocs = m.allocs := rfl
@[simp] theorem setB_next (m : Clif.Mem) (B : Bytes) : (setB m B).next = m.next := rfl
@[simp] theorem setB_symbols (m : Clif.Mem) (B : Bytes) : (setB m B).symbols = m.symbols := rfl
@[simp] theorem setB_bytes (m : Clif.Mem) (B : Bytes) : (setB m B).bytes = B := rfl

theorem mix_or (U V : Nat → Prop) (B : Bytes) : mix U (mix V B) = mix (fun a => U a ∨ V a) B := by
  funext a; unfold mix; by_cases hu : U a <;> by_cases hv : V a <;> simp [hu, hv]

/-- A fold of slot allocations on a byte memory `B`, each clearing the bytes `Zx x`. -/
theorem foldl_bytes {X : Type}
    (g : List (Clif.SlotId × Nat) × Clif.Mem → X → List (Clif.SlotId × Nat) × Clif.Mem)
    (Zx : X → Nat → Prop)
    (hg : ∀ L m B x, g (L, setB m B) x = ((g (L, m) x).1, setB (g (L, m) x).2 (mix (Zx x) B))) :
    ∀ (xs : List X) L m B, xs.foldl g (L, setB m B) =
      ((xs.foldl g (L, m)).1, setB (xs.foldl g (L, m)).2 (mix (fun a => ∃ x ∈ xs, Zx x a) B))
  | [], L, m, B => by
    have e : mix (fun a => ∃ x ∈ ([] : List X), Zx x a) B = B := by funext a; simp [mix]
    simp only [List.foldl_nil, e]
  | x :: xs, L, m, B => by
    simp only [List.foldl_cons]
    rw [hg]
    generalize g (L, m) x = q
    obtain ⟨L', m'⟩ := q
    rw [foldl_bytes g Zx hg xs L' m', mix_or]
    congr 3
    funext a
    apply propext
    simp only [List.mem_cons, exists_eq_or_imp]
    exact ⟨fun h => h.elim .inr .inl, fun h => h.elim .inr .inl⟩

theorem mix_none (B : Bytes) {X : Type} (xs : List X) :
    mix (fun a => ∃ x ∈ xs, (fun (_ : X) (_ : Nat) => False) x a) B = B := by
  funext a; simp [mix]

theorem bumpSlots_bytes (sl : List (Clif.SlotId × Clif.StackSlot)) (m : Clif.Mem) (B : Bytes) :
    Clif.bumpSlots sl (setB m B) = ((Clif.bumpSlots sl m).1, setB (Clif.bumpSlots sl m).2 B) := by
  unfold Clif.bumpSlots
  refine (foldl_bytes _ (fun _ _ => False) ?_ sl [] m B).trans ?_
  · intro L m B x
    rw [mix_false]
    rfl
  · rw [mix_none]

theorem placeSlots_bytes (sl : List (Clif.SlotId × Clif.StackSlot)) (sp : BitVec 64)
    (off : Clif.SlotId → Nat) (m : Clif.Mem) (B : Bytes) :
    Clif.placeSlots sl sp off (setB m B) = ((Clif.placeSlots sl sp off m).1,
      setB (Clif.placeSlots sl sp off m).2 (mix (fun a => ∃ x ∈ sl, sp.toNat + off x.1 ≤ a ∧
        a < sp.toNat + off x.1 + x.2.size) B)) := by
  unfold Clif.placeSlots
  refine foldl_bytes _ (fun x a => sp.toNat + off x.1 ≤ a ∧ a < sp.toNat + off x.1 + x.2.size)
    ?_ sl [] m B
  intro L m B x
  simp only [setB, Clif.Mem.allocAt, Prod.mk.injEq, true_and]
  congr 1; funext a; unfold mix
  by_cases h : sp.toNat + off x.1 ≤ a ∧ a < sp.toNat + off x.1 + x.2.size <;> simp [h]

/-- **`enterSlots` on a byte memory `B`** is its outcome with the placed slots' bytes cleared
(without the slot-byte oracle `Clif.Place.init`). -/
theorem enterSlots_bytes (f : Clif.Function) (m : Clif.Mem) (B : Bytes)
    (hi : ∀ pl, m.place = some pl → pl.init = none) :
    Clif.enterSlots f (setB m B) =
      ((Clif.enterSlots f m).1, setB (Clif.enterSlots f m).2 (mix (slotZ f m) B)) := by
  obtain ⟨al, by0, nx, sy, pl⟩ := m
  cases pl with
  | none =>
    have e : mix (slotZ f ⟨al, by0, nx, sy, none⟩) B = B := by funext a; simp [mix, slotZ]
    rw [e]
    exact bumpSlots_bytes f.slots ⟨al, by0, nx, sy, none⟩ B
  | some pl =>
    cases hf : pl.frame f.name with
    | none =>
      have e : mix (slotZ f ⟨al, by0, nx, sy, some pl⟩) B = B := by
        funext a; simp [mix, slotZ, hf]
      rw [e]
      have := bumpSlots_bytes f.slots
        ⟨al, by0, nx, sy, some { pl with sps := pl.sps.headD 0 :: pl.sps }⟩ B
      simp only [Clif.enterSlots, hf, setB_place, setB_allocs, setB_bytes, setB_next, setB_symbols]
      exact this
    | some dp =>
      obtain ⟨d, off⟩ := dp
      have e : slotZ f ⟨al, by0, nx, sy, some pl⟩ = fun a => ∃ x ∈ f.slots,
          (pl.sps.headD 0 - BitVec.ofNat 64 d).toNat + off x.1 ≤ a ∧
            a < (pl.sps.headD 0 - BitVec.ofNat 64 d).toNat + off x.1 + x.2.size := by
        simp only [slotZ, hf]
      rw [e]
      have := placeSlots_bytes f.slots (pl.sps.headD 0 - BitVec.ofNat 64 d) off
        ⟨al, by0, nx, sy, some { pl with sps := (pl.sps.headD 0 - BitVec.ofNat 64 d) :: pl.sps }⟩ B
      have hi0 : pl.init = none := hi pl rfl
      simp only [Clif.enterSlots, hf, hi0, Clif.initSlots_none, setB_place, setB_allocs, setB_bytes,
        setB_next, setB_symbols]
      rw [hi0] at this
      exact this

theorem placeSlots_fst (sp : BitVec 64) (off : Clif.SlotId → Nat) (m : Clif.Mem)
    (sl : List (Clif.SlotId × Clif.StackSlot)) :
    (Clif.placeSlots sl sp off m).1 = sl.map fun x => (x.1, sp.toNat + off x.1) := by
  unfold Clif.placeSlots
  suffices h : ∀ (acc : List (Clif.SlotId × Nat)) (m : Clif.Mem),
      (sl.foldl (fun (acc : List (Clif.SlotId × Nat) × Clif.Mem) s =>
        (acc.1 ++ [(s.1, sp.toNat + off s.1)], acc.2.allocAt (sp.toNat + off s.1) s.2.size))
        (acc, m)).1 = acc ++ sl.map fun x => (x.1, sp.toNat + off x.1) by
    simpa using h [] m
  induction sl with
  | nil => intro acc m; simp
  | cons x sl ih =>
    intro acc m
    simp only [List.foldl_cons]
    rw [ih]
    simp

/-- The placed slots' bytes are bytes of the new frame's slots. -/
theorem slotZ_frameSlot {f : Clif.Function} {m : Clif.Mem} {a : Nat} (hz : slotZ f m a) :
    ∃ x ∈ f.slots, ∃ base, (x.1, base) ∈ (Clif.enterSlots f m).1 ∧ base ≤ a ∧
      a < base + x.2.size := by
  obtain ⟨al, by0, nx, sy, pl⟩ := m
  cases pl with
  | none => exact hz.elim
  | some pl =>
    cases hf : pl.frame f.name with
    | none => simp [slotZ, hf] at hz
    | some dp =>
      obtain ⟨d, off⟩ := dp
      simp only [slotZ, hf] at hz
      obtain ⟨x, hx, h1, h2⟩ := hz
      refine ⟨x, hx, _, ?_, h1, h2⟩
      simp only [Clif.enterSlots, hf]
      rw [Clif.initSlots_fst, placeSlots_fst]
      exact List.mem_map.mpr ⟨x, hx, rfl⟩

theorem Res.bind_eq_ok {α β : Type} {x : Clif.Res α} {k : α → Clif.Res β} {v : β}
    (h : (x >>= k) = .ok v) : ∃ a, x = .ok a ∧ k a = .ok v := by
  cases x with
  | ok a => exact ⟨a, rfl, h⟩
  | trap c => cases h
  | stuck m => cases h

/-- **`enterFunc` on a byte memory `B`** is its outcome with the placed slots' bytes cleared
(without the slot-byte oracle `Clif.Place.init`). -/
theorem enterFunc_bytes {f : Clif.Function} {args : List Clif.Val} {m m' : Clif.Mem}
    {fr : Clif.Frame} (h : Clif.enterFunc f args m = .ok (fr, m')) (B : Bytes)
    (hi : ∀ pl, m.place = some pl → pl.init = none) :
    Clif.enterFunc f args (setB m B) = .ok (fr, setB m' (mix (slotZ f m) B)) ∧
      fr.func = f ∧ fr.slots = (Clif.enterSlots f m).1 := by
  unfold Clif.enterFunc at h ⊢
  obtain ⟨u1, h1, h⟩ := Res.bind_eq_ok h
  rw [h1, Clif.Res.ok_bind]
  obtain ⟨entry, h2, h⟩ := Res.bind_eq_ok h
  rw [h2, Clif.Res.ok_bind]
  rw [enterSlots_bytes f m B hi]
  generalize hes : Clif.enterSlots f m = es at h ⊢
  obtain ⟨sl, m2⟩ := es
  simp only at h ⊢
  obtain ⟨u3, h3, h⟩ := Res.bind_eq_ok h
  rw [h3, Clif.Res.ok_bind]
  obtain ⟨regs, h4, h⟩ := Res.bind_eq_ok h
  rw [h4, Clif.Res.ok_bind]
  simp only [Clif.Res.pure_eq, Clif.Res.ok.injEq, Prod.mk.injEq] at h ⊢
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨⟨rfl, rfl⟩, rfl, rfl⟩

/-- **The call of a program function is a `CStepI`** that adds the slots `enterFunc` placed to
the mask (without the slot-byte oracle `Clif.Place.init`). -/
theorem cstepI_call {env : Clif.Env} {p : Clif.Program} {s s' : Clif.State}
    {results : List Clif.ValueId} {fn : Clif.FnRef} {args : List Clif.ValueId}
    {rest : List Clif.Stmt} (hb : s.frame.body = { results, inst := .call fn args } :: rest)
    {ext : Clif.ExtFunc} {callee : Clif.Function} (he : s.frame.func.extern? fn = some ext)
    (hc : p.func? ext.name = some callee) (hs : Clif.step env p s = .next s') (U : Nat → Prop)
    (hi : ∀ pl, s.mem.place = some pl → pl.init = none) :
    CStepI env p (.run s, U) [] (.run s', fun a => U a ∨ slotZ callee s.mem a) := by
  have key : ∀ B, Clif.step env p (withBytes s B) =
      .next (withBytes s' (mix (slotZ callee s.mem) B)) ∧ s'.frame.func = callee ∧
        s'.frame.slots = (Clif.enterSlots callee s.mem).1 := by
    intro B
    have hbB : (withBytes s B).frame.body = { results, inst := .call fn args } :: rest := hb
    rw [Clif.step_call _ _ _ _ _ _ _ hbB]
    rw [Clif.step_call _ _ _ _ _ _ _ hb] at hs
    unfold Clif.stepCall at hs ⊢
    dsimp only [withBytes] at hs ⊢
    simp only [Clif.StepResult.ofRes] at hs ⊢
    split at hs
    · rename_i a heq
      obtain ⟨e0, h0, heq⟩ := Res.bind_eq_ok heq
      rw [he] at h0
      cases h0
      obtain ⟨vals, -, heq⟩ := Res.bind_eq_ok heq
      obtain ⟨u, -, heq⟩ := Res.bind_eq_ok heq
      cases heq
      rw [hc] at hs ⊢
      dsimp only at hs ⊢
      split at hs
      · rename_i hsig
        rw [if_pos hsig]
        split at hs
        · rename_i r hef
          obtain ⟨fr', mem'⟩ := r
          obtain ⟨hB, hf1, hf2⟩ := enterFunc_bytes hef B hi
          simp only [setB] at hB
          rw [hB]
          cases hs
          exact ⟨rfl, hf1, hf2⟩
        · cases hs
        · cases hs
      · cases hs
    · cases hs
    · cases hs
  obtain ⟨-, hf1, hf2⟩ := key (fun _ => none)
  refine ⟨⟨?_, fun e he => by cases he⟩, ⟨fun _ => none, trivial⟩, fun a ha => ?_, fun B _ => ?_⟩
  · unfold evShape; rw [hb]; simp
  · rcases ha with hu | hz
    · exact .inl ⟨hu, fun ⟨e, he, _⟩ => by cases he⟩
    · obtain ⟨x, hx, base, hm, h1, h2⟩ := slotZ_frameSlot hz
      refine .inr (.inl ⟨x, by rw [hf1]; exact hx, base, by rw [hf2]; exact hm, h1, h2⟩)
  · refine ⟨.run (withBytes s' (mix (slotZ callee s.mem) (mix U B))), ?_, rfl⟩
    rw [(key (mix U B)).1, mix_or]
    show some _ = some (_, mix _ B)
    have e : (fun a => slotZ callee s.mem a ∨ U a) = fun a => U a ∨ slotZ callee s.mem a := by
      funext a; exact propext Or.comm
    simp only [res, withBytes, e]

/-! ## The single-thread correspondence -/

/-- **A `CStepI` whose read events read the thread's own memory is the `Clif.step` of the
state** (module doc), when the masked bytes are `none` there; the new masked bytes are `none`
in the memory after it. -/
theorem cstepI_own {env : Clif.Env} {p : Clif.Program} {s : Clif.State} {U U' : Nat → Prop}
    {t' : TState} {evs : List (Ev SKind BVal)} (h : CStepI env p (.run s, U) evs (t', U'))
    (hU : MaskOk U (.run s)) (hA : Agrees bytesI s.mem.bytes evs) :
    ∃ t'', res (Clif.step env p s) = some (t'', mix U' (applyEvs bytesI s.mem.bytes evs)) ∧
      strip t'' = strip t' ∧ MaskOk U' t'' := by
  obtain ⟨-, -, -, hf⟩ := h
  obtain ⟨t'', hr, hst⟩ := hf s.mem.bytes hA
  rw [mix_own hU, withBytes_self] at hr
  refine ⟨t'', hr, hst, ?_⟩
  cases hs : Clif.step env p s with
  | next s2 =>
    rw [hs] at hr
    simp only [res, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, hb⟩ := hr
    intro a ha
    rw [hb]; simp [mix, ha]
  | done vals m =>
    rw [hs] at hr
    simp only [res, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    trivial
  | trapped c => rw [hs] at hr; cases hr
  | stuck m => rw [hs] at hr; cases hr

/-- **Where `Clif.run` is stuck or traps, `CStepI` has no step** reading the thread's own
memory (e.g. a load of a masked, uninitialised slot byte). -/
theorem cstepI_own_stuck {env : Clif.Env} {p : Clif.Program} {s : Clif.State} {U : Nat → Prop}
    (hU : MaskOk U (.run s)) (hs : res (Clif.step env p s) = none) {evs : List (Ev SKind BVal)}
    (hA : Agrees bytesI s.mem.bytes evs) (y : TStateI) : ¬ CStepI env p (.run s, U) evs y := by
  intro h
  obtain ⟨t'', hr, -⟩ := cstepI_own (U' := y.2) (t' := y.1) h hU hA
  rw [hs] at hr; cases hr

end Concurrency.ClifThreadI
